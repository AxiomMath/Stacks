module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.SchemeQC.ZariskiChartFunctor
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.RepresentableQC.ChartCovers

/-!
# Restriction from `(Aff/S)_{Zar}` to the affine opens of `S` on the subcategories of 0GZS

Let `S` be a scheme in a big fppf site `B`. Write `X↑` for the lift of the Zariski affine site
`(Aff/S)_{Zar}` of the big fppf category of `S`
(`AlgebraicGeometry.Stack.zariskiAffineLiftedSite` for the identity of `(Sch/S)_{fppf}`) and `Y↑`
for the lift of the small affine Zariski site of `S`
(`AlgebraicGeometry.ZariskiCharts.zariskiChartLiftedSite`), both in the universe `max (u + 1) t`.
The inclusion of the affine opens of `S` into `(Aff/S)` gives a morphism of ringed sites
`f : X↑ ⟶ Y↑` (`AlgebraicGeometry.ZariskiCharts.liftedAffineOpensHom`), whose functor is fully
faithful and cocontinuous and whose structure map is invertible.

Every object `x` of `X↑` has a finite Zariski covering by objects mapping to affine opens of `S`
(`AlgebraicGeometry.ZariskiCharts.exists_finite_covering_liftedAffineOpensHom`), and the
cartesian condition descends along it (Stacks 0H0J for the Zariski topology,
`AlgebraicGeometry.Stack.isIso_comparison_of_zariskiEtaleCover`); together with the invertibility
of the `ε`-units on the slices of `X↑`, this makes `f_*` and `Lf^*` mutually inverse equivalences
between the subcategories of Stacks 0GZS
(`AlgebraicGeometry.ZariskiCharts.liftedAffineOpensCartesianEquivalence`): the argument of Stacks
09J1, as in the proof of Stacks 0H0K.

## References

* [Stacks Project, Tag 0H0K](https://stacks.math.columbia.edu/tag/0H0K)
* [Stacks Project, Tag 0H0J](https://stacks.math.columbia.edu/tag/0H0J)
* [Stacks Project, Tag 0GZS](https://stacks.math.columbia.edu/tag/0GZS)
* [Stacks Project, Tag 09J1](https://stacks.math.columbia.edu/tag/09J1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SubsiteQuasiCoherentEquivalence

universe u t t'

namespace AlgebraicGeometry.ZariskiCharts

open AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (p : BigFppfOver B S hS ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (hp1 : p = 𝟭 (BigFppfOver B S hS))

/-- The comparison of `(Aff/S)` with its small model is a dense subsite inclusion for the Zariski
topologies. -/
instance asSmallUp_isDenseSubsite_zariskiAffineLiftedSite :
    (AsSmall.equiv : AffineCategory B S hS p ≌
      (zariskiAffineLiftedSite.{u, u + 1, u, t} B S hS p hp).C).functor.IsDenseSubsite
      (associatedAffineTopology B S hS p
        (BigAffineZariski.topology B.toBigZariskiSite S hS))
      (zariskiAffineLiftedSite.{u, u + 1, u, t} B S hS p hp).J :=
  RingedSite.transport_functor_isDenseSubsite.{max (u + 1) u t}
    (AffineCategory.siteKindRingedSite B S hS p hp .zariski) AsSmall.equiv

/-- The comparison of the small model of `(Aff/S)` with `(Aff/S)` is a dense subsite inclusion
for the Zariski topologies. -/
instance asSmallDown_isDenseSubsite_zariskiAffineLiftedSite :
    (AsSmall.equiv : AffineCategory B S hS p ≌
      (zariskiAffineLiftedSite.{u, u + 1, u, t} B S hS p hp).C).inverse.IsDenseSubsite
      (zariskiAffineLiftedSite.{u, u + 1, u, t} B S hS p hp).J
      (associatedAffineTopology B S hS p
        (BigAffineZariski.topology B.toBigZariskiSite S hS)) :=
  RingedSite.transport_inverse_isDenseSubsite.{max (u + 1) u t}
    (AffineCategory.siteKindRingedSite B S hS p hp .zariski) AsSmall.equiv

/-- **The functor underlying the morphism of lifted ringed sites**: the inclusion of the affine
opens of `S` into `(Aff/S)`, read on the lifted sites. -/
noncomputable def liftedAffineOpensInclusion :
    (zariskiChartLiftedSite.{u, t} B S hS).C ⥤
      (zariskiAffineLiftedSite.{u, u + 1, u, t} B S hS p hp).C :=
  haveI := essentiallySmall_lift.{max (u + 1) t, u}
    (SmallAffineZariski B.toBigZariskiSite S (zariskiContains B S hS))
  (equivSmallModel.{max (u + 1) t}
      (SmallAffineZariski B.toBigZariskiSite S (zariskiContains B S hS))).inverse ⋙
    affineOpensInclusion B S hS p hp1 ⋙ AsSmall.equiv.functor

/-- The inclusion of the affine opens of `S` into the lifted `(Aff/S)` is full. -/
instance liftedAffineOpensInclusion_full : (liftedAffineOpensInclusion B S hS p hp hp1).Full := by
  unfold liftedAffineOpensInclusion
  infer_instance

/-- The inclusion of the affine opens of `S` into the lifted `(Aff/S)` is faithful. -/
instance liftedAffineOpensInclusion_faithful :
    (liftedAffineOpensInclusion B S hS p hp hp1).Faithful := by
  unfold liftedAffineOpensInclusion
  infer_instance

/-- The inclusion of the affine opens of `S` into the lifted `(Aff/S)` is continuous for the
Zariski topologies. -/
instance liftedAffineOpensInclusion_isContinuous :
    (liftedAffineOpensInclusion B S hS p hp hp1).IsContinuous
      (zariskiChartLiftedSite.{u, t} B S hS).J
      (zariskiAffineLiftedSite.{u, u + 1, u, t} B S hS p hp).J := by
  have := essentiallySmall_lift.{max (u + 1) t, u}
    (SmallAffineZariski B.toBigZariskiSite S (zariskiContains B S hS))
  have := affineOpensInclusion_isContinuous B S hS p hp hp1
  have : (affineOpensInclusion B S hS p hp1 ⋙ AsSmall.equiv.functor).IsContinuous
      (SmallAffineZariski.topology B.toBigZariskiSite S (zariskiContains B S hS))
      (zariskiAffineLiftedSite.{u, u + 1, u, t} B S hS p hp).J :=
    Functor.isContinuous_comp _ _ _
      (associatedAffineTopology B S hS p
        (BigAffineZariski.topology B.toBigZariskiSite S hS)) _
  unfold liftedAffineOpensInclusion
  exact Functor.isContinuous_comp _ _ _
    (SmallAffineZariski.topology B.toBigZariskiSite S (zariskiContains B S hS)) _

/-- The inclusion of the affine opens of `S` into the lifted `(Aff/S)` is cocontinuous for the
Zariski topologies. -/
instance liftedAffineOpensInclusion_isCocontinuous :
    (liftedAffineOpensInclusion B S hS p hp hp1).IsCocontinuous
      (zariskiChartLiftedSite.{u, t} B S hS).J
      (zariskiAffineLiftedSite.{u, u + 1, u, t} B S hS p hp).J := by
  have := essentiallySmall_lift.{max (u + 1) t, u}
    (SmallAffineZariski B.toBigZariskiSite S (zariskiContains B S hS))
  have := affineOpensInclusion_isCocontinuous B S hS p hp hp1
  have : (affineOpensInclusion B S hS p hp1 ⋙ AsSmall.equiv.functor).IsCocontinuous
      (SmallAffineZariski.topology B.toBigZariskiSite S (zariskiContains B S hS))
      (zariskiAffineLiftedSite.{u, u + 1, u, t} B S hS p hp).J :=
    isCocontinuous_comp _ _ _
      (associatedAffineTopology B S hS p
        (BigAffineZariski.topology B.toBigZariskiSite S hS))
  unfold liftedAffineOpensInclusion
  exact isCocontinuous_comp _ _ _
    (SmallAffineZariski.topology B.toBigZariskiSite S (zariskiContains B S hS))

/-- The functor of the lifted sites defines a morphism of sites. -/
theorem liftedAffineOpensInclusion_isMorphismOfSites :
    (liftedAffineOpensInclusion B S hS p hp hp1).IsMorphismOfSites
      (zariskiChartLiftedSite.{u, t} B S hS).J
      (zariskiAffineLiftedSite.{u, u + 1, u, t} B S hS p hp).J := by
  have := essentiallySmall_lift.{max (u + 1) t, u}
    (SmallAffineZariski B.toBigZariskiSite S (zariskiContains B S hS))
  let E := equivSmallModel.{max (u + 1) t}
    (SmallAffineZariski B.toBigZariskiSite S (zariskiContains B S hS))
  let := rootMorphismOfSites_of_equivalence_inverse.{max (u + 1) t} E
    (SmallAffineZariski.topology B.toBigZariskiSite S (zariskiContains B S hS))
    (zariskiChartLiftedSite.{u, t} B S hS).J
  let := affineOpensInclusion_isMorphismOfSites.{u, t} B S hS p hp hp1
  let := rootMorphismOfSites_of_equivalence.{max (u + 1) t}
    (AsSmall.equiv : AffineCategory B S hS p ≌
      (zariskiAffineLiftedSite.{u, u + 1, u, t} B S hS p hp).C)
    (associatedAffineTopology B S hS p
      (BigAffineZariski.topology B.toBigZariskiSite S hS))
    (zariskiAffineLiftedSite.{u, u + 1, u, t} B S hS p hp).J
  let := isMorphismOfSites_comp.{max (u + 1) t}
    (zariskiAffineLiftedSite.{u, u + 1, u, t} B S hS p hp).J
    (associatedAffineTopology B S hS p
      (BigAffineZariski.topology B.toBigZariskiSite S hS))
    (SmallAffineZariski.topology B.toBigZariskiSite S (zariskiContains B S hS))
    (affineOpensInclusion B S hS p hp1) AsSmall.equiv.functor
  exact (isMorphismOfSites_comp.{max (u + 1) t}
    (zariskiAffineLiftedSite.{u, u + 1, u, t} B S hS p hp).J
    (SmallAffineZariski.topology B.toBigZariskiSite S (zariskiContains B S hS))
    (zariskiChartLiftedSite.{u, t} B S hS).J
    E.inverse
    (affineOpensInclusion B S hS p hp1 ⋙ AsSmall.equiv.functor)).toSmallIsMorphismOfSites

/-- The structure map of the morphism of lifted ringed sites, as an isomorphism: on sections both
structure sheaves are the ring of global functions of an affine open of `S`, raised to the
universe of the lifts. -/
noncomputable def liftedAffineOpensStructureIso :
    (zariskiChartLiftedSite.{u, t} B S hS).O ≅
      ((liftedAffineOpensInclusion B S hS p hp hp1).sheafPushforwardContinuous
        CommRingCat.{max (u + 1) t} (zariskiChartLiftedSite.{u, t} B S hS).J
        (zariskiAffineLiftedSite.{u, u + 1, u, t} B S hS p hp).J).obj
        (zariskiAffineLiftedSite.{u, u + 1, u, t} B S hS p hp).O :=
  haveI := essentiallySmall_lift.{max (u + 1) t, u}
    (SmallAffineZariski B.toBigZariskiSite S (zariskiContains B S hS))
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (Functor.isoWhiskerLeft (equivSmallModel.{max (u + 1) t}
      (SmallAffineZariski B.toBigZariskiSite S (zariskiContains B S hS))).inverse.op
      (Functor.isoWhiskerRight
        (eqToIso (affineOpensInclusion_op_comp_affineStructureCommPresheaf B S hS p hp1).symm)
        SheafOfModules.commRingCatULift.{u, max (u + 1) t}))

/-- **The morphism of lifted ringed sites** from the lift of `(Aff/S)_{Zar}` to the lift of the
small affine Zariski site of `S`, given by the inclusion of the affine opens of `S`. -/
noncomputable def liftedAffineOpensHom :
    RingedSite.Hom (zariskiAffineLiftedSite.{u, u + 1, u, t} B S hS p hp)
      (zariskiChartLiftedSite.{u, t} B S hS) where
  u := liftedAffineOpensInclusion B S hS p hp hp1
  isMorphismOfSites := liftedAffineOpensInclusion_isMorphismOfSites B S hS p hp hp1
  fsharp := (liftedAffineOpensStructureIso B S hS p hp hp1).hom

/-- The functor of `liftedAffineOpensHom` is `liftedAffineOpensInclusion`. -/
@[simp]
theorem liftedAffineOpensHom_u :
    (liftedAffineOpensHom B S hS p hp hp1).u = liftedAffineOpensInclusion B S hS p hp hp1 :=
  rfl

/-- The structure map of the morphism of ringed sites `liftedAffineOpensHom` is an isomorphism. -/
instance liftedAffineOpensHom_fsharp_isIso : IsIso (liftedAffineOpensHom B S hS p hp hp1).fsharp :=
  inferInstanceAs (IsIso (liftedAffineOpensStructureIso B S hS p hp hp1).hom)

/-! ### Coverings by affine opens of `S` -/

include hp in
/-- **The affine opens of `S` cover `(Aff/S)_{Zar}`**: the objects `j(y)`, for `y` an affine open
of `S`, cover the final object of the associated affine Zariski site of `(Sch/S)`. -/
theorem coversTop_affineOpensInclusion :
    (associatedAffineTopology B S hS p
      (BigAffineZariski.topology B.toBigZariskiSite S hS)).CoversTop
      (affineOpensInclusion B S hS p hp1).obj := by
  have hd := affineInclusion_isDenseSubsite_zariski B S hS p hp hp1
  have := (SmallAffineZariski.inclusion_isSpecialCocontinuous B.toBigZariskiSite S
    (zariskiContains B S hS)).2.isCoverDense
  have hK : (bigZariskiOverTopology B S hS).CoversTop
      (affineOpensInclusion B S hS p hp1 ⋙ AffineCategory.inclusion B S hS p).obj :=
    GrothendieckTopology.coversTop_comp_of_isCoverDense
      (SmallAffineZariski.inclusion B.toBigZariskiSite S (zariskiContains B S hS))
      (smallZariskiIncl B S hS)
      (SmallZariski.topology B.toBigZariskiSite S (zariskiContains B S hS))
      _ (coversTop_smallZariskiIncl B S hS)
  intro x
  refine GrothendieckTopology.superset_covering _ ?_
    ((AffineCategory.inclusion B S hS p).cover_lift _
      (bigZariskiOverTopology B S hS)
      (hK ((AffineCategory.inclusion B S hS p).obj x)))
  rintro z f ⟨y, ⟨g⟩⟩
  exact ⟨y, ⟨(AffineCategory.inclusion B S hS p).preimage g⟩⟩

/-- **Every object of the lifted `(Aff/S)_{Zar}` is covered by finitely many objects mapping to
affine opens of `S`.** For every object `x` there is a finite family `x_i ⟶ x` generating a
covering sieve, each `x_i` admitting an arrow to the image of an affine open of `S`, and lying
over open immersions of affine schemes. -/
theorem exists_finite_covering_liftedAffineOpensHom
    (x : (zariskiAffineLiftedSite.{u, u + 1, u, t} B S hS p hp).C) :
    ∃ (n : ℕ) (obj : Fin n → (zariskiAffineLiftedSite.{u, u + 1, u, t} B S hS p hp).C)
      (π : ∀ i, obj i ⟶ x),
      Sieve.ofArrows obj π ∈ (zariskiAffineLiftedSite.{u, u + 1, u, t} B S hS p hp).J x ∧
      (∀ i, ∃ y, Nonempty (obj i ⟶ (liftedAffineOpensHom B S hS p hp hp1).u.obj y)) ∧
      ∀ i, IsOpenImmersion ((zariskiAffineLiftedToScheme.{u, u + 1, u, t} B S hS
        p hp).map (π i)) := by
  have := essentiallySmall_lift.{max (u + 1) t, u}
    (SmallAffineZariski B.toBigZariskiSite S (zariskiContains B S hS))
  obtain ⟨E, hfin, hzar, hcov, hle⟩ := AffineCategory.exists_finite_zariski_covering B S hS
    p hp _
    (coversTop_affineOpensInclusion B S hS p hp hp1 (AsSmall.down.obj x))
  let ε : Fin (Nat.card E.I₀) ≃ E.I₀ := (Finite.equivFin E.I₀).symm
  let E' := E.reindex ε
  have hs : E'.sieve₀ = E.sieve₀ := congrArg Sieve.generate (E.presieve₀_reindex ε)
  obtain ⟨-, hopen⟩ := (Scheme.presieve₀_mem_precoverage_iff _).mp hzar
  refine ⟨Nat.card E.I₀, fun i => AsSmall.up.obj (E'.X i), fun i => AsSmall.up.map (E'.f i),
    ?_, fun i => ?_, fun i => hopen (ε i)⟩
  · refine (RingedSite.lift_asSmallDown_isDenseSubsite.{t}
      (AffineCategory.siteKindRingedSite B S hS p hp .zariski)).functorPushforward_mem_iff.1
      (GrothendieckTopology.superset_covering _ ?_ (hs ▸ hcov))
    rintro Z g ⟨Y, a, b, ⟨i⟩, rfl⟩
    exact ⟨_, AsSmall.up.map (E'.f i), a, Sieve.ofArrows_mk _ _ i, rfl⟩
  · obtain ⟨y, ⟨g⟩⟩ := hle _ (Sieve.ofArrows_mk _ _ (ε i))
    let E₀ := equivSmallModel.{max (u + 1) t}
      (SmallAffineZariski B.toBigZariskiSite S (zariskiContains B S hS))
    exact ⟨E₀.functor.obj y, ⟨AsSmall.up.map
      (g ≫ (affineOpensInclusion B S hS p hp1).map (E₀.unitIso.hom.app y))⟩⟩

section Descent

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance] AlgebraicGeometry.RingedSite.Hom.pushforwardTopos_additive

/-- **Every object of the lifted `(Aff/S)_{Zar}` has a descent cover** for the morphism of
lifted ringed sites `AlgebraicGeometry.ZariskiCharts.liftedAffineOpensHom`: the finite Zariski
covering by objects mapping to affine opens of `S`
(`AlgebraicGeometry.ZariskiCharts.exists_finite_covering_liftedAffineOpensHom`), along which the
cartesian condition descends (`AlgebraicGeometry.Stack.isIso_comparison_of_zariskiEtaleCover`). -/
theorem nonempty_descentCover_liftedAffineOpensHom
    (x : (zariskiAffineLiftedSite.{u, u + 1, u, t} B S hS p hp).C) :
    Nonempty (DescentCover.{t'} (liftedAffineOpensHom B S hS p hp hp1) x) := by
  obtain ⟨n, obj, π, hπ, hhom, hopen⟩ :=
    exists_finite_covering_liftedAffineOpensHom.{u, t} B S hS p hp hp1 x
  have hπ' : Sieve.ofArrows (fun j : ULift.{t'} (Fin n) => obj j.down) (fun j => π j.down) ∈
      (zariskiAffineLiftedSite.{u, u + 1, u, t} B S hS p hp).J x := by
    refine GrothendieckTopology.superset_covering _ ?_ hπ
    rw [Sieve.generate_le_iff]
    rintro _ _ ⟨j⟩
    exact Sieve.ofArrows_mk (fun j : ULift.{t'} (Fin n) => obj j.down) (fun j => π j.down) ⟨j⟩
  have het' : ∀ j : ULift.{t'} (Fin n),
      Etale ((zariskiAffineLiftedToScheme.{u, u + 1, u, t} B S hS p hp).map (π j.down)) :=
    fun j => have := hopen j.down; inferInstance
  exact ⟨⟨ULift.{t'} (Fin n), fun j => obj j.down, fun j => π j.down, hπ', fun j => hhom j.down,
    fun L hL j => isIso_comparison_of_zariskiEtaleCover.{u, u + 1, u, t} B S hS
      p hp x
      (fun j : ULift.{t'} (Fin n) => obj j.down) (fun j : ULift.{t'} (Fin n) => π j.down) hπ'
      het' L hL j⟩⟩

end Descent

/-- **Restriction from `(Aff/S)_{Zar}` to the affine opens of `S` is an equivalence on the
subcategories of Stacks 0GZS.** On the lifted sites, the direct image `f_*` along the morphism of
ringed sites `f` given by the affine opens of `S` is an equivalence, inverse to the derived
pullback `Lf^*`: its functor is full, faithful and cocontinuous, the `ε`-units on the slices of
the lifted `(Aff/S)_{Zar}` are invertible (Stacks 0H0J for the Zariski topology), and every object
has a descent cover by affine opens of `S`. -/
def liftedAffineOpensCartesianEquivalence :
    (IsCartesianPushforwardOn (zariskiChartLiftedSite.{u, t} B S hS)).FullSubcategory ≌
      (IsCartesianPushforwardOn
        (zariskiAffineLiftedSite.{u, u + 1, u, t} B S hS p hp)).FullSubcategory :=
  haveI hX₁ : HasSheafify (zariskiAffineLiftedSite.{u, u + 1, u, t} B S hS p hp).J
      AddCommGrpCat.{max (u + 1) u u t} := inferInstance
  haveI hX₂ : (zariskiAffineLiftedSite.{u, u + 1, u, t} B S hS p hp).J.WEqualsLocallyBijective
      AddCommGrpCat.{max (u + 1) u u t} := inferInstance
  haveI hY₁ : HasSheafify (zariskiChartLiftedSite.{u, t} B S hS).J
      AddCommGrpCat.{max (u + 1) u u t} := inferInstance
  haveI hY₂ : (zariskiChartLiftedSite.{u, t} B S hS).J.WEqualsLocallyBijective
      AddCommGrpCat.{max (u + 1) u u t} := inferInstance
  haveI hX₃ : ∀ U : (zariskiAffineLiftedSite.{u, u + 1, u, t} B S hS p hp).C,
      HasSheafify ((zariskiAffineLiftedSite.{u, u + 1, u, t} B S hS p hp).J.over U)
        AddCommGrpCat.{max (u + 1) u u t} :=
    fun _ => inferInstance
  haveI hX₄ : ∀ U : (zariskiAffineLiftedSite.{u, u + 1, u, t} B S hS p hp).C,
      ((zariskiAffineLiftedSite.{u, u + 1, u, t} B S hS p hp).J.over U).WEqualsLocallyBijective
        AddCommGrpCat.{max (u + 1) u u t} :=
    fun _ => inferInstance
  haveI hY₃ : ∀ U : (zariskiChartLiftedSite.{u, t} B S hS).C,
      HasSheafify ((zariskiChartLiftedSite.{u, t} B S hS).J.over U)
        AddCommGrpCat.{max (u + 1) u u t} :=
    fun _ => inferInstance
  haveI hY₄ : ∀ U : (zariskiChartLiftedSite.{u, t} B S hS).C,
      ((zariskiChartLiftedSite.{u, t} B S hS).J.over U).WEqualsLocallyBijective
        AddCommGrpCat.{max (u + 1) u u t} :=
    fun _ => inferInstance
  haveI : (liftedAffineOpensHom B S hS p hp hp1).u.Full :=
    liftedAffineOpensInclusion_full B S hS p hp hp1
  haveI : (liftedAffineOpensHom B S hS p hp hp1).u.Faithful :=
    liftedAffineOpensInclusion_faithful B S hS p hp hp1
  haveI : (liftedAffineOpensHom B S hS p hp hp1).u.IsCocontinuous
      (zariskiChartLiftedSite.{u, t} B S hS).J
      (zariskiAffineLiftedSite.{u, u + 1, u, t} B S hS p hp).J :=
    liftedAffineOpensInclusion_isCocontinuous B S hS p hp hp1
  @equivalence _ _ (liftedAffineOpensHom B S hS p hp hp1) hX₁ hX₂ hY₁ hY₂ hX₃ hX₄ hY₃ hY₄ _ _ _ _
    (fun x P => by
      let (y : (zariskiAffineLiftedSite.{u, u + 1, u, t} B S hS p hp).C) :=
        Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{max (u + 1) u u t,
          max (u + 1) u u t, max (u + 1) u u t, max (u + 1) u u t}
          (Stacks.ModulesOnACategory.ChaoticComparison.overRingSheaf
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (zariskiAffineLiftedSite.{u, u + 1, u, t} B S hS p hp).O) y)
      open Stacks.ModulesOnACategory.ChaoticComparison in
      convert isIso_derivedEpsilonAdjunction_unit_app_Lpullback_of_baseChange
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (zariskiAffineLiftedSite.{u, u + 1, u, t} B S hS p hp).O)
        (RingedSite.mul_comm_ringSheaf _) x
        (baseChangeIsSheaf_zariskiAffineLiftedSite.{u, u + 1, u, t} B S hS p hp x)
        (baseChangeAcyclic_zariskiAffineLiftedSite.{u, u + 1, u, t} B S hS p hp x) P using 2)
    (nonempty_descentCover_liftedAffineOpensHom.{u, t, 0} B S hS p hp hp1)


end AlgebraicGeometry.ZariskiCharts
