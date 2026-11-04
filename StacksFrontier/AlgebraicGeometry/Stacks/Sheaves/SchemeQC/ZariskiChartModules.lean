module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.SchemeQC.ZariskiChartSite
public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.SmallZariskiModules
public import StacksFrontier.AlgebraicGeometry.Descent.SmallAffineRingedTopos
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffines
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentRestrictionOfUniv
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.RingUniverseLift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalTypesUnderSpecialCocontinuous
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.QuasiCoherenceOnAChaoticSite

/-!
# `O_S`-modules on the affine Zariski charts of a scheme

Let `S` be a scheme in a big fppf site `B` and let `M = max (u + 1) m` be a module universe
containing the universe of the objects of the small Zariski site of `S`. This file identifies the
`O_S`-modules with sections in `M` with the sheaves of modules on the lifted chart site
`AlgebraicGeometry.ZariskiCharts.zariskiChartLiftedSite` of the affine opens of `S`
(`AlgebraicGeometry.ZariskiCharts.zariskiChartModulesEquivalence`), and shows that under this
identification **the quasi-coherent `O_S`-modules are exactly the cartesian ones**
(`AlgebraicGeometry.ZariskiCharts.isCartesianPresheaf_zariskiChartModulesEquivalence_iff`):
an `O_S`-module is quasi-coherent if and only if for every inclusion `U ⊆ V` of affine opens the
restriction map `F(V) ⟶ F(U)` is a base change along `O_S(V) ⟶ O_S(U)`.

The equivalence is the composite of three: Descent, Remark 03FG (modules on the space are modules
on the small Zariski site), the Comparison Lemma along the dense subsite of affine opens
(Stacks 0F1B), and the transport to the small model.

The quasi-coherence criterion is proved in the source's way, on the affine charts. A
quasi-coherent module restricts to a quasi-coherent module on the affine opens, which is
cartesian by flat descent (Stacks 0H04 for the chart rings,
`AlgebraicGeometry.SmallAffineZariski.isIso_restrictionBaseChange_of_isQuasicoherentOnSite`).
Conversely, a module cartesian on affine opens restricts to a module on the affine opens all of
whose comparison maps are invertible, hence a quasi-coherent one; quasi-coherence is intrinsic
to the ringed topos (Stacks 03DM for clause (6) of 03DL along the dense subsite, read with the
coefficient rings raised to the module universe), so the module itself is quasi-coherent.

## Main definitions

* `AlgebraicGeometry.ZariskiCharts.zariskiChartModulesEquivalence`: `O_S`-modules with sections in
  `max (u + 1) m` are sheaves of modules on the lifted chart site.

## Main results

* `AlgebraicGeometry.ZariskiCharts.isQuasicoherentOnSite_iff_isCartesianOnAffines`: an
  `O_S`-module on the small Zariski site is quasi-coherent exactly when its restriction maps
  between affine opens are base changes.
* `AlgebraicGeometry.ZariskiCharts.isCartesianPresheaf_zariskiChartModulesEquivalence_iff`: an
  `O_S`-module is quasi-coherent exactly when its image on the lifted chart site is cartesian.

## References

* [Stacks Project, Tag 03FG](https://stacks.math.columbia.edu/tag/03FG)
* [Stacks Project, Tag 0F1B](https://stacks.math.columbia.edu/tag/0F1B)
* [Stacks Project, Tag 0H04](https://stacks.math.columbia.edu/tag/0H04)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.ModulesOnACategory.ChaoticComparison (IsCartesianPresheaf)

universe u m

namespace AlgebraicGeometry.ZariskiCharts

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The small Zariski ringed site of `S`, read in the big Zariski site carried by `B`. -/
noncomputable abbrev zariskiSmallRingedSite : RingedSite.{u + 1, u, u} :=
  smallZariskiRingedSite B.toBigZariskiSite S (zariskiContains B S hS)

/-- **The Comparison Lemma along the affine opens, at sections in `max (u + 1) m`**: sheaves of
abelian groups on the small Zariski site of `S` restrict to an equivalence with sheaves of
abelian groups on its affine opens. -/
theorem isEquivalence_smallAffineZariskiRestriction_addCommGrpCat :
    ((SmallAffineZariski.inclusion B.toBigZariskiSite S
        (zariskiContains B S hS)).sheafPushforwardContinuous
      AddCommGrpCat.{max (u + 1) m}
      (SmallAffineZariski.topology B.toBigZariskiSite S (zariskiContains B S hS))
      (SmallZariski.topology B.toBigZariskiSite S (zariskiContains B S hS))).IsEquivalence := by
  have hl : ∀ W : (SmallZariski B.toBigZariskiSite S (zariskiContains B S hS))ᵒᵖ,
      HasLimitsOfShape (StructuredArrow W
        (SmallAffineZariski.inclusion B.toBigZariskiSite S (zariskiContains B S hS)).op)
        AddCommGrpCat.{max (u + 1) m} :=
    fun _ ↦ hasLimitsOfShape_of_essentiallySmall.{u} _ _
  infer_instance

/-- **`O_S`-modules are sheaves of modules on the lifted chart site.** For module sections in
`max (u + 1) m`, the category of `O_S`-modules is equivalent to the category of sheaves of
modules on `AlgebraicGeometry.ZariskiCharts.zariskiChartLiftedSite`: Descent, Remark 03FG,
followed by restriction to the affine opens (the Comparison Lemma of Stacks 0F1B), followed by
the transport to the small model. -/
noncomputable def zariskiChartModulesEquivalence :
    SheafOfModules.{max (u + 1) m} S.ringCatSheaf ≌
      SheafOfModules.{max (u + 1) m}
        (Stacks.SheafOfModules.Tensor.ringSheaf (zariskiChartLiftedSite.{u, m} B S hS).O) :=
  haveI := essentiallySmall_lift.{max (u + 1) m, u}
    (SmallAffineZariski B.toBigZariskiSite S (zariskiContains B S hS))
  (smallZariskiModuleEquiv.{u, max (u + 1) m} B.toBigZariskiSite S
      (zariskiContains B S hS)).symm.trans
    ((@Stacks.UniverseLift.moduleRestrictionEquivalenceULift.{max (u + 1) m}
        (zariskiSmallRingedSite B S hS) _ _
        (SmallAffineZariski.topology B.toBigZariskiSite S (zariskiContains B S hS))
        (SmallAffineZariski.inclusion B.toBigZariskiSite S (zariskiContains B S hS)) inferInstance
        (isEquivalence_smallAffineZariskiRestriction_addCommGrpCat.{u, m} B S hS)).trans
      ((zariskiChartRingedSite B S hS).transportRingTransport.{max (u + 1) m}
        (equivSmallModel.{max (u + 1) m}
          (SmallAffineZariski B.toBigZariskiSite S (zariskiContains B S hS)))).sheafEquivalence)

/-- The structure-sheaf identification of Descent, Remark 03FG along the open-image functor
`S_Zar ⥤ Opens S`: the sections of `𝒪_S` over the image of an open subscheme are the global
functions of that open subscheme. -/
noncomputable def smallZariskiRingComparison :
    SmallZariski.structureSheaf B.toBigZariskiSite S (zariskiContains B S hS) ⟶
      ((smallZariskiSiteEquiv B.toBigZariskiSite S
          (zariskiContains B S hS)).functor.sheafPushforwardContinuous
        RingCat.{u} (SmallZariski.topology B.toBigZariskiSite S (zariskiContains B S hS))
        (Opens.grothendieckTopology S.carrier)).obj S.ringCatSheaf :=
  ObjectProperty.homMk
    ((smallZariskiStructureSheaf_pullbackIso B.toBigZariskiSite S (zariskiContains B S hS)).inv.hom)

/-- The comparison map `smallZariskiRingComparison` of structure sheaves is an isomorphism. -/
instance isIso_smallZariskiRingComparison : IsIso (smallZariskiRingComparison B S hS) :=
  inferInstanceAs (IsIso (smallZariskiStructureSheaf_pullbackIso B.toBigZariskiSite S
    (zariskiContains B S hS)).inv)

/-- The inverse of Descent, Remark 03FG is restriction along the open-image functor. -/
theorem smallZariskiModuleEquiv_inverse_obj
    (G : SheafOfModules.{max (u + 1) m} S.ringCatSheaf) :
    (smallZariskiModuleEquiv.{u, max (u + 1) m} B.toBigZariskiSite S
        (zariskiContains B S hS)).inverse.obj G =
      (SheafOfModules.pushforward.{max (u + 1) m} (smallZariskiRingComparison B S hS)).obj G :=
  rfl

/-- **A quasi-coherent `O_S`-module, read on the small Zariski site, is quasi-coherent there**:
quasi-coherence is carried along the restriction of Descent, Remark 03FG. -/
theorem isQuasicoherentOnSite_smallZariskiModuleEquiv_inverse
    (G : SheafOfModules.{max (u + 1) m} S.ringCatSheaf) (hG : G.IsQuasicoherentOnSite) :
    ((smallZariskiModuleEquiv.{u, max (u + 1) m} B.toBigZariskiSite S
        (zariskiContains B S hS)).inverse.obj G).IsQuasicoherentOnSite := by
  rw [smallZariskiModuleEquiv_inverse_obj B S hS]
  have : ∀ X : SmallZariski B.toBigZariskiSite S (zariskiContains B S hS),
      (Over.post (X := X) (smallZariskiSiteEquiv B.toBigZariskiSite S
        (zariskiContains B S hS)).functor).IsContinuous
        ((SmallZariski.topology B.toBigZariskiSite S (zariskiContains B S hS)).over X)
        ((Opens.grothendieckTopology S.carrier).over
          ((smallZariskiSiteEquiv B.toBigZariskiSite S (zariskiContains B S hS)).functor.obj X)) :=
    fun X => Functor.isContinuous_overPost _ _ _ X
  exact Stacks.SheafOfModules.SiteTransport.isQuasicoherentOnSite_pushforward_ofUniv.{u, u, u + 1,
    u, u, m} (smallZariskiSiteEquiv B.toBigZariskiSite S (zariskiContains B S hS)).functor
    (smallZariskiRingComparison B S hS) inferInstance G hG

/-- **A quasi-coherent module on the small Zariski site is cartesian on affine opens** (Stacks
0H04 for the chart rings): for every morphism of affine opens the restriction map is a base
change. The module is restricted to the affine opens, which preserves quasi-coherence, and flat
descent along their finite flat coverings makes it cartesian there. -/
theorem isUniversalArrow_of_isQuasicoherentOnSite_smallZariski
    (G : SheafOfModules.{max (u + 1) m}
      (SmallZariski.structureSheaf B.toBigZariskiSite S (zariskiContains B S hS)))
    (hG : G.IsQuasicoherentOnSite)
    ⦃U V : (SmallAffineZariski B.toBigZariskiSite S (zariskiContains B S hS))ᵒᵖ⦄ (a : V ⟶ U) :
    (ModuleCat.restrictScalars.{max (u + 1) m}
      ((SmallZariski.structureSheaf B.toBigZariskiSite S (zariskiContains B S hS)).obj.map
        ((SmallAffineZariski.inclusion B.toBigZariskiSite S (zariskiContains B S hS)).op.map
          a)).hom).IsUniversalArrow
      (G.val.map ((SmallAffineZariski.inclusion B.toBigZariskiSite S
        (zariskiContains B S hS)).op.map a)) := by
  have h₁ := Stacks.SheafOfModules.isQuasicoherentOnSite_restriction
    (J := SmallZariski.topology B.toBigZariskiSite S (zariskiContains B S hS))
    (K := SmallAffineZariski.topology B.toBigZariskiSite S (zariskiContains B S hS))
    (SmallAffineZariski.inclusion B.toBigZariskiSite S (zariskiContains B S hS))
    (SmallZariski.structureSheaf B.toBigZariskiSite S (zariskiContains B S hS)) G hG
  exact (Functor.isUniversalArrow_iff_isIso (ModuleCat.extendRestrictScalarsAdj
    ((SmallAffineZariski.affineChartRings B.toBigZariskiSite S (zariskiContains B S hS)).map
      a).hom) _).2
    (SmallAffineZariski.isIso_restrictionBaseChange_of_isQuasicoherentOnSite.{u, m}
      B.toBigZariskiSite S (zariskiContains B S hS) _ h₁ a.unop)

/-- The structure presheaf of the small Zariski site of `S` is a sheaf of *sets*: it is the
restriction of `𝒪_S`, a sheaf of sets on the opens of `S`, along the equivalence of sites of
Stacks 020X. -/
theorem isSheaf_smallZariski_structurePresheaf_forget :
    Presheaf.IsSheaf (SmallZariski.topology B.toBigZariskiSite S (zariskiContains B S hS))
      ((SmallZariski.structureSheaf B.toBigZariskiSite S (zariskiContains B S hS)).obj ⋙
        forget RingCat.{u}) :=
  (Presheaf.isSheaf_of_iso_iff (Functor.isoWhiskerRight
    (smallZariskiStructurePresheafIso B.toBigZariskiSite S (zariskiContains B S hS))
    (forget RingCat.{u}))).1
    ((smallZariskiSheafEquivWith B.toBigZariskiSite S (zariskiContains B S hS) (Type u)).inverse.obj
      ((sheafCompose (Opens.grothendieckTopology S.carrier) (forget RingCat.{u})).obj
        S.ringCatSheaf)).property

/-- The ring universe lift `U ↦ ULift Γ(U, 𝒪_U)` of the structure presheaf of the small Zariski
site of `S` into `max (u + 1) m`, as a sheaf of commutative rings. -/
noncomputable def smallZariskiLiftedRing :
    Sheaf (SmallZariski.topology B.toBigZariskiSite S (zariskiContains B S hS))
      CommRingCat.{max (u + 1) m} :=
  ⟨Stacks.Modules.ringULift.{u + 1, u, u, m} (zariskiSmallRingedSite B S hS).O.obj,
    Presheaf.isSheaf_of_isSheaf_comp _ _ (forget₂ CommRingCat RingCat)
      (Stacks.Modules.isSheaf_structureRingPresheaf_ringULift.{u + 1, u, u, m}
        (zariskiSmallRingedSite B S hS).O.obj
        (isSheaf_smallZariski_structurePresheaf_forget B S hS))⟩

/-- The small affine Zariski site of `S` with the ring-lifted structure sheaf, as a ringed site
whose rings and module sections lie in the one universe `max (u + 1) m`. -/
noncomputable abbrev smallAffineZariskiLiftedRingedSite :
    RingedSite.{u + 1, u, max (u + 1) m} :=
  affineRingedSite (SmallAffineZariski.topology B.toBigZariskiSite S (zariskiContains B S hS))
    (SmallZariski.topology B.toBigZariskiSite S (zariskiContains B S hS))
    (SmallAffineZariski.inclusion B.toBigZariskiSite S (zariskiContains B S hS))
    (smallZariskiLiftedRing.{u, m} B S hS)

/-- **A module on the small Zariski site cartesian on affine opens is quasi-coherent.** Raise
the coefficient rings to the module universe; the restriction of the raised module to the affine
opens has all its comparison maps invertible, hence is quasi-coherent; quasi-coherence is
intrinsic along the dense subsite of affine opens (Stacks 03DM for clause (6) of 03DL), and it
descends along the ring universe lift. -/
theorem isQuasicoherentOnSite_of_isUniversalArrow_smallZariski
    (G : SheafOfModules.{max (u + 1) m}
      (SmallZariski.structureSheaf B.toBigZariskiSite S (zariskiContains B S hS)))
    (hG : ∀ ⦃U V : (SmallAffineZariski B.toBigZariskiSite S (zariskiContains B S hS))ᵒᵖ⦄
      (a : V ⟶ U),
      (ModuleCat.restrictScalars.{max (u + 1) m}
        ((SmallZariski.structureSheaf B.toBigZariskiSite S (zariskiContains B S hS)).obj.map
          ((SmallAffineZariski.inclusion B.toBigZariskiSite S (zariskiContains B S hS)).op.map
            a)).hom).IsUniversalArrow
        (G.val.map ((SmallAffineZariski.inclusion B.toBigZariskiSite S
          (zariskiContains B S hS)).op.map a))) :
    G.IsQuasicoherentOnSite := by
  let X := zariskiSmallRingedSite B S hS
  let ι := SmallAffineZariski.inclusion B.toBigZariskiSite S (zariskiContains B S hS)
  let T := Stacks.UniverseLift.uliftRingTransport.{max (u + 1) m} X.O.obj
  let R' := Stacks.SheafOfModules.Tensor.ringSheaf
    (RingedSite.uliftRing.{max (u + 1) m} X).O
  let N := (T.sheafEquivalence (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    (R' := R')).functor.obj G
  have hN : ∀ ⦃U V : (SmallAffineZariski B.toBigZariskiSite S (zariskiContains B S hS))ᵒᵖ⦄
      (a : V ⟶ U),
      (ModuleCat.restrictScalars.{max (u + 1) m} (R'.obj.map (ι.op.map a)).hom).IsUniversalArrow
        (N.val.map (ι.op.map a)) :=
    fun _ _ a => (T.isUniversalArrow_functor_obj_map_iff_of_refl G.val (ι.op.map a)).2 (hG a)
  let Y : RingedSite.{u + 1, u, max (u + 1) m} :=
    affineRingedSite (SmallAffineZariski.topology B.toBigZariskiSite S (zariskiContains B S hS))
      X.J ι (RingedSite.uliftRing.{max (u + 1) m} X).O
  let P : SheafOfModules.{max (u + 1) m} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) :=
    (Stacks.DenseSubsiteModules.moduleRestriction
      (SmallAffineZariski.topology B.toBigZariskiSite S (zariskiContains B S hS)) X.J ι R').obj N
  have hP : P.IsQuasicoherentOnSite :=
    Stacks.SheafOfModules.isQuasicoherentOnSite_of_canonicalMap_isIso Y P fun _ _ f =>
      (Functor.isUniversalArrow_iff_isIso (ModuleCat.extendRestrictScalarsAdj _) _).1 (hN f.op)
  have hNq : N.IsQuasicoherentOnSite :=
    (Stacks.Sheaves.SpecialCocontinuous.isQuasicoherentOnSite_iff
      (SmallAffineZariski.topology B.toBigZariskiSite S (zariskiContains B S hS)) X.J ι R' N).2 hP
  have h𝒪 : Presheaf.IsSheaf X.J
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf X.O.obj) :=
    (SmallZariski.structureSheaf B.toBigZariskiSite S (zariskiContains B S hS)).property
  have hset : Presheaf.IsSheaf X.J
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf X.O.obj ⋙
        forget RingCat.{u}) :=
    isSheaf_smallZariski_structurePresheaf_forget B S hS
  have : SheafOfModules.IsQuasicoherentOnSite
      (R := Stacks.Modules.structureSheafRingULift.{u + 1, u, u, m} (𝒪 := X.O.obj) hset) N := hNq
  let G' : SheafOfModules.{max (u + 1) m}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf X.O.obj h𝒪) := G
  let D := (Stacks.Modules.sheafRingULiftDown.{u + 1, u, u, m, max (u + 1) m} h𝒪 hset).obj N
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso (Iso.refl D : D ≅ G')
    (Stacks.Modules.isQuasicoherentOnSite_sheafRingULiftDown.{u + 1, u, u, m} h𝒪 hset N)

/-- The structure-sheaf identification of Descent, Remark 03FG along the inverse functor
`Opens S ⥤ S_Zar`. -/
noncomputable def smallZariskiRingComparisonInv :
    S.ringCatSheaf ⟶
      ((smallZariskiSiteEquiv B.toBigZariskiSite S
          (zariskiContains B S hS)).inverse.sheafPushforwardContinuous
        RingCat.{u} (Opens.grothendieckTopology S.carrier)
        (SmallZariski.topology B.toBigZariskiSite S (zariskiContains B S hS))).obj
        (SmallZariski.structureSheaf B.toBigZariskiSite S (zariskiContains B S hS)) :=
  ObjectProperty.homMk
    ((smallZariskiStructureSheaf_iso B.toBigZariskiSite S (zariskiContains B S hS)).inv.hom)

/-- The comparison map `smallZariskiRingComparisonInv` of structure sheaves is an isomorphism. -/
instance isIso_smallZariskiRingComparisonInv : IsIso (smallZariskiRingComparisonInv B S hS) :=
  inferInstanceAs (IsIso (smallZariskiStructureSheaf_iso B.toBigZariskiSite S
    (zariskiContains B S hS)).inv)

/-- Descent, Remark 03FG is restriction along the inverse functor `Opens S ⥤ S_Zar`. -/
theorem smallZariskiModuleEquiv_functor_obj
    (G : SheafOfModules.{max (u + 1) m}
      (SmallZariski.structureSheaf B.toBigZariskiSite S (zariskiContains B S hS))) :
    (smallZariskiModuleEquiv.{u, max (u + 1) m} B.toBigZariskiSite S
        (zariskiContains B S hS)).functor.obj G =
      (SheafOfModules.pushforward.{max (u + 1) m} (smallZariskiRingComparisonInv B S hS)).obj G :=
  rfl

/-- **A quasi-coherent module on the small Zariski site gives a quasi-coherent `O_S`-module**
under Descent, Remark 03FG. -/
theorem isQuasicoherentOnSite_smallZariskiModuleEquiv_functor
    (G : SheafOfModules.{max (u + 1) m}
      (SmallZariski.structureSheaf B.toBigZariskiSite S (zariskiContains B S hS)))
    (hG : G.IsQuasicoherentOnSite) :
    ((smallZariskiModuleEquiv.{u, max (u + 1) m} B.toBigZariskiSite S
        (zariskiContains B S hS)).functor.obj G).IsQuasicoherentOnSite := by
  rw [smallZariskiModuleEquiv_functor_obj B S hS]
  have : ∀ X : S.Opens,
      (Over.post (X := X) (smallZariskiSiteEquiv B.toBigZariskiSite S
        (zariskiContains B S hS)).inverse).IsContinuous
        ((Opens.grothendieckTopology S.carrier).over X)
        ((SmallZariski.topology B.toBigZariskiSite S (zariskiContains B S hS)).over
          ((smallZariskiSiteEquiv B.toBigZariskiSite S (zariskiContains B S hS)).inverse.obj X)) :=
    fun X => Functor.isContinuous_overPost _ _ _ X
  exact Stacks.SheafOfModules.SiteTransport.isQuasicoherentOnSite_pushforward_ofUniv.{u + 1, u,
    u, u, u, m} (smallZariskiSiteEquiv B.toBigZariskiSite S (zariskiContains B S hS)).inverse
    (smallZariskiRingComparisonInv B S hS) (isIso_smallZariskiRingComparisonInv B S hS) G hG

/-- **An `O_S`-module is quasi-coherent exactly when, read on the small Zariski site, its
restriction maps between affine opens are base changes.** -/
theorem isQuasicoherentOnSite_iff_isUniversalArrow
    (G : SheafOfModules.{max (u + 1) m} S.ringCatSheaf) :
    G.IsQuasicoherentOnSite ↔
      ∀ ⦃U V : (SmallAffineZariski B.toBigZariskiSite S (zariskiContains B S hS))ᵒᵖ⦄
        (a : V ⟶ U),
        (ModuleCat.restrictScalars.{max (u + 1) m}
          ((SmallZariski.structureSheaf B.toBigZariskiSite S (zariskiContains B S hS)).obj.map
            ((SmallAffineZariski.inclusion B.toBigZariskiSite S (zariskiContains B S hS)).op.map
              a)).hom).IsUniversalArrow
          (((smallZariskiModuleEquiv.{u, max (u + 1) m} B.toBigZariskiSite S
            (zariskiContains B S hS)).inverse.obj G).val.map
            ((SmallAffineZariski.inclusion B.toBigZariskiSite S (zariskiContains B S hS)).op.map
              a)) := by
  refine ⟨fun hG => isUniversalArrow_of_isQuasicoherentOnSite_smallZariski B S hS _
    (isQuasicoherentOnSite_smallZariskiModuleEquiv_inverse B S hS G hG), fun h => ?_⟩
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((smallZariskiModuleEquiv.{u, max (u + 1) m} B.toBigZariskiSite S
      (zariskiContains B S hS)).counitIso.app G)
    (isQuasicoherentOnSite_smallZariskiModuleEquiv_functor B S hS _
      (isQuasicoherentOnSite_of_isUniversalArrow_smallZariski B S hS _ h))

/-- **An `O_S`-module is quasi-coherent exactly when its image on the lifted chart site is
cartesian.** The image is cartesian exactly when the restriction maps of the module between
affine opens of `S` are base changes, which is quasi-coherence by
`AlgebraicGeometry.ZariskiCharts.isQuasicoherentOnSite_iff_isUniversalArrow`. -/
theorem isCartesianPresheaf_zariskiChartModulesEquivalence_iff
    (G : SheafOfModules.{max (u + 1) m} S.ringCatSheaf) :
    IsCartesianPresheaf ((zariskiChartModulesEquivalence.{u, m} B S hS).functor.obj G).val ↔
      G.IsQuasicoherentOnSite := by
  have := essentiallySmall_lift.{max (u + 1) m, u}
    (SmallAffineZariski B.toBigZariskiSite S (zariskiContains B S hS))
  refine (((zariskiChartRingedSite B S hS).transportRingTransport.{max (u + 1) m}
      (equivSmallModel.{max (u + 1) m}
        (SmallAffineZariski B.toBigZariskiSite S
          (zariskiContains B S hS)))).isCartesianPresheaf_functor_obj_iff _).trans ?_
  refine
    (@Stacks.UniverseLift.isCartesianPresheaf_moduleRestrictionEquivalenceULift_iff.{max (u + 1) m}
      (zariskiSmallRingedSite B S hS) _ _
      (SmallAffineZariski.topology B.toBigZariskiSite S (zariskiContains B S hS))
      (SmallAffineZariski.inclusion B.toBigZariskiSite S (zariskiContains B S hS)) inferInstance
      (isEquivalence_smallAffineZariskiRestriction_addCommGrpCat.{u, m} B S hS) _).trans ?_
  exact (isQuasicoherentOnSite_iff_isUniversalArrow B S hS G).symm

end AlgebraicGeometry.ZariskiCharts
