module

public import StacksFrontier.AlgebraicGeometry.Topologies.AffineSiteBaseChangeCech
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.VanishingAlongAFunctorEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.ChaoticComparisonOnCartesianObjects
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.DerivedCollapse
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaRightDerivedUnivLE
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicGlobalSections
public import StacksFrontier.Algebra.Homology.DerivedCategory.InverseLimitHelpers
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EvaluationConservative

/-!
# The base-change sheaves on the slices of a site of affine schemes are acyclic

Let `C` be a category with pullbacks, `L : C ⥤ Scheme` a functor preserving pullbacks whose values
are affine schemes, and `J` a topology on `C` flatly cofinal for `L`.  For an object `x` of `C`
and a module `N` over `O(x)`, the sheaf `N ⊗_{O(x)} O_x` on the slice `(C/x, J)` has vanishing
higher cohomology over every object of the slice, as module-valued right derived functors of
sections.  The global functions of `L` form a sheaf of rings for `J`.

## Main results

* `Stacks.AffineSiteBaseChange.isSheaf_rings`: the global functions of `L` are a sheaf of rings.
* `Stacks.AffineSiteBaseChange.subsingleton_ext_baseChange`: the higher cohomology of the
  abelian sheaf underlying `N ⊗_{O(x)} O_x` vanishes over every object of the slice
  ([Stacks, Tag 03F9] for the finite flat coverings).
* `Stacks.AffineSiteBaseChange.subsingleton_ext_toSheaf_injective`: the abelian sheaf underlying
  an injective sheaf of modules on the slice has no higher cohomology ([Stacks, Tag 03FC] and
  [Stacks, Tag 03F9]).
* `Stacks.AffineSiteBaseChange.isZero_rightDerived_evaluation_baseChange`: **the higher
  module-valued cohomology of `N ⊗_{O(x)} O_x` vanishes over every object of the slice.**

## References

* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
* [Stacks Project, Tag 03FC](https://stacks.math.columbia.edu/tag/03FC)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Stacks.AffineSiteBaseChange

universe t u v w

open Stacks.TerminalBaseChange Stacks.CechSite Stacks.Sites.OverModules

variable {C : Type v} [Category.{w} C] (L : C ⥤ Scheme.{u}) [HasPullbacks C]
  [PreservesLimitsOfShape WalkingCospan L] [∀ X, IsAffine (L.obj X)]

/-- The finite families of the slice at `x` which are covering and flat coverings of schemes,
indexed in the universe `max t u v w`. -/
def flatCovers (J : GrothendieckTopology C) (x : C) (V : Over x) :
    Set { E : PreZeroHypercover.{max t u v w} V // E.sieve₀ ∈ J.over x V } :=
  fun E => Finite E.1.I₀ ∧
    (E.1.map (Over.forget x ⋙ L)).presieve₀ ∈ Scheme.precoverage @Flat (L.obj V.left)

/-- The reindexing of a `0`-hypercover along a universe lift of its index type. -/
def PreZeroHypercover.uliftIndex {D : Type*} [Category D] {X : D}
    (E : PreZeroHypercover.{0} X) : PreZeroHypercover.{max t u v w} X where
  I₀ := ULift.{max t u v w} E.I₀
  X i := E.X i.down
  f i := E.f i.down

/-- Reindexing along a universe lift does not change the presieve. -/
theorem PreZeroHypercover.presieve₀_uliftIndex {D : Type*} [Category D] {X : D}
    (E : PreZeroHypercover.{0} X) :
    (PreZeroHypercover.uliftIndex.{t, u, v, w} E).presieve₀ = E.presieve₀ := by
  funext Y g
  exact propext ⟨fun ⟨i⟩ => ⟨i.down⟩, fun ⟨i⟩ => ⟨ULift.up i⟩⟩

omit [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan L] [∀ (X : C), IsAffine (L.obj X)] in
variable {L} in
/-- The flat coverings are cofinal among the covering sieves of the slice. -/
theorem flatCovers_cofinal {J : GrothendieckTopology C} (hJ : IsFlatCofinal L J) (x : C)
    (V : Over x) (R : Sieve V) (hR : R ∈ J.over x V) :
    ∃ E : { E : PreZeroHypercover.{max t u v w} V // E.sieve₀ ∈ J.over x V },
      E ∈ flatCovers.{t} L J x V ∧ E.1.sieve₀ ≤ R := by
  obtain ⟨E₀, hfin, hflat, hle, hmem⟩ := hJ.over x V R hR
  have hs : (PreZeroHypercover.uliftIndex.{t, u, v, w} E₀).sieve₀ = E₀.sieve₀ :=
    congrArg Sieve.generate (PreZeroHypercover.presieve₀_uliftIndex.{t, u, v, w} E₀)
  have hp : ((PreZeroHypercover.uliftIndex.{t, u, v, w} E₀).map (Over.forget x ⋙ L)).presieve₀ =
      (E₀.map (Over.forget x ⋙ L)).presieve₀ := by
    rw [PreZeroHypercover.presieve₀_map, PreZeroHypercover.presieve₀_uliftIndex,
      ← PreZeroHypercover.presieve₀_map]
  refine ⟨⟨PreZeroHypercover.uliftIndex.{t, u, v, w} E₀, hs.symm ▸ hmem⟩, ⟨?_, ?_⟩,
    hs.symm ▸ hle⟩
  · exact inferInstanceAs (Finite (ULift E₀.I₀))
  · exact hp.symm ▸ hflat

/-- The base-change presheaf on the slice at `x`, along the terminal object `overIdTerminal`, is
the one along `Over.mkIdTerminal`. -/
def baseChangePresheafTerminalIso (x : C)
    (N : ModuleCat.{max t u}
      ((overRingPresheaf (rings L ⋙ forget₂ CommRingCat RingCat) x).obj (op (Over.mk (𝟙 x))))) :
    ((baseChangePresheaf.{t} (overRingPresheaf (rings L ⋙ forget₂ CommRingCat RingCat) x)
        Over.mkIdTerminal).obj N).presheaf ≅
      ((baseChangePresheaf.{t} (overRingPresheaf (rings L ⋙ forget₂ CommRingCat RingCat) x)
        (overIdTerminal x)).obj N).presheaf :=
  (PresheafOfModules.toPresheaf _).mapIso
    ((baseChangePresheafIsoOfTerminal.{t} _ Over.mkIdTerminal (overIdTerminal x)).app N)

/-- **Čech vanishing for the base-change presheaf along `Over.mkIdTerminal`** on a finite flat
covering of an object of the slice. -/
theorem isZero_cechCohomology_flatCover_baseChange (x : C)
    (N : ModuleCat.{max t u v w}
      ((overRingPresheaf (rings L ⋙ forget₂ CommRingCat RingCat) x).obj (op (Over.mk (𝟙 x)))))
    {V : Over x} (E : PreZeroHypercover.{max t u v w} V) (hfin : Finite E.I₀)
    (hE : (E.map (Over.forget x ⋙ L)).presieve₀ ∈ Scheme.precoverage @Flat (L.obj V.left))
    (q : ℕ) (hq : 0 < q) :
    letI := fun n i => Stacks.Sites.hasProduct_fibreProducts E (fun _ _ _ => inferInstance) n i
    IsZero (cechCohomology E ((baseChangePresheaf.{max t v w}
      (overRingPresheaf (rings L ⋙ forget₂ CommRingCat RingCat) x) Over.mkIdTerminal).obj
        N).presheaf q) := by
  let := fun n i => Stacks.Sites.hasProduct_fibreProducts E (fun _ _ _ => inferInstance) n i
  exact (isZero_cechCohomology_baseChangePresheaf_over.{max t v w} L x N E hE q hq).of_iso
    ((HomologicalComplex.homologyFunctor _ _ q).mapIso
      ((Stacks.CechSite.cechComplexFunctor E).mapIso
        (baseChangePresheafTerminalIso.{max t v w} L x N)))

variable {L} in
/-- **The higher cohomology of the base-change sheaf vanishes over every object of the slice**,
in the form of the vanishing of `Ext` out of the free abelian sheaf on the representable. -/
theorem subsingleton_ext_baseChange {J : GrothendieckTopology C} (hJ : IsFlatCofinal L J)
    (x : C)
    (N : ModuleCat.{max t u v w}
      ((overRingPresheaf (rings L ⋙ forget₂ CommRingCat RingCat) x).obj (op (Over.mk (𝟙 x)))))
    (hsh : Presheaf.IsSheaf (J.over x)
      ((baseChangePresheaf.{max t v w} (overRingPresheaf (rings L ⋙ forget₂ CommRingCat RingCat) x)
        Over.mkIdTerminal).obj N).presheaf)
    [HasSheafify (J.over x) AddCommGrpCat.{max t u v w}]
    [HasExt.{max t u v w} (Sheaf (J.over x) AddCommGrpCat.{max t u v w})]
    (V : Over x) (p : ℕ) (hp : 0 < p) :
    Subsingleton (Abelian.Ext ((presheafToSheaf (J.over x) AddCommGrpCat.{max t u v w}).obj
      (uliftYoneda.{max t u v w}.obj V ⋙ AddCommGrpCat.free))
      ⟨_, hsh⟩ p) :=
  subsingleton_ext_of_cechCohomology_isZero.{max t u v w, 0, max t u v w, w, max v w}
    (J.over x) Set.univ (flatCovers.{t} L J x)
    (fun E _ q i => Stacks.Sites.hasProduct_fibreProducts E.1 (fun _ _ _ => inferInstance) q i)
    (fun _ _ => ⟨trivial, fun _ => trivial, fun _ _ => trivial⟩)
    (fun V _ R hR => flatCovers_cofinal.{t} hJ x V R hR) ⟨_, hsh⟩
    (fun E hE q hq => isZero_cechCohomology_flatCover_baseChange.{t} L x N E.1 hE.1 hE.2 q hq)
    V trivial p hp

/-! ### The sheaf of rings -/

section Rings

variable {L} {J : GrothendieckTopology C}

/-- **The global functions of `L` form a sheaf of rings** for a flatly cofinal topology. -/
theorem isSheaf_rings (hJ : IsFlatCofinal L J) :
    Presheaf.IsSheaf J (rings L ⋙ forget₂ CommRingCat RingCat) := by
  have : ∀ Y : C, IsAffine (unop (L.op.obj (op Y))) := fun Y =>
    (inferInstance : IsAffine (L.obj Y))
  have hff : ∀ {U : C} (E : PreZeroHypercover.{0} U), Finite E.I₀ →
      (E.map L).presieve₀ ∈ Scheme.precoverage @Flat (L.obj U) →
      (RingHom.pi (fun k => ((rings L).map (E.f k).op).hom)).FaithfullyFlat := by
    intro U E hfin hE
    obtain ⟨hcover, hflat⟩ := (Scheme.presieve₀_mem_precoverage_iff (E.map L)).mp hE
    let _ (i : E.I₀) : Flat (L.map (E.f i)) := hflat i
    exact Scheme.faithfullyFlat_pi_appTop (fun i => L.obj (E.X i))
      (fun i => L.map (E.f i)) hcover
  have hpo : ∀ {X Y Z P : C} {fst : P ⟶ X} {snd : P ⟶ Y} {a : X ⟶ Z} {b : Y ⟶ Z},
      IsPullback fst snd a b →
      IsPushout ((rings L).map a.op) ((rings L).map b.op) ((rings L).map fst.op)
        ((rings L).map snd.op) := fun h =>
    isPushout_appTop_of_isPullback (Functor.map_isPullback L h)
  let M := Stacks.PresheafOfModules.largeUnit.{v, w, u, 0} (rings L)
  have h := Stacks.PresheafOfModules.isSheaf_of_cartesian_of_flat_refinements'.{u, v, u, 0, w, 0}
    L (rings L) hff hpo M
    (fun f => Stacks.PresheafOfModules.isIso_restrictionBaseChange_largeUnit (rings L) f) J
    (fun S hS => by
      obtain ⟨E, hfin, hE, hES, -⟩ := hJ _ S hS
      exact ⟨E, hfin, hE, hES⟩)
  have key : Presieve.IsSheaf J (M.presheaf ⋙ forget AddCommGrpCat) :=
    Presieve.isSheaf_iso J (Functor.isoWhiskerLeft M.presheaf AddCommGrpCat.coyonedaObjIsoForget)
      (h _)
  exact Stacks.Sites.isSheaf_ringCat_of_isSheaf_forget _ _
    (Presieve.isSheaf_iso J (NatIso.ofComponents (fun X => Equiv.ulift.toIso) (fun f => rfl)) key)

/-- The sheaf of rings of global functions of `L`, for a flatly cofinal topology. -/
abbrev ringsSheaf (hJ : IsFlatCofinal L J) : Sheaf J RingCat.{u} :=
  ⟨rings L ⋙ forget₂ CommRingCat RingCat, isSheaf_rings hJ⟩

end Rings

/-! ### Injective sheaves of modules -/

section Injective

variable {L} {J : GrothendieckTopology C} (hJ : IsFlatCofinal L J)

/-- The ringed site of the slice at `x` of a site of affine schemes, with the global functions
of `L` as structure sheaf. -/
abbrev sliceRingedSite (x : C) : AlgebraicGeometry.RingedSite.{max v w, w, u} where
  C := Over x
  J := J.over x
  O := ⟨(Over.forget x).op ⋙ rings L, (Over.forget x).op_comp_isSheaf (J.over x) J
    ⟨rings L, Presheaf.isSheaf_of_isSheaf_comp J (rings L) (forget₂ CommRingCat RingCat)
      (isSheaf_rings hJ)⟩⟩

/-- The sheaf of rings of the ringed slice is the restriction of `ringsSheaf` to the slice. -/
theorem sliceRingedSite_ringSheaf (x : C) :
    (Stacks.SheafOfModules.Tensor.ringSheaf (sliceRingedSite hJ x).O) =
    Stacks.ModulesOnACategory.ChaoticComparison.overRingSheaf (ringsSheaf hJ) x := rfl

/-- **The underlying abelian sheaf of an injective sheaf of modules on the slice has no higher
cohomology over any object.** -/
theorem subsingleton_ext_toSheaf_injective (x : C)
    [HasSheafify (J.over x) AddCommGrpCat.{max t u v w}]
    [HasExt.{max t u v w} (Sheaf (J.over x) AddCommGrpCat.{max t u v w})]
    (I : SheafOfModules.{max t u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (sliceRingedSite hJ x).O)) [Injective I]
    (V : Over x) (p : ℕ) (hp : 0 < p) :
    Subsingleton (Abelian.Ext ((presheafToSheaf (J.over x) AddCommGrpCat.{max t u v w}).obj
      (uliftYoneda.{max t u v w}.obj V ⋙ AddCommGrpCat.free))
      ((SheafOfModules.toSheaf _).obj I) p) :=
  subsingleton_ext_of_cechCohomology_isZero.{max t u v w, 0, max t u v w, w, max v w}
    (J.over x) Set.univ (flatCovers.{t} L J x)
    (fun E _ q i => Stacks.Sites.hasProduct_fibreProducts E.1 (fun _ _ _ => inferInstance) q i)
    (fun _ _ => ⟨trivial, fun _ => trivial, fun _ _ => trivial⟩)
    (fun V _ R hR => flatCovers_cofinal.{t} hJ x V R hR) _
    (fun {V'} E hE q hq => by
      let := fun n i => Stacks.Sites.hasProduct_fibreProducts E.1 (fun _ _ _ => inferInstance) n i
      exact injective_moduleCechCohomology_isZero.{0, max t u v w} (sliceRingedSite hJ x) E.1 I
        q hq)
    V trivial p hp

end Injective

/-! ### The module-valued cohomology of the base-change sheaf -/

section Module

attribute [local instance] HasDerivedCategory.standard
  Stacks.SheafOfModulesEvaluation.evaluation_additive
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

-- The ambient-universe instances on sheaves of modules have their universe as a `max` pattern
-- which the module universe here does not match syntactically; left in place they leave the
-- universe of the statement below unsolved.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives
  Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_isGrothendieckAbelian
  Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory

variable {L} {J : GrothendieckTopology C} (hJ : IsFlatCofinal L J)

open Stacks.ModulesOnACategory.ChaoticComparison in
/-- **The higher module-valued cohomology of the base-change sheaf `N ⊗_{O(x)} O_x` vanishes over
every object of the slice at `x`.** -/
theorem isZero_rightDerived_evaluation_baseChange (x : C)
    [HasSheafify (J.over x) AddCommGrpCat.{max t u v w}]
    [(J.over x).WEqualsLocallyBijective AddCommGrpCat.{max t u v w}]
    [EnoughInjectives (SheafOfModules.{max t u v w} (overRingSheaf (ringsSheaf hJ) x))]
    (N : ModuleCat.{max t u v w}
      ((overRingPresheaf (ringsSheaf hJ).obj x).obj (op (Over.mk (𝟙 x)))))
    (hsh : Presheaf.IsSheaf (J.over x)
      ((baseChangePresheaf.{max t v w} (overRingPresheaf (ringsSheaf hJ).obj x)
        Over.mkIdTerminal).obj N).presheaf)
    (V : Over x) (p : ℕ) (hp : 0 < p) :
    IsZero (((_root_.SheafOfModules.evaluation (overRingSheaf (ringsSheaf hJ) x)
      (op V)).rightDerived
      p).obj (⟨(baseChangePresheaf.{max t v w} (overRingPresheaf (ringsSheaf hJ).obj x)
        Over.mkIdTerminal).obj N, hsh⟩ :
          SheafOfModules.{max t u v w} (overRingSheaf (ringsSheaf hJ) x))) := by
  let R' := overRingSheaf (ringsSheaf hJ) x
  let Fsh : SheafOfModules.{max t u v w} R' := ⟨_, hsh⟩
  let F := _root_.SheafOfModules.toSheaf.{max t u v w} R'
  let G := (sheafSections (J.over x) AddCommGrpCat.{max t u v w}).obj (op V)
  have : EnoughInjectives (Sheaf (J.over x) AddCommGrpCat.{max t u v w}) :=
    Stacks.Cohomology.SiteModules.site_enoughInjectives_addCommGrp.{max v w, w, max t u}
  have : HasExt.{max t u v w} (Sheaf (J.over x) AddCommGrpCat.{max t u v w}) :=
    hasExt_of_enoughInjectives _
  have hzero : ∀ (Y : Sheaf (J.over x) AddCommGrpCat.{max t u v w}) (q : ℕ),
      Subsingleton (Abelian.Ext ((presheafToSheaf (J.over x) AddCommGrpCat.{max t u v w}).obj
        (uliftYoneda.{max t u v w}.obj V ⋙ AddCommGrpCat.free)) Y q) →
      IsZero ((G.rightDerived q).obj Y) := by
    intro Y q h
    obtain ⟨e⟩ :=
      Stacks.Cohomology.FreeYonedaUnivLE.nonempty_extFunctorObj_iso_rightDerived_sections.{
        max t u} (J.over x) V q
    exact (AddCommGrpCat.isZero_iff_subsingleton.mpr h).of_iso (e.app Y).symm
  have hac : ∀ I : SheafOfModules.{max t u v w} R', Injective I → G.rightAcyclic (F.obj I) := by
    intro I hI
    rw [rightAcyclic_iff_isZero_rightDerived]
    intro q hq
    exact hzero _ q (@subsingleton_ext_toSheaf_injective.{t} C _ L _ _ _ J hJ x _ _ I hI V q hq)
  have e1 := Stacks.Cohomology.AcyclicCollapse.rightDerivedCompIsoOfAcyclic F G hac p
  have h2 : IsZero (((F ⋙ G).rightDerived p).obj Fsh) :=
    (hzero _ p (subsingleton_ext_baseChange.{t} hJ x N hsh V p hp)).of_iso (e1.app Fsh)
  let Ev := _root_.SheafOfModules.evaluation R' (op V)
  let T := forget₂ (ModuleCat.{max t u v w} (R'.obj.obj (op V))) AddCommGrpCat.{max t u v w}
  let α : F ⋙ G ≅ Ev ⋙ T := NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)
  have h3 : IsZero (((Ev ⋙ T).rightDerived p).obj Fsh) :=
    h2.of_iso
      { hom := (NatTrans.rightDerived α.inv p).app Fsh
        inv := (NatTrans.rightDerived α.hom p).app Fsh
        hom_inv_id := by
          rw [← NatTrans.comp_app, ← NatTrans.rightDerived_comp, α.inv_hom_id,
            NatTrans.rightDerived_id]
          rfl
        inv_hom_id := by
          rw [← NatTrans.comp_app, ← NatTrans.rightDerived_comp, α.hom_inv_id,
            NatTrans.rightDerived_id]
          rfl }
  obtain ⟨e⟩ := Stacks.Cohomology.rightDerived_comp_iso_of_preservesHomology Ev T p Fsh
  exact ModuleCat.isZero_iff_subsingleton.mpr
    (AddCommGrpCat.isZero_iff_subsingleton.mp (h3.of_iso e))

end Module

end Stacks.AffineSiteBaseChange
