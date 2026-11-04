module

public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.SiteFunctorLimits
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Precoverage
public import StacksFrontier.CategoryTheory.Sites.Continuous
public import StacksFrontier.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi
public import StacksCore.Tactic.StacksAttribute

/-!
# The small pro-étale topos inside a big pro-étale topos

For a morphism `f : T ⟶ S` in a chosen big pro-étale site, composition with `f` sends the small
pro-étale site of `T` to the big pro-étale site over `S`. That functor is both cocontinuous and
continuous, so it induces a morphism of topoi whose inverse image is restriction along it, and
whose inverse image in turn has a left adjoint preserving fibre products and equalizers.

## Main definitions

* `AlgebraicGeometry.ProEtale.smallProetaleToBigProetaleFunctor` — composition with `f`.
* `AlgebraicGeometry.ProEtale.smallProetaleToBigProetaleMorphism` — the induced morphism of
  topoi.
* `AlgebraicGeometry.ProEtale.smallProetaleToBigProetaleLowerShriek` — the left adjoint of
  inverse image.

## Main results

* `AlgebraicGeometry.ProEtale.smallProetaleToBigProetaleFunctor_isCocontinuous` and
  `AlgebraicGeometry.ProEtale.smallProetaleToBigProetaleFunctor_isContinuous` — cocontinuity
  and continuity of composition with `f`.
* `CategoryTheory.Functor.sheafPullbackCocontinuousIsoSheafPushforwardContinuous` — the formula
  for inverse image on sections.
* `AlgebraicGeometry.ProEtale.smallProetaleToBigProetaleLowerShriekAdjunction` — the
  lower-shriek adjunction; the two preservation instances beside it record that lower shriek
  preserves fibre products and equalizers.

## Implementation notes

The small pro-étale site of `T` is the full subcategory of the big slice over `T` cut out by
the objects weakly étale over `T`. The displayed equality of sections is represented by the
canonical natural isomorphism between inverse image and restriction for a functor which is both
continuous and cocontinuous; its objectwise form is
`CategoryTheory.Functor.sheafPullbackCocontinuousObjObjIso`. The morphism of topoi is assembled
from the general cocontinuous-site construction, and continuity is recorded separately because
it also supplies the lower-shriek construction.

Covering families of the big slice and of the small site are identified with the comap of the
big site's precoverage along the respective forgetful functors, which is what reduces the site
axioms for both to the site axioms for the big pro-étale site.

## References

* [Stacks Project, Tag 098P](https://stacks.math.columbia.edu/tag/098P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProEtale

add_to_stacks 098P "the inverse-image formula"
  CategoryTheory.Functor.sheafPullbackCocontinuousIsoSheafPushforwardContinuous

/-- Mapping a family of arrows along a functor gives the family `g` when the images agree up to
`eqToHom`. -/
private theorem map_ofArrows_eq_ofArrows_of_eqToHom
    {C D : Type*} [Category C] [Category D] (G : C ⥤ D) {X : C} {I : Type*} {Y : I → C}
    (f : ∀ i, Y i ⟶ X) {Z : I → D} (g : ∀ i, Z i ⟶ G.obj X) (hobj : ∀ i, G.obj (Y i) = Z i)
    (hcomm : ∀ i, G.map (f i) = eqToHom (hobj i) ≫ g i) :
    (Presieve.ofArrows Y f).map G = Presieve.ofArrows Z g := by
  rw [Presieve.map_ofArrows]
  apply le_antisymm <;> rw [Presieve.ofArrows_le_iff] <;> intro i
  · exact Presieve.ofArrows.mk' i (hobj i) (hcomm i)
  · exact Presieve.ofArrows.mk' i (hobj i).symm
      (by rw [hcomm, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp])

variable (B : BigProetaleSite.{u}) (T S : B.Scheme) (f : T ⟶ S)

include f

/-- Send a weakly étale object `U / T` to the composite `U / S`. -/
@[stacks 098P "the functor"]
public abbrev smallProetaleToBigProetaleFunctor :
    SmallProetale B T.obj T.property ⥤ BigProetaleOver B S.obj S.property :=
  SmallProetale.inclusion B T.obj T.property ⋙ Over.map f

private instance smallProetaleToBigProetale_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan
      (smallProetaleToBigProetaleFunctor B T S f) :=
  inferInstance

private instance smallProetaleToBigProetale_preservesEqualizers :
    PreservesLimitsOfShape WalkingParallelPair
      (smallProetaleToBigProetaleFunctor B T S f) :=
  inferInstance

private def proetaleBigOverPrecoverage (B : BigProetaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :
    Precoverage (BigProetaleOver B S hS) where
  coverings X := {R | ∃ E : PreZeroHypercover X,
    R = E.presieve₀ ∧ BigProetaleOver.IsCovering B S hS ⟨X, E⟩}

omit f in
private theorem proetaleBigOver_mem_precoverage_iff
    (B : BigProetaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : BigProetaleOver B S hS} {R : Presieve X} :
    R ∈ proetaleBigOverPrecoverage B S hS X ↔
      ∃ E : PreZeroHypercover X, R = E.presieve₀ ∧
        BigProetaleOver.IsCovering B S hS ⟨X, E⟩ := Iff.rfl

omit f in
private theorem proetaleBigOver_precoverage_eq_comap
    (B : BigProetaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    proetaleBigOverPrecoverage B S hS =
      B.precoverage.comap (Over.forget (⟨S, hS⟩ : B.Scheme)) := by
  ext U R
  rw [proetaleBigOver_mem_precoverage_iff, Precoverage.mem_comap_iff,
    BigProetaleSite.mem_precoverage_iff]
  constructor
  · rintro ⟨E, hR, hE⟩
    refine ⟨E.map (Over.forget (⟨S, hS⟩ : B.Scheme)), ?_, hE⟩
    rw [PreZeroHypercover.presieve₀_map, hR]
  · rintro ⟨E, hR, hE⟩
    let E' : PreZeroHypercover U :=
      ⟨E.I₀, fun i => Over.mk (E.f i ≫ U.hom),
        fun i => Over.homMk (E.f i) (by simp)⟩
    have hmap : E'.map (Over.forget (⟨S, hS⟩ : B.Scheme)) = E := by
      cases E
      rfl
    have hpresieve : E'.presieve₀.map (Over.forget (⟨S, hS⟩ : B.Scheme)) =
        E.presieve₀ := by
      rw [← PreZeroHypercover.presieve₀_map, hmap]
    have hR' : R = E'.presieve₀ :=
      overForget_presieve_map_injective (U := U) (R := R)
        (Q := E'.presieve₀) (hR.symm.trans hpresieve.symm)
    refine ⟨E', hR', ?_⟩
    show B.covering ⟨(Over.forget (⟨S, hS⟩ : B.Scheme)).obj U,
      E'.map (Over.forget (⟨S, hS⟩ : B.Scheme))⟩
    simpa [hmap] using hE

omit f in
private instance proetaleBigOver_precoverage_hasIsos
    (B : BigProetaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (proetaleBigOverPrecoverage B S hS).HasIsos := by
  rw [proetaleBigOver_precoverage_eq_comap]
  infer_instance

omit f in
private instance proetaleBigOver_precoverage_stableUnderBaseChange
    (B : BigProetaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (proetaleBigOverPrecoverage B S hS).IsStableUnderBaseChange := by
  let : PreservesLimitsOfShape WalkingCospan
      (Over.forget (⟨S, hS⟩ : B.Scheme)) := inferInstance
  rw [proetaleBigOver_precoverage_eq_comap]
  infer_instance

omit f in
private instance proetaleBigOver_precoverage_stableUnderComposition
    (B : BigProetaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (proetaleBigOverPrecoverage B S hS).IsStableUnderComposition := by
  rw [proetaleBigOver_precoverage_eq_comap]
  infer_instance

omit f in
private instance proetaleBigOver_precoverage_hasPullbacks
    (B : BigProetaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (proetaleBigOverPrecoverage B S hS).HasPullbacks := by
  let : CreatesLimitsOfShape WalkingCospan
      (Over.forget (⟨S, hS⟩ : B.Scheme)) := inferInstance
  rw [proetaleBigOver_precoverage_eq_comap]
  infer_instance

omit f in
private theorem smallProetale_presieve_map_injective
    {X : SmallProetale B T.obj T.property} {R Q : Presieve X}
    (h : R.map (SmallProetale.inclusion B T.obj T.property) =
      Q.map (SmallProetale.inclusion B T.obj T.property)) : R = Q := by
  have key : ∀ {R Q : Presieve X}, R.map (SmallProetale.inclusion B T.obj T.property) =
      Q.map (SmallProetale.inclusion B T.obj T.property) → R ≤ Q := by
    intro R Q h Y g hg
    have hm := Presieve.map_map (F := SmallProetale.inclusion B T.obj T.property) hg
    rw [h, Presieve.map_iff] at hm
    obtain ⟨Z, hZ, a, ha, hfac⟩ := hm
    have hZY : Z = Y := by cases Z; cases Y; cases hZ; rfl
    cases hZY
    have hfac' : a = g := by
      apply (SmallProetale.inclusion B T.obj T.property).map_injective
      simpa using hfac
    simpa [hfac'] using ha
  exact le_antisymm (key h) (key h.symm)

omit B T f in
private theorem weaklyEtale_left_of_isCovering (B : BigProetaleSite.{u}) {U : Scheme.{u}}
    {hU : B.Contains U} {Y : BigProetaleOver B U hU} {E : PreZeroHypercover Y}
    (hE : BigProetaleOver.IsCovering B U hU ⟨Y, E⟩) (i : E.I₀) :
    WeaklyEtale (B.inclusion.map (E.f i).left) := by
  have hweak := AlgebraicGeometry.Scheme.proetalePrecoverage_le_precoverage_weaklyEtale
    ((BigProetaleOver.toScheme B U hU).obj Y)
    ((B.isProetaleCovering_iff _).mp ((B.covering_iff _).mp hE).1)
  have hi : WeaklyEtale ((BigProetaleOver.toScheme B U hU).map (E.f i)) :=
    (MorphismProperty.ofArrows_mem_precoverage.mp hweak) i
  simpa [BigProetaleOver.toScheme] using hi

omit f in
private def SmallProetale.liftPreZeroHypercover {X : SmallProetale B T.obj T.property}
    (E : PreZeroHypercover X.obj.left) (hE : ∀ i, WeaklyEtale (B.inclusion.map (E.f i))) :
    PreZeroHypercover X :=
  ⟨E.I₀, fun i => ⟨Over.mk (E.f i ≫ X.obj.hom), by
    change WeaklyEtale (B.inclusion.map (E.f i ≫ X.obj.hom))
    have : WeaklyEtale (B.inclusion.map X.obj.hom) := X.property
    rw [Functor.map_comp]
    infer_instance⟩,
   fun i => ObjectProperty.homMk (Over.homMk (E.f i) rfl)⟩

omit f in
private theorem SmallProetale.isCovering_liftPreZeroHypercover
    {X : SmallProetale B T.obj T.property} {E : PreZeroHypercover X.obj.left}
    (hw : ∀ i, WeaklyEtale (B.inclusion.map (E.f i))) (hE : B.covering ⟨_, E⟩) :
    SmallProetale.IsCovering B T.obj T.property ⟨X, liftPreZeroHypercover B T E hw⟩ :=
  hE

omit f in
private theorem smallProetale_precoverage_eq_comap :
    SmallProetale.precoverage B T.obj T.property =
      (proetaleBigOverPrecoverage B T.obj T.property).comap
        (SmallProetale.inclusion B T.obj T.property) := by
  ext X R
  rw [SmallProetale.mem_precoverage_iff, Precoverage.mem_comap_iff,
    proetaleBigOver_mem_precoverage_iff]
  constructor
  · rintro ⟨E, rfl, hE⟩
    exact ⟨E.map (SmallProetale.inclusion B T.obj T.property),
      (PreZeroHypercover.presieve₀_map
        (F := SmallProetale.inclusion B T.obj T.property) E).symm, hE⟩
  · rintro ⟨E, hR, hE⟩
    have hw := weaklyEtale_left_of_isCovering B hE
    let E' : PreZeroHypercover X :=
      SmallProetale.liftPreZeroHypercover B T (E.map (Over.forget _)) hw
    have hobj (i : E.I₀) :
        (SmallProetale.inclusion B T.obj T.property).obj (E'.X i) = E.X i := by
      apply CostructuredArrow.obj_ext
        ((SmallProetale.inclusion B T.obj T.property).obj (E'.X i)) (E.X i) rfl
      exact (Category.id_comp _).trans (Over.w (E.f i)).symm
    have hcomm (i : E.I₀) :
        (E'.map (SmallProetale.inclusion B T.obj T.property)).f i =
          eqToHom (hobj i) ≫ E.f i := by
      apply Over.OverMorphism.ext
      show (E.f i).left = (eqToHom (hobj i)).left ≫ (E.f i).left
      simp only [Over.eqToHom_left]
      rfl
    have hpresieve : E'.presieve₀.map (SmallProetale.inclusion B T.obj T.property) =
        E.presieve₀ :=
      map_ofArrows_eq_ofArrows_of_eqToHom _ E'.f E.f hobj hcomm
    exact ⟨E', smallProetale_presieve_map_injective B T (hR.trans hpresieve.symm),
      SmallProetale.isCovering_liftPreZeroHypercover B T hw hE⟩

omit f in
private instance smallProetalePrecoverage_stableUnderBaseChange :
    (SmallProetale.precoverage B T.obj T.property).IsStableUnderBaseChange := by
  rw [smallProetale_precoverage_eq_comap]
  let : PreservesLimitsOfShape WalkingCospan
      (SmallProetale.inclusion B T.obj T.property) :=
    smallProetaleInclusion_preservesPullbacks B T.obj T.property
  let : B.precoverage.IsStableUnderBaseChange := inferInstance
  rw [proetaleBigOver_precoverage_eq_comap]
  infer_instance

omit B T S f in
private theorem presieve_map_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    {X : C} (R : Presieve X) (F : C ⥤ D) (G : D ⥤ E) :
    (R.map F).map G = R.map (F ⋙ G) := by
  funext Y g
  apply propext
  constructor
  · intro hg
    obtain ⟨Z, hZ, a, ha, hfac⟩ := Presieve.map_iff.mp hg
    obtain ⟨W, hW, b, hb, hfac'⟩ := Presieve.map_iff.mp ha
    have h' : G.obj (F.obj W) = Y := (congrArg G.obj hW).trans hZ
    refine Presieve.map_iff.mpr ⟨W, h', b, hb, ?_⟩
    calc
      G.map (F.map b) = G.map (eqToHom hW ≫ a) := congrArg G.map hfac'
      _ = G.map (eqToHom hW) ≫ G.map a := G.map_comp _ _
      _ = eqToHom (congrArg G.obj hW) ≫ G.map a := by rw [eqToHom_map]
      _ = eqToHom (congrArg G.obj hW) ≫ (eqToHom hZ ≫ g) := by rw [hfac]
      _ = eqToHom h' ≫ g := by simp
  · intro hg
    obtain ⟨W, hW, b, hb, hfac⟩ := Presieve.map_iff.mp hg
    exact Presieve.map_iff.mpr ⟨F.obj W, hW, F.map b, Presieve.map_map hb, hfac⟩

omit f in
/-- **Small pro-étale coverings are the pro-étale coverings of the underlying schemes.** The
precoverage of the small pro-étale site of `T` in a chosen big pro-étale site is the restriction
of the pro-étale precoverage on all schemes along the functor sending a weakly étale object over
`T` to its underlying scheme.

This is the small-site form of `AlgebraicGeometry.ProEtale.BigProetaleSite.precoverage_eq_comap`,
and like it the content is that the index bound `BigProetaleSite.coveringBound` carried by
`AlgebraicGeometry.ProEtale.SmallProetale.IsCovering` imposes no restriction on the covering
*presieves*: a presieve on an object of the small site is covering as soon as its image in schemes
is a pro-étale covering, the chosen covering family presenting it being supplied by
`BigProetaleSite.covering_representatives` and then lifted back along the two full subcategory
inclusions. It is not an identification of the two classes of indexed families. -/
public theorem SmallProetale.precoverage_eq_comap :
    SmallProetale.precoverage B T.obj T.property =
      AlgebraicGeometry.Scheme.proetalePrecoverage.comap
        (SmallProetale.toScheme B T.obj T.property) := by
  rw [smallProetale_precoverage_eq_comap B T, proetaleBigOver_precoverage_eq_comap,
    B.precoverage_eq_comap]
  ext X R
  simp only [Precoverage.mem_comap_iff, presieve_map_comp]
  rfl

omit f in
/-- A presieve on an object of the small pro-étale site is covering as soon as its image in
schemes is a pro-étale covering of the underlying scheme; the index bound of the chosen big site
is no obstruction. This is the direction of
`AlgebraicGeometry.ProEtale.SmallProetale.precoverage_eq_comap` that is used to produce covering
families of the small site out of Zariski or pro-étale covers. -/
public theorem SmallProetale.mem_precoverage_of_map_mem
    {X : SmallProetale B T.obj T.property} {R : Presieve X}
    (hR : R.map (SmallProetale.toScheme B T.obj T.property) ∈
      AlgebraicGeometry.Scheme.proetalePrecoverage
        ((SmallProetale.toScheme B T.obj T.property).obj X)) :
    R ∈ SmallProetale.precoverage B T.obj T.property X := by
  rwa [SmallProetale.precoverage_eq_comap B T, Precoverage.mem_comap_iff]

omit f in
private theorem proetaleBigOver_topology_eq
    (B : BigProetaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    BigProetaleOver.topology B S hS =
      (proetaleBigOverPrecoverage B S hS).toGrothendieck := by
  show B.precoverage.toGrothendieck.over (⟨S, hS⟩ : B.Scheme) =
    (proetaleBigOverPrecoverage B S hS).toGrothendieck
  rw [proetaleBigOver_precoverage_eq_comap]
  exact over_toGrothendieck_eq_toGrothendieck_comap_forget
    B.precoverage (⟨S, hS⟩ : B.Scheme)

private theorem smallProetaleToBigProetale_preimage_isCovering
    {X : SmallProetale B T.obj T.property}
    {R : Presieve ((smallProetaleToBigProetaleFunctor B T S f).obj X)}
    (hR : R ∈ proetaleBigOverPrecoverage B S.obj S.property
      ((smallProetaleToBigProetaleFunctor B T S f).obj X)) :
    ∃ Q ∈ SmallProetale.precoverage B T.obj T.property X,
      Q.map (smallProetaleToBigProetaleFunctor B T S f) ≤ R := by
  rw [proetaleBigOver_mem_precoverage_iff] at hR
  obtain ⟨E, hER, hE⟩ := hR
  have hw := weaklyEtale_left_of_isCovering B hE
  let E' : PreZeroHypercover X :=
    SmallProetale.liftPreZeroHypercover B T (E.map (Over.forget _)) hw
  have hobj (i : E.I₀) :
      (smallProetaleToBigProetaleFunctor B T S f).obj (E'.X i) = E.X i := by
    apply CostructuredArrow.obj_ext
      ((smallProetaleToBigProetaleFunctor B T S f).obj (E'.X i)) (E.X i) rfl
    show (E.X i).hom = ((E.f i).left ≫ X.obj.hom) ≫ f
    simpa [Category.assoc] using (Over.w (E.f i)).symm
  refine ⟨E'.presieve₀,
    ⟨E', rfl, SmallProetale.isCovering_liftPreZeroHypercover B T hw hE⟩, ?_⟩
  have hmap (i : E.I₀) : (smallProetaleToBigProetaleFunctor B T S f).map (E'.f i) =
      eqToHom (hobj i) ≫ E.f i := by
    apply Over.OverMorphism.ext
    simp [Over.comp_left]
    rfl
  rw [hER]
  exact (map_ofArrows_eq_ofArrows_of_eqToHom _ E'.f E.f hobj hmap).le

/-- Composition from the small pro-étale site of `T` to the big pro-étale
site over `S` is cocontinuous. -/
@[stacks 098P "cocontinuity"]
public instance smallProetaleToBigProetaleFunctor_isCocontinuous :
    (smallProetaleToBigProetaleFunctor B T S f).IsCocontinuous
      (SmallProetale.topology B T.obj T.property)
      (BigProetaleOver.topology B S.obj S.property) := by
  refine ⟨?_⟩
  intro X R hR
  rw [proetaleBigOver_topology_eq] at hR
  obtain ⟨Q, hQ, hQR⟩ :=
    (Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition).mp hR
  obtain ⟨P, hP, hPQ⟩ :=
    smallProetaleToBigProetale_preimage_isCovering B T S f hQ
  apply (SmallProetale.topology B T.obj T.property).superset_covering ?_
    (Precoverage.generate_mem_toGrothendieck hP)
  rw [Sieve.generate_le_iff]
  intro Y g hg
  exact hQR _ _ (hPQ _ _ (Presieve.map_map hg))

/-- Composition also preserves coverings and fibre products, hence is continuous. -/
@[stacks 098P "continuity"]
public instance smallProetaleToBigProetaleFunctor_isContinuous :
    (smallProetaleToBigProetaleFunctor B T S f).IsContinuous
      (SmallProetale.topology B T.obj T.property)
      (BigProetaleOver.topology B S.obj S.property) := by
  let J := SmallProetale.precoverage B T.obj T.property
  let K := B.precoverage.comap
    (Over.forget (⟨S.obj, S.property⟩ : B.Scheme))
  let : J.IsStableUnderBaseChange := smallProetalePrecoverage_stableUnderBaseChange B T
  let : J.HasPullbacks := inferInstance
  let : K.IsStableUnderBaseChange := inferInstance
  let : K.HasPullbacks := inferInstance
  let : PreservesLimitsOfShape WalkingCospan
      (smallProetaleToBigProetaleFunctor B T S f) :=
    smallProetaleToBigProetale_preservesPullbacks B T S f
  have hle : J ≤ K.comap (smallProetaleToBigProetaleFunctor B T S f) := by
    intro X R hR
    change R ∈ SmallProetale.precoverage B T.obj T.property X at hR
    rw [smallProetale_precoverage_eq_comap,
      proetaleBigOver_precoverage_eq_comap] at hR
    simp only [Precoverage.mem_comap_iff] at hR
    change R.map (smallProetaleToBigProetaleFunctor B T S f) ∈
      K ((smallProetaleToBigProetaleFunctor B T S f).obj X)
    rw [Precoverage.mem_comap_iff]
    have hbase :
        smallProetaleToBigProetaleFunctor B T S f ⋙
          Over.forget (⟨S.obj, S.property⟩ : B.Scheme) =
        SmallProetale.inclusion B T.obj T.property ⋙
          Over.forget (⟨T.obj, T.property⟩ : B.Scheme) := by
      dsimp [smallProetaleToBigProetaleFunctor]
      rw [Functor.assoc, Over.mapForget_eq]
    convert hR using 1
    · exact congrArg (fun F => Presieve (F.obj X)) hbase
    · exact congrArg (fun F => Set (Presieve (F.obj X))) hbase
    · have hobj := congrArg (fun F => F.obj X) hbase
      cases hobj
      rfl
    · rw [presieve_map_comp, presieve_map_comp]
      cases hbase
      rfl
  have hcont := Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy
    (smallProetaleToBigProetaleFunctor B T S f) J K hle
  simpa [J, K, SmallProetale.topology, BigProetaleOver.topology,
    BigProetaleSite.topology,
    over_toGrothendieck_eq_toGrothendieck_comap_forget] using hcont

/-- The morphism `i_f : Sh(T_proetale) ⟶ Sh((Sch/S)_proetale)` of topoi. -/
@[stacks 098P "the morphism of topoi"]
public noncomputable def smallProetaleToBigProetaleMorphism :
    MorphismOfTopoi
      (Sheaf (SmallProetale.topology B T.obj T.property) (Type (u + 1)))
      (Sheaf (BigProetaleOver.topology B S.obj S.property) (Type (u + 1))) :=
  { pushforward := (smallProetaleToBigProetaleFunctor B T S f).sheafPushforwardCocontinuous
      (Type (u + 1)) (SmallProetale.topology B T.obj T.property)
      (BigProetaleOver.topology B S.obj S.property)
    inverseImage := (smallProetaleToBigProetaleFunctor B T S f).sheafPullbackCocontinuous
      (Type (u + 1)) (SmallProetale.topology B T.obj T.property)
      (BigProetaleOver.topology B S.obj S.property)
    adj := (smallProetaleToBigProetaleFunctor B T S f).sheafAdjunctionPullbackCocontinuous
      (Type (u + 1)) (SmallProetale.topology B T.obj T.property)
      (BigProetaleOver.topology B S.obj S.property)
    preservesFiniteLimits := by infer_instance }

/-- The left adjoint `i_{f,!}` of inverse image. -/
public noncomputable abbrev smallProetaleToBigProetaleLowerShriek :
    Sheaf (SmallProetale.topology B T.obj T.property) (Type (u + 1)) ⥤
      Sheaf (BigProetaleOver.topology B S.obj S.property) (Type (u + 1)) :=
  (smallProetaleToBigProetaleFunctor B T S f).sheafPullback (Type (u + 1))
    (SmallProetale.topology B T.obj T.property)
    (BigProetaleOver.topology B S.obj S.property)

/-- The lower shriek is left adjoint to inverse image. -/
@[stacks 098P "existence of lower shriek"]
public noncomputable def smallProetaleToBigProetaleLowerShriekAdjunction :
    smallProetaleToBigProetaleLowerShriek B T S f ⊣
      (smallProetaleToBigProetaleMorphism B T S f).inverseImage :=
  (((smallProetaleToBigProetaleFunctor B T S f).sheafAdjunctionLowerShriek
      (Type (u + 1)) (SmallProetale.topology B T.obj T.property)
      (BigProetaleOver.topology B S.obj S.property)).ofNatIsoLeft
        (Functor.sheafPullbackConstruction.sheafPullbackIso
          (smallProetaleToBigProetaleFunctor B T S f) (Type (u + 1))
          (SmallProetale.topology B T.obj T.property)
          (BigProetaleOver.topology B S.obj S.property)).symm).ofNatIsoRight
    ((smallProetaleToBigProetaleFunctor B T S
          f).sheafPullbackCocontinuousIsoSheafPushforwardContinuous
      (Type (u + 1)) (SmallProetale.topology B T.obj T.property)
      (BigProetaleOver.topology B S.obj S.property)).symm

/-- The lower shriek preserves fibre products. -/
@[stacks 098P "lower shriek preserves fibre products"]
public instance smallProetaleToBigProetaleLowerShriek_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan
      (smallProetaleToBigProetaleLowerShriek B T S f) := by
  let : PreservesLimitsOfShape WalkingCospan
      (smallProetaleToBigProetaleFunctor B T S f) :=
    smallProetaleToBigProetale_preservesPullbacks B T S f
  exact Functor.preservesLimitsOfShape_sheafPullback
    (smallProetaleToBigProetaleFunctor B T S f)
    (SmallProetale.topology B T.obj T.property)
    (BigProetaleOver.topology B S.obj S.property) (I := WalkingCospan)

/-- The lower shriek preserves equalizers. -/
@[stacks 098P "lower shriek preserves equalizers"]
public instance smallProetaleToBigProetaleLowerShriek_preservesEqualizers :
    PreservesLimitsOfShape WalkingParallelPair
      (smallProetaleToBigProetaleLowerShriek B T S f) := by
  let : PreservesLimitsOfShape WalkingParallelPair
      (smallProetaleToBigProetaleFunctor B T S f) :=
    smallProetaleToBigProetale_preservesEqualizers B T S f
  exact Functor.preservesLimitsOfShape_sheafPullback
    (smallProetaleToBigProetaleFunctor B T S f)
    (SmallProetale.topology B T.obj T.property)
    (BigProetaleOver.topology B S.obj S.property) (I := WalkingParallelPair)

end AlgebraicGeometry.ProEtale

end
