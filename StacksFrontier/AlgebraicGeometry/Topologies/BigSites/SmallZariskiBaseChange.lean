module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.LeftKanExtensionExactness
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ZariskiPrecoverage
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.CoverPreserving
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.MorphismDefs
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSitesLimits

/-!
# Base change on small Zariski sites

A morphism `f : T ⟶ S` of schemes in a big Zariski site induces a morphism of small Zariski
sites from `T` to `S`, whose underlying continuous functor sends an open subscheme `U` of `S`
to its fibre product `U ×_S T`, an open subscheme of `T`.

## Main definitions

* `AlgebraicGeometry.smallSiteInSchemesOver` — the inclusion of the small Zariski site of `X`
  into the slice category of schemes over `X`.
* `AlgebraicGeometry.smallZariskiBaseChange` — the continuous functor underlying the morphism
  of sites.

## Main results

* `AlgebraicGeometry.exists_smallZariskiBaseChange` — there is a morphism of small Zariski sites
  from `T` to `S` whose functor is base change along `f`, naturally in the open subscheme.
* `AlgebraicGeometry.smallZariskiBaseChange_isMorphismOfSites` — base change is a morphism of
  small Zariski sites.
* `AlgebraicGeometry.smallZariskiBaseChangeIso` — the functor is scheme-theoretic base change,
  naturally in the open subscheme.

## References

* [Stacks Project, Tag 0211](https://stacks.math.columbia.edu/tag/0211)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable (B : BigZariskiSite.{u}) {S T : B.Schemes} (f : T ⟶ S)

/-- The inclusion of the small Zariski site of `X` into the category of schemes over `X`. -/
public abbrev smallSiteInSchemesOver (X : B.Schemes) :
    SmallZariski B X.1 X.property ⥤ Over X.1 :=
  SmallZariski.inclusion B X.1 X.property ⋙
    Over.post B.inclusion

private theorem baseChange_openImmersion (X : SmallZariski B S.1 S.property) :
    IsOpenImmersion (B.inclusion.map ((Over.pullback f).obj X.obj).hom) := by
  show IsOpenImmersion (B.inclusion.map (pullback.snd X.obj.hom f))
  rw [← PreservesPullback.iso_hom_snd B.inclusion X.obj.hom f]
  let : IsOpenImmersion (B.inclusion.map X.obj.hom) := X.property
  infer_instance

private noncomputable def smallZariskiBaseChangeFunctor :
    SmallZariski B S.1 S.property ⥤
      SmallZariski B T.1 T.property where
  obj X := ⟨(Over.pullback f).obj X.obj, baseChange_openImmersion B f X⟩
  map g := ObjectProperty.homMk ((Over.pullback f).map g.hom)
  map_id X := (SmallZariski.inclusion B T.1 T.property).map_injective
    ((Over.pullback f).map_id X.obj)
  map_comp g h := (SmallZariski.inclusion B T.1 T.property).map_injective
    ((Over.pullback f).map_comp g.hom h.hom)

private noncomputable def smallZariskiBaseChangeComparisonApp
    (X : SmallZariski B S.1 S.property) :
    (smallSiteInSchemesOver B T).obj ((smallZariskiBaseChangeFunctor B f).obj X) ≅
      (Over.pullback (B.inclusion.map f)).obj ((smallSiteInSchemesOver B S).obj X) := by
  let e := PreservesPullback.iso B.inclusion X.obj.hom f
  refine Over.isoMk e ?_
  dsimp [smallSiteInSchemesOver, smallZariskiBaseChangeFunctor]
  change e.hom ≫ pullback.snd (B.inclusion.map X.obj.hom) (B.inclusion.map f) =
    B.inclusion.map (pullback.snd X.obj.hom f)
  exact PreservesPullback.iso_hom_snd B.inclusion X.obj.hom f

private theorem pullbackComparison_natural
    {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {X Y S T : C} (a : X ⟶ S) (b : Y ⟶ S) (k : X ⟶ Y) (t : T ⟶ S)
    (hk : k ≫ b = a)
    [HasPullback a t] [HasPullback b t]
    [HasPullback (G.map a) (G.map t)] [HasPullback (G.map b) (G.map t)] :
    G.map (pullback.lift (pullback.fst a t ≫ k) (pullback.snd a t)
      (by rw [Category.assoc, hk, pullback.condition])) ≫
        pullbackComparison G b t =
      pullbackComparison G a t ≫
        pullback.lift (pullback.fst (G.map a) (G.map t) ≫ G.map k)
          (pullback.snd (G.map a) (G.map t)) (by
            calc
              _ = pullback.fst (G.map a) (G.map t) ≫ (G.map k ≫ G.map b) := by
                simp [Category.assoc]
              _ = pullback.fst (G.map a) (G.map t) ≫ G.map (k ≫ b) := by
                rw [Functor.map_comp]
              _ = pullback.fst (G.map a) (G.map t) ≫ G.map a := by rw [hk]
              _ = pullback.snd (G.map a) (G.map t) ≫ G.map t := pullback.condition) := by
  rw [map_lift_pullbackComparison G b t (by
    rw [Category.assoc, hk, pullback.condition])]
  apply pullback.hom_ext
  · calc
      _ = G.map (pullback.fst a t ≫ k) := by
        simp only [pullback.lift_fst]
      _ = (pullbackComparison G a t ≫ pullback.fst (G.map a) (G.map t)) ≫ G.map k := by
        rw [pullbackComparison_comp_fst, ← Functor.map_comp]
      _ = _ := by
        simp only [Category.assoc, pullback.lift_fst]
  · calc
      _ = G.map (pullback.snd a t) := by
        simp only [pullback.lift_snd]
      _ = _ := by
        simp only [Category.assoc, pullback.lift_snd]
        rw [pullbackComparison_comp_snd]

private noncomputable def smallZariskiBaseChangeComparison :
    smallZariskiBaseChangeFunctor B f ⋙ smallSiteInSchemesOver B T ≅
      smallSiteInSchemesOver B S ⋙ Over.pullback (B.inclusion.map f) := by
  refine NatIso.ofComponents (smallZariskiBaseChangeComparisonApp B f) (by
    intro X Y g
    let : IsOpenImmersion ((smallSiteInSchemesOver B S).obj Y).hom := Y.property
    let : IsOpenImmersion
        ((Over.pullback (B.inclusion.map f)).obj
          ((smallSiteInSchemesOver B S).obj Y)).hom := by
      change IsOpenImmersion (pullback.snd
        ((smallSiteInSchemesOver B S).obj Y).hom (B.inclusion.map f))
      infer_instance
    apply Over.OverMorphism.ext
    dsimp [smallZariskiBaseChangeComparisonApp, smallZariskiBaseChangeFunctor,
      smallSiteInSchemesOver]
    exact pullbackComparison_natural B.inclusion X.obj.hom Y.obj.hom g.hom.left f
      g.hom.w)

private lemma isCovering_of_isPullback
    {X Y : B.Schemes} (E : PreZeroHypercover.{u + 1} X)
    (hE : B.IsCovering ⟨X, E⟩) (g : Y ⟶ X)
    (P : E.I₀ → B.Schemes) (p₁ : ∀ i, P i ⟶ Y) (p₂ : ∀ i, P i ⟶ E.X i)
    (h : ∀ i, IsPullback (p₁ i) (p₂ i) g (E.f i)) :
    B.IsCovering ⟨Y, ⟨E.I₀, P, p₁⟩⟩ := by
  let := preservesPullbacks_bigZariskiSiteInclusion B
  let : (Scheme.zariskiPrecoverage : Precoverage Scheme.{u}).IsStableUnderBaseChange :=
    Scheme.zariskiPrecoverage_isStableUnderBaseChange
  refine ⟨?_, hE.2⟩
  show (PreZeroHypercover.mk E.I₀ P p₁ |>.map B.inclusion).presieve₀ ∈
    Scheme.zariskiPrecoverage (B.inclusion.obj Y)
  let : (Scheme.zariskiPretopology.toPrecoverage).IsStableUnderBaseChange :=
    Scheme.zariskiPrecoverage_isStableUnderBaseChange.{u}
  apply Precoverage.mem_coverings_of_isPullback
    (f := fun i => B.inclusion.map (E.f i))
    (hR := hE.1) (g := B.inclusion.map g)
    (p₁ := fun i => B.inclusion.map (p₁ i))
    (p₂ := fun i => B.inclusion.map (p₂ i))
  exact fun i => (h i).map B.inclusion

private lemma isCovering_overPullback
    {S T : B.Schemes} (f : T ⟶ S) {X : Over S}
    (E : PreZeroHypercover.{u + 1} X)
    (hE : B.IsCovering ⟨X.left, E.map (Over.forget S)⟩) :
    B.IsCovering ⟨((Over.pullback f).obj X).left,
      (E.map (Over.pullback f)).map (Over.forget T)⟩ := by
  let := hasPullbacks_bigZariskiSite B
  apply isCovering_of_isPullback B (E.map (Over.forget S)) hE
    (pullback.fst X.hom f)
    (fun i => ((Over.pullback f).obj (E.X i)).left)
    (fun i => ((Over.pullback f).map (E.f i)).left)
    (fun i => pullback.fst (E.X i).hom f)
  intro i
  show IsPullback
    (pullback.lift (pullback.fst (E.X i).hom f ≫ (E.f i).left)
      (pullback.snd (E.X i).hom f) _)
    (pullback.fst (E.X i).hom f) (pullback.fst X.hom f) (E.f i).left
  exact baseChange_square (E.f i).left X.hom (E.X i).hom f (Over.w (E.f i))

/-- Base change on small sites is compatible with the inclusions into schemes over `S` and `T`. -/
private noncomputable def smallZariskiBaseChangeInclusionIso :
    SmallZariski.inclusion B S.1 S.property ⋙ Over.pullback f ≅
      smallZariskiBaseChangeFunctor B f ⋙ SmallZariski.inclusion B T.1 T.property :=
  eqToIso (CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => rfl))

private lemma preservesPullbacks_baseChange :
    PreservesLimitsOfShape WalkingCospan (smallZariskiBaseChangeFunctor B f) := by
  let := hasPullbacks_bigZariskiSite B
  let := preservesPullbacks_smallZariskiInclusion B S.1 S.property
  have : PreservesLimitsOfShape WalkingCospan
      (SmallZariski.inclusion B S.1 S.property ⋙ Over.pullback f) := inferInstance
  let := preservesLimitsOfShape_of_natIso (J := WalkingCospan)
    (smallZariskiBaseChangeInclusionIso B f)
  exact preservesLimitsOfShape_of_reflects_of_preserves
    (smallZariskiBaseChangeFunctor B f)
    (SmallZariski.inclusion B T.1 T.property)

private lemma preservesTerminal_baseChange :
    PreservesLimit (Functor.empty.{0}
      (SmallZariski B S.1 S.property))
      (smallZariskiBaseChangeFunctor B f) := by
  let := hasPullbacks_bigZariskiSite B
  let := preservesTerminal_smallZariskiInclusion B S.1 S.property
  have : PreservesLimit (Functor.empty.{0}
      (SmallZariski B S.1 S.property))
      (SmallZariski.inclusion B S.1 S.property ⋙ Over.pullback f) := inferInstance
  let := preservesLimit_of_natIso
    (Functor.empty.{0} (SmallZariski B S.1 S.property))
    (smallZariskiBaseChangeInclusionIso B f)
  exact preservesLimit_of_reflects_of_preserves
    (smallZariskiBaseChangeFunctor B f)
    (SmallZariski.inclusion B T.1 T.property)

private lemma coverPreserving_baseChange :
    CoverPreserving
      (SmallZariski.topology B S.1 S.property)
      (SmallZariski.topology B T.1 T.property)
      (smallZariskiBaseChangeFunctor B f) := by
  let := hasPullbacks_smallZariski B S.1 S.property
  let := preservesPullbacks_baseChange B f
  apply coverPreserving_of_generators
    (smallZariskiBaseChangeFunctor B f)
    (SmallZariski.precoverage B S.1 S.property)
    (SmallZariski.topology B T.1 T.property)
  intro X R hR
  obtain ⟨E, rfl, hE⟩ :=
    (SmallZariski.mem_precoverage_iff B S.1 S.property).1 hR
  rw [← PreZeroHypercover.sieve₀_map]
  apply Precoverage.generate_mem_toGrothendieck
  apply (SmallZariski.mem_precoverage_iff B T.1 T.property).2
  refine ⟨E.map (smallZariskiBaseChangeFunctor B f), rfl, ?_⟩
  exact isCovering_overPullback B f
    (E.map (SmallZariski.inclusion B S.1 S.property)) hE

private lemma representablyFlat_baseChange :
    RepresentablyFlat (smallZariskiBaseChangeFunctor B f) := by
  let := hasPullbacks_smallZariski B S.1 S.property
  let := hasTerminal_smallZariski B S.1 S.property
  let : HasFiniteLimits (SmallZariski B S.1 S.property) :=
    hasFiniteLimits_of_hasTerminal_and_pullbacks
  let := preservesPullbacks_baseChange B f
  let := preservesTerminal_baseChange B f
  let : PreservesLimitsOfShape (Discrete PEmpty.{1})
      (smallZariskiBaseChangeFunctor B f) :=
    preservesLimitsOfShape_pempty_of_preservesTerminal _
  let : PreservesFiniteLimits (smallZariskiBaseChangeFunctor B f) :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks _
  exact flat_of_preservesFiniteLimits _

private theorem smallZariskiBaseChange_isContinuous :
    Functor.IsContinuous (smallZariskiBaseChangeFunctor B f)
      (SmallZariski.topology B S.1 S.property)
      (SmallZariski.topology B T.1 T.property) := by
  let := representablyFlat_baseChange B f
  exact Functor.isContinuous_iff_coverPreserving.2
    (coverPreserving_baseChange B f)

private theorem smallZariskiBaseChangeFunctor_sheafPullback_preservesFiniteLimits
    (f : T ⟶ S)
    [Functor.IsContinuous (smallZariskiBaseChangeFunctor B f)
      (SmallZariski.topology B S.1 S.property)
      (SmallZariski.topology B T.1 T.property)] :
    PreservesFiniteLimits
      ((smallZariskiBaseChangeFunctor B f).sheafPullback (Type (u + 1))
        (SmallZariski.topology B S.1 S.property)
        (SmallZariski.topology B T.1 T.property)) := by
  let := representablyFlat_baseChange B f
  let : PreservesFiniteLimits
      ((smallZariskiBaseChangeFunctor B f).op.lan :
        (_ ⥤ Type (u + 1)) ⥤ _ ⥤ Type (u + 1)) :=
    CategoryTheory.lan_preservesFiniteLimits_of_representablyFlat.{u, u, u + 1, u + 1, u + 1}
      (smallZariskiBaseChangeFunctor B f)
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits
    (smallZariskiBaseChangeFunctor B f) (Type (u + 1)) _ _

/-- There is a morphism of small Zariski sites from `T` to `S` whose underlying functor, after
including both small sites into schemes over `T` and `S`, is naturally isomorphic to base change
along `f`. -/
@[stacks 0211 "f_small"]
public theorem exists_smallZariskiBaseChange :
    ∃ F : SmallZariski B S.1 S.property ⥤
        SmallZariski B T.1 T.property,
      _root_.IsMorphismOfSites.{u + 1} F
        (SmallZariski.topology B S.1 S.property)
        (SmallZariski.topology B T.1 T.property) ∧
      Nonempty (F ⋙ smallSiteInSchemesOver B T ≅
        smallSiteInSchemesOver B S ⋙ Over.pullback (B.inclusion.map f)) := by
  refine ⟨smallZariskiBaseChangeFunctor B f, ?_, ⟨smallZariskiBaseChangeComparison B f⟩⟩
  have := smallZariskiBaseChange_isContinuous B f
  exact ⟨(smallZariskiBaseChangeFunctor B f).sheafPullback (Type (u + 1))
    (SmallZariski.topology B S.1 S.property)
    (SmallZariski.topology B T.1 T.property),
    ⟨(smallZariskiBaseChangeFunctor B f).sheafAdjunctionContinuous (Type (u + 1))
      (SmallZariski.topology B S.1 S.property)
      (SmallZariski.topology B T.1 T.property)⟩,
    smallZariskiBaseChangeFunctor_sheafPullback_preservesFiniteLimits B f⟩

/-- The continuous base-change functor on small Zariski sites. -/
@[stacks 0211 "f_small", implicit_reducible]
public noncomputable def smallZariskiBaseChange :
    SmallZariski B S.1 S.property ⥤
      SmallZariski B T.1 T.property :=
  Classical.choose (exists_smallZariskiBaseChange B f)

/-- After inclusion into schemes over `T` and `S`, the functor `smallZariskiBaseChange B f` is
naturally isomorphic to base change along `f`. -/
@[implicit_reducible]
public noncomputable def smallZariskiBaseChangeIso :
    smallZariskiBaseChange B f ⋙ smallSiteInSchemesOver B T ≅
      smallSiteInSchemesOver B S ⋙ Over.pullback (B.inclusion.map f) :=
  Classical.choice (Classical.choose_spec (exists_smallZariskiBaseChange B f)).2

/-- Base change defines a morphism of small Zariski sites. -/
public instance smallZariskiBaseChange_isMorphismOfSites :
    _root_.IsMorphismOfSites.{u + 1} (smallZariskiBaseChange B f)
      (SmallZariski.topology B S.1 S.property)
      (SmallZariski.topology B T.1 T.property) :=
  (Classical.choose_spec (exists_smallZariskiBaseChange B f)).1

end AlgebraicGeometry
