module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianLocalFactorization
public import StacksFrontier.AlgebraicGeometry.Stacks.ParasiticLisseEtaleVanishing
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStackTerminalSubsite
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineCover
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineSiteCartesianModules
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.QuasiCoherentModulesAndAffines
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsitePushforwardAmbientNaturality
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteModuleShriekBaseChange

/-!
# Flat base change between flat objects of an algebraic stack, along every arrow

Let `𝒳` be an algebraic stack and let `F` be a presheaf of `O_𝒳`-modules on `𝒳` which is
cartesian along every arrow between affine objects lying over a flat morphism of schemes: for
such an arrow `φ : z ⟶ x` the comparison `O(z) ⊗_{O(x)} F(x) ⟶ F(z)` is bijective. This file
proves that `F` is then cartesian along *every* arrow `f : y ⟶ y'` between *flat* objects of
`𝒳` lying over affine schemes, whether or not the morphism of schemes under `f` is flat.

## The argument

The 2-fibre product `P = Y' ×_{y', 𝒳} (Sch/Y)` of the 1-morphisms named by `y'` and by `y` is an
algebraic stack whose two projections are flat, because `y` and `y'` are flat objects. The arrow
`f` gives an object `γ` of `P` over `Y`, the graph of `f`. Pick a smooth surjective atlas
`U₀ → P`; by **Stacks 06XH** the object `γ` is covered by an arrow out of the image of an object of
`(Sch/U₀)`, which maps to the distinguished object `d₀` of the atlas; and `d₀` is covered by its
restrictions to affine opens of `U₀`. Each such restriction `d` gives an object `w` of `𝒳` over an
affine scheme with arrows `a : w ⟶ y` and `b : w ⟶ y'` over flat morphisms of schemes. So `y` is
covered by arrows `q : v ⟶ y` for which there are `c : v ⟶ w` with `c ≫ a = q` and
`c ≫ b = q ≫ f`.

On the affine site of `𝒳` this covering contains a finite flat covering of `y`, and
`Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_factorizations` concludes.

## Main results

* `AlgebraicGeometry.Stack.exists_affine_openImmersion_cover`: every object of a category
  fibred in groupoids over the big fppf site is covered by lifts of affine open immersions.
* `AlgebraicGeometry.Stack.factorizationSieve_mem`: the covering of `y` above.
* `AlgebraicGeometry.Stack.isIso_restrictionBaseChange_of_flatObject`: the conclusion.
* `AlgebraicGeometry.Stack.FlatFppf.isIso_restrictionBaseChange_modulePullback`: the conclusion
  read on the flat-fppf site, for the pullback `g^{-1}M` of **Stacks 0788** (2) of a sheaf of
  modules on `𝒳_fppf`.

## References

* [Stacks Project, Tag 06XH](https://stacks.math.columbia.edu/tag/06XH)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
* [Stacks Project, Tag 07B1](https://stacks.math.columbia.edu/tag/07B1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section AffineCover

variable {𝒞 : Type v} [Category.{w} 𝒞] (p : 𝒞 ⥤ BigFppfOver B S hS)

/-- **Every object is covered by lifts of affine open immersions.** For an object `x` of a
category fibred in groupoids over the big fppf category of schemes over `S`, an affine open cover
of the scheme under `x` lifts to a covering family of `x` for the inherited fppf topology, whose
members lie over affine schemes and over open immersions. -/
theorem exists_affine_openImmersion_cover (hp : p.IsFiberedInGroupoids) (x : 𝒞) :
    ∃ (I : Type (u + 1)) (y : I → 𝒞) (φ : ∀ i, y i ⟶ x),
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj (y i)))) ∧
      (∀ i, AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (p.map (φ i)))) ∧
      Sieve.ofArrows y φ ∈ BigFppfOver.associatedTopology B S hS p .fppf x := by
  classical
  obtain ⟨V, hV, hVU⟩ := exists_isCovering_tautologicallyEquivalent_openCover B
    (p.obj x).left (B.inclusion.obj (p.obj x).left).affineOpenCover.openCover
  obtain ⟨-, β, hβ⟩ := hVU
  have hVaff : ∀ j, IsAffine (B.inclusion.obj (V.X j)) := fun j => by
    obtain ⟨e, -⟩ := hβ j
    have : IsAffine (Spec ((B.inclusion.obj (p.obj x).left).affineOpenCover.X (β j))) :=
      isAffine_Spec _
    exact @IsAffine.of_isIso _ _ e.hom e.isIso_hom this
  have hVopen : ∀ j, AlgebraicGeometry.IsOpenImmersion (B.inclusion.map (V.f j)) := by
    intro j
    obtain ⟨e, he⟩ := hβ j
    change AlgebraicGeometry.IsOpenImmersion ((V.map B.inclusion).f j)
    rw [← he]
    infer_instance
  let Vobj (j : V.I₀) : BigFppfOver B S hS := Over.mk (V.f j ≫ (p.obj x).hom)
  let vmap (j : V.I₀) : Vobj j ⟶ p.obj x := Over.homMk (V.f j)
  have hBcover : Sieve.ofArrows Vobj vmap ∈
      BigFppfOver.baseOverTopology B S hS .fppf (p.obj x) := by
    change Sieve.ofArrows Vobj vmap ∈ (B.topology.over (B.obj hS)) (p.obj x)
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    change Sieve.ofArrows V.X V.f ∈ B.topology (p.obj x).left
    have hpre : V.presieve₀ ∈ B.precoverage (p.obj x).left := ⟨V, rfl, hV⟩
    simpa [PreZeroHypercover.presieve₀] using Precoverage.generate_mem_toGrothendieck hpre
  choose y φ hφ using fun j => hp.exists_lift (vmap j) x rfl
  have hdom : ∀ j, p.obj (y j) = Vobj j := fun j => by
    have := hφ j
    exact IsHomLift.domain_eq p (vmap j) (φ j)
  have hfac : ∀ j, p.map (φ j) = eqToHom (hdom j) ≫ vmap j := fun j => by
    have := hφ j
    rw [IsHomLift.fac p (vmap j) (φ j)]
    simp
  have hvmapmem : ∀ j, (Sieve.ofArrows (fun k => p.obj (y k)) fun k => p.map (φ k)) (vmap j) := by
    intro j
    refine (Sieve.mem_ofArrows_iff _ _ _).2 ⟨j, eqToHom (hdom j).symm, ?_⟩
    rw [hfac j]
    simp
  have hfib : p.IsFibered := hp.isFibered
  refine ⟨V.I₀, y, φ, fun j => ?_, fun j => ?_, ?_⟩
  · rw [hdom j]
    exact hVaff j
  · rw [hfac j, Functor.map_comp]
    have : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (vmap j)) :=
      hVopen j
    infer_instance
  · refine (Functor.isInheritedTopology_inheritedTopology p
      (BigFppfOver.baseOverTopology B S hS .fppf) y φ
      (fun j => hp.isStronglyCartesian (φ j))).2 ?_
    refine (BigFppfOver.baseOverTopology B S hS .fppf).superset_covering ?_ hBcover
    intro Z g hg
    obtain ⟨j, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg
    exact (Sieve.ofArrows (fun k => p.obj (y k)) fun k => p.map (φ k)).downward_closed
      (hvmapmem j) a

end AffineCover

section Graph

variable (𝒳 : AlgebraicStacks.{u, w} B S hS) (y : 𝒳.val.val.obj) (y' : FlatFppf B S hS 𝒳)

/-- The 1-morphism `(Sch/Y) ⟶ 𝒳` named by an object `y` of `𝒳` over `Y`. -/
noncomputable abbrev chart : schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y) ⟶ 𝒳 :=
  Bicategory.InducedBicategory.mkHom
    (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := y) rfl))

/-- The chart named by `y` sends the final object `id_Y` to an object isomorphic to `y`. -/
noncomputable def chartIso :
    (chart B S hS 𝒳 y).hom.hom.toFunctor.obj (Over.mk (𝟙 (𝒳.val.val.p.obj y))) ≅ y :=
  Functor.Fiber.fiberInclusion.mapIso
    (Functor.TwoYoneda.liftBasedEvaluationIso 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids _
      (Functor.Fiber.mk (a := y) rfl))

/-- The comparison `chartIso` lies over the identity. -/
instance isHomLift_chartIso_hom :
    𝒳.val.val.p.IsHomLift (𝟙 (𝒳.val.val.p.obj y)) (chartIso B S hS 𝒳 y).hom :=
  (Functor.TwoYoneda.liftBasedEvaluationIso 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids _
    (Functor.Fiber.mk (a := y) rfl)).hom.2

/-- The objects of the 2-fibre product `Y' ×_{y', 𝒳} (Sch/Y)` of the charts named by `y'` and
by `y`. -/
abbrev GraphObj : Type (u + 1) :=
  CategoryTheory.SubsitePushforward.ambientTwoFibreProduct
    (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y)).val.val.p
    𝒳.val.val.p (chart B S hS 𝒳 y).hom.hom.toFunctor (ambientChoiceOfPullbacks B S hS 𝒳) y'

/-- The image in `𝒳` of an object of the 2-fibre product, through its `(Sch/Y)`-component. -/
abbrev graphPt (d : GraphObj B S hS 𝒳 y y') : 𝒳.val.val.obj :=
  (chart B S hS 𝒳 y).hom.hom.toFunctor.obj d.y

/-- The arrow to `y` out of the image of an object of the 2-fibre product. -/
noncomputable def graphFst (d : GraphObj B S hS 𝒳 y y') : graphPt B S hS 𝒳 y y' d ⟶ y :=
  (chart B S hS 𝒳 y).hom.hom.toFunctor.map
      (Over.homMk d.y.hom (Category.comp_id _) : d.y ⟶ Over.mk (𝟙 _)) ≫
    (chartIso B S hS 𝒳 y).hom

/-- The arrow to `y'` out of the image of an object of the 2-fibre product: the comparison
isomorphism of the object followed by the chosen cartesian lift of `y'`. -/
noncomputable def graphSnd (d : GraphObj B S hS 𝒳 y y') : graphPt B S hS 𝒳 y y' d ⟶ y'.obj :=
  d.iso.inv ≫ (ambientChoiceOfPullbacks B S hS 𝒳).map d.x.hom ⟨y'.obj, rfl⟩

variable {B S hS 𝒳 y y'}

/-- `graphFst` is natural. -/
theorem graphFst_naturality {d₁ d₂ : GraphObj B S hS 𝒳 y y'} (h : d₁ ⟶ d₂) :
    (chart B S hS 𝒳 y).hom.hom.toFunctor.map h.b ≫ graphFst B S hS 𝒳 y y' d₂ =
      graphFst B S hS 𝒳 y y' d₁ := by
  have hb : h.b ≫ (Over.homMk d₂.y.hom (Category.comp_id _) : d₂.y ⟶ Over.mk (𝟙 _)) =
      (Over.homMk d₁.y.hom (Category.comp_id _) : d₁.y ⟶ Over.mk (𝟙 _)) :=
    Over.mkIdTerminal.hom_ext _ _
  unfold graphFst
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (chartIso B S hS 𝒳 y).hom)
    (((chart B S hS 𝒳 y).hom.hom.toFunctor.map_comp _ _).symm.trans (congrArg _ hb)))

/-- `graphSnd` is natural. -/
theorem graphSnd_naturality {d₁ d₂ : GraphObj B S hS 𝒳 y y'} (h : d₁ ⟶ d₂) :
    (chart B S hS 𝒳 y).hom.hom.toFunctor.map h.b ≫ graphSnd B S hS 𝒳 y y' d₂ =
      graphSnd B S hS 𝒳 y y' d₁ := by
  have hw : (chart B S hS 𝒳 y).hom.hom.toFunctor.map h.b ≫ d₂.iso.inv =
      d₁.iso.inv ≫ ((ambientChoiceOfPullbacks B S hS 𝒳).sliceFunctor ⟨y'.obj, rfl⟩).map h.a := by
    refine (cancel_epi d₁.iso.hom).1 ?_
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← h.w, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  unfold graphSnd
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hw).trans
    ((Category.assoc _ _ _).trans (congrArg (d₁.iso.inv ≫ ·)
      (Functor.ChoiceOfPullbacks.sliceFunctor_map_fac _ _ h.a))))

/-- `graphFst` lies over the structure morphism of the `(Sch/Y)`-component. -/
theorem isHomLift_graphFst (d : GraphObj B S hS 𝒳 y y') :
    𝒳.val.val.p.IsHomLift d.y.hom (graphFst B S hS 𝒳 y y' d) := by
  have h0 := isHomLift_map_toUnit.{u, w} (a := chart B S hS 𝒳 y) d.y
  unfold graphFst
  exact IsHomLift.comp_lift_id_right 𝒳.val.val.p d.y.hom _ _

/-- `graphSnd` lies over the structure morphism of the `Y'`-component. -/
theorem isHomLift_graphSnd (d : GraphObj B S hS 𝒳 y y') :
    𝒳.val.val.p.IsHomLift d.x.hom (graphSnd B S hS 𝒳 y y' d) :=
  isHomLift_ambientArrow _ 𝒳.val.val.p _ (ambientChoiceOfPullbacks B S hS 𝒳) y' d

end Graph


section Flat

variable {𝒞 : Type v} [Category.{w} 𝒞] (p : 𝒞 ⥤ BigFppfOver B S hS)

/-- An arrow lying over a flat morphism of schemes has a flat morphism of schemes under it. -/
theorem flat_toScheme_map_of_isHomLift {U V : BigFppfOver B S hS} {k : U ⟶ V} {a b : 𝒞}
    (φ : a ⟶ b) (hφ : p.IsHomLift k φ) (hk : Flat ((BigFppfOver.toScheme B S hS).map k)) :
    Flat ((BigFppfOver.toScheme B S hS).map (p.map φ)) := by
  have := hφ
  rw [IsHomLift.fac' p k φ]
  simp only [Functor.map_comp, eqToHom_map]
  infer_instance

/-- The structure map of an object of an over category is flat if that of its target and the
underlying arrow of a morphism to it are. -/
private theorem flat_hom_of_flat_comp {X : BigFppfOver B S hS} {u v : Over X} (g : u ⟶ v)
    (hg : Flat ((BigFppfOver.toScheme B S hS).map ((Over.forget X).map g)))
    (hv : Flat ((BigFppfOver.toScheme B S hS).map v.hom)) :
    Flat ((BigFppfOver.toScheme B S hS).map u.hom) := by
  rw [← Over.w g, Functor.map_comp]
  exact @Flat.comp _ _ _ _ _ hg hv

end Flat

section Cover

variable {𝒳 : AlgebraicStacks.{u, w} B S hS}

/-- **The sieve of local factorizations of an arrow through flat arrows.** For an arrow
`f : y ⟶ y'` of `𝒳`, the arrows `q : v ⟶ y` for which there are an object `w` over an affine
scheme, arrows `a : w ⟶ y` and `b : w ⟶ y'` over flat morphisms of schemes, and `c : v ⟶ w`
with `c ≫ a = q` and `c ≫ b = q ≫ f`. -/
def factorizationSieve {y y' : 𝒳.val.val.obj} (f : y ⟶ y') : Sieve y where
  arrows {v} q := ∃ (w : 𝒳.val.val.obj) (c : v ⟶ w) (a : w ⟶ y) (b : w ⟶ y'),
    IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj w)) ∧
    Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map a)) ∧
    Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map b)) ∧
    c ≫ a = q ∧ c ≫ b = q ≫ f
  downward_closed := by
    rintro _ _ q ⟨w, c, a, b, h₁, h₂, h₃, h₄, h₅⟩ g
    exact ⟨w, g ≫ c, a, b, h₁, h₂, h₃, by rw [Category.assoc, h₄],
      by rw [Category.assoc, h₅, Category.assoc]⟩

variable {y : 𝒳.val.val.obj} {y' : FlatFppf B S hS 𝒳}

/-- **The graph of an arrow** `f : y ⟶ y'`, as an object of the 2-fibre product
`Y' ×_{y', 𝒳} (Sch/Y)` over `Y`: its `(Sch/Y)`-component is `id_Y`, and its comparison arrow is
`f` itself, read through the chart named by `y`. -/
noncomputable def graphPoint (f : y ⟶ y'.obj) : GraphObj B S hS 𝒳 y y' :=
  ((CategoryTheory.SubsitePushforward.primedProperty _ _ _ (FlatFppf.objectProperty B S hS
      (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y))) _ y').ι.obj
    (CategoryTheory.SubsitePushforward.primedObjOfHom
      (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y)).val.val.p
      𝒳.val.val.p (chart B S hS 𝒳 y).hom.hom.toFunctor
      (FlatFppf.objectProperty B S hS (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y)))
      (ambientChoiceOfPullbacks B S hS 𝒳) 𝒳.val.isFiberedInGroupoids
      (chart B S hS 𝒳 y).hom.hom.w y'
      ⟨Over.mk (𝟙 _), flatObject_schemeStack_id.{u, w} B S hS _⟩
      ((chartIso B S hS 𝒳 y).hom ≫ f)))

/-- The arrow to `y'` out of the graph of `f` is `f`. -/
theorem graphSnd_graphPoint (f : y ⟶ y'.obj) :
    graphSnd B S hS 𝒳 y y' (graphPoint B S hS f) = (chartIso B S hS 𝒳 y).hom ≫ f :=
  CategoryTheory.SubsitePushforward.primedObjOfHom_comparison _ _ _ _ _ _ _ y' _ _

/-- The arrow to `y` out of the graph of `f` is the comparison of the chart. -/
theorem graphFst_graphPoint (f : y ⟶ y'.obj) :
    graphFst B S hS 𝒳 y y' (graphPoint B S hS f) = (chartIso B S hS 𝒳 y).hom := by
  unfold graphFst
  have h : (Over.homMk (graphPoint B S hS f).y.hom (Category.comp_id _) :
      (graphPoint B S hS f).y ⟶ Over.mk (𝟙 _)) = 𝟙 _ := Over.mkIdTerminal.hom_ext _ _
  rw [h]
  exact (congrArg (· ≫ (chartIso B S hS 𝒳 y).hom)
    ((chart B S hS 𝒳 y).hom.hom.toFunctor.map_id _)).trans (Category.id_comp _)

/-- An object of the 2-fibre product over an affine scheme whose two components lie over flat
morphisms of schemes. -/
def IsGoodGraphObj (d : GraphObj B S hS 𝒳 y y') : Prop :=
  IsAffine ((BigFppfOver.toScheme B S hS).obj d.base) ∧
    Flat ((BigFppfOver.toScheme B S hS).map d.x.hom) ∧
    Flat ((BigFppfOver.toScheme B S hS).map d.y.hom)

/-- **The graph of `f` is covered by arrows into good objects of the 2-fibre product.** -/
theorem goodSieve_mem (hy : flatObject B S hS 𝒳.val y) (f : y ⟶ y'.obj) :
    ({ arrows := fun {ζ} _ => ∃ ω : GraphObj B S hS 𝒳 y y', IsGoodGraphObj B S hS ω ∧
          Nonempty (ζ ⟶ ω)
       downward_closed := fun {_ _} _ ⟨ω, hω, ⟨t⟩⟩ g => ⟨ω, hω, ⟨g ≫ t⟩⟩ } :
        Sieve (graphPoint B S hS f)) ∈
      BigFppfOver.associatedTopology B S hS
        (ambientSquare B S hS (chart B S hS 𝒳 y) y').pt.val.val.p .fppf
        (graphPoint B S hS f) := by
  let P := ambientSquare B S hS (chart B S hS 𝒳 y) y'
  have hfz : AlgebraicStacks.IsFlat B S hS (chart B S hS 𝒳 y) :=
    (AlgebraicStacks.isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS _).2 hy
  have hfst : AlgebraicStacks.IsFlat B S hS P.fst :=
    AlgebraicStacks.isFlat_baseChange B S hS (chart B S hS 𝒳 y) (ambientSliceMorphism B S hS y')
      P (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS
        (ambientSliceMorphism B S hS y') (chart B S hS 𝒳 y)) hfz
  have hsnd : AlgebraicStacks.IsFlat B S hS P.snd :=
    FlatFppf.isFlat_ambientSquare_snd B S hS (chart B S hS 𝒳 y) y'
  obtain ⟨U₀, a₀, hsm, hsurj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS P.pt
  obtain ⟨x'', α, hgen⟩ := exists_etaleLocalLift B S hS a₀ hsurj hsm (graphPoint B S hS f)
  let s₀ : GraphObj B S hS 𝒳 y y' := a₀.hom.hom.toFunctor.obj (Over.mk (𝟙 U₀))
  have hs₀ : flatObject B S hS P.pt.val s₀ :=
    FlatFppf.flatObject_map B S hS a₀ (AlgebraicStacks.isFlat_of_isSmooth B S hS a₀ hsm)
      ⟨Over.mk (𝟙 U₀), flatObject_schemeStack_id.{u, w} B S hS U₀⟩
  have hs₀x : Flat ((BigFppfOver.toScheme B S hS).map s₀.x.hom) :=
    (flatObject_schemeStack_iff.{u, w} B S hS _ s₀.x).1
      (FlatFppf.flatObject_map B S hS P.fst hfst ⟨s₀, hs₀⟩)
  have hs₀y : Flat ((BigFppfOver.toScheme B S hS).map s₀.y.hom) :=
    (flatObject_schemeStack_iff.{u, w} B S hS _ s₀.y).1
      (FlatFppf.flatObject_map B S hS P.snd hsnd ⟨s₀, hs₀⟩)
  refine (BigFppfOver.associatedTopology B S hS P.pt.val.val.p .fppf).transitive
    (BigFppfOver.associatedTopology_le_fppf B S hS P.pt.val.val.p .etale _ hgen) _ ?_
  rintro ζ g ⟨Y, m, k, hk, rfl⟩
  cases hk
  obtain ⟨I, ω, ψ, haff, hopen, hcov⟩ := exists_affine_openImmersion_cover B S hS
    P.pt.val.val.p P.pt.val.isFiberedInGroupoids s₀
  let r : ζ ⟶ s₀ := m ≫ a₀.hom.hom.toFunctor.map
    (Over.homMk x''.hom (Category.comp_id _) : x'' ⟶ Over.mk (𝟙 U₀))
  refine (BigFppfOver.associatedTopology B S hS P.pt.val.val.p .fppf).superset_covering ?_
    ((BigFppfOver.associatedTopology B S hS P.pt.val.val.p .fppf).pullback_stable r hcov)
  intro Z t ht
  obtain ⟨j, e, -⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp ht
  have hb : Flat ((BigFppfOver.toScheme B S hS).map (ψ j).hbase) := by
    have := hopen j
    exact inferInstanceAs (Flat ((BigFppfOver.toScheme B S hS).map
      (P.pt.val.val.p.map (ψ j))))
  refine ⟨ω j, ⟨haff j, ?_, ?_⟩, ⟨e⟩⟩
  · exact flat_hom_of_flat_comp B S hS (ψ j).a
      (flat_toScheme_map_of_isHomLift B S hS (Over.forget _) _ (ψ j).ha hb) hs₀x
  · exact flat_hom_of_flat_comp B S hS (ψ j).b
      (flat_toScheme_map_of_isHomLift B S hS (Over.forget _) _ (ψ j).hb hb) hs₀y

/-- **An arrow between flat objects factors locally through pairs of flat arrows.** For flat
objects `y`, `y'` of an algebraic stack `𝒳` and an arrow `f : y ⟶ y'`, the sieve
`AlgebraicGeometry.Stack.factorizationSieve` of `f` covers `y` for the fppf topology. -/
theorem factorizationSieve_mem (hy : flatObject B S hS 𝒳.val y) (f : y ⟶ y'.obj) :
    factorizationSieve B S hS f ∈ BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf y := by
  let P := ambientSquare B S hS (chart B S hS 𝒳 y) y'
  let π : P.pt ⟶ 𝒳 := P.snd ≫ chart B S hS 𝒳 y
  have hcont := (isContinuous_and_isCocontinuous_homFunctor_associatedTopology B S hS π
    B.topology).1
  have hpush := (CoverPreserving.of_isContinuous π.hom.hom.toFunctor
    (associatedTopology B S hS P.pt.val.val.p B.topology)
    (associatedTopology B S hS 𝒳.val.val.p B.topology)).cover_preserve (goodSieve_mem B S hS hy f)
  let e := chartIso B S hS 𝒳 y
  have hT : (factorizationSieve B S hS f).pullback e.hom ∈
      BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf
        (graphPt B S hS 𝒳 y y' (graphPoint B S hS f)) := by
    refine (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf).superset_covering ?_ hpush
    rintro Z k ⟨ζ, h, l, ⟨ω, hω, ⟨c'⟩⟩, rfl⟩
    refine ⟨graphPt B S hS 𝒳 y y' ω, l ≫ (chart B S hS 𝒳 y).hom.hom.toFunctor.map c'.b,
      graphFst B S hS 𝒳 y y' ω, graphSnd B S hS 𝒳 y y' ω, ?_, ?_, ?_, ?_, ?_⟩
    · have hb : 𝒳.val.val.p.obj (graphPt B S hS 𝒳 y y' ω) = ω.base :=
        (Functor.congr_obj (chart B S hS 𝒳 y).hom.hom.w ω.y).trans ω.hy
      rw [hb]
      exact hω.1
    · exact flat_toScheme_map_of_isHomLift B S hS 𝒳.val.val.p _ (isHomLift_graphFst ω) hω.2.2
    · exact flat_toScheme_map_of_isHomLift B S hS 𝒳.val.val.p _ (isHomLift_graphSnd ω) hω.2.1
    · exact (Category.assoc _ _ _).trans ((congrArg (l ≫ ·) ((graphFst_naturality c').trans
        ((graphFst_naturality h).symm.trans
          (congrArg (_ ≫ ·) (graphFst_graphPoint B S hS f))))).trans (Category.assoc _ _ _).symm)
    · exact (Category.assoc _ _ _).trans ((congrArg (l ≫ ·) ((graphSnd_naturality c').trans
        ((graphSnd_naturality h).symm.trans
          (congrArg (_ ≫ ·) (graphSnd_graphPoint B S hS f))))).trans
          ((Category.assoc _ _ _).trans (Category.assoc _ _ _)).symm)
  have h := (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf).pullback_stable e.inv hT
  rwa [← Sieve.pullback_comp, Iso.inv_hom_id, Sieve.pullback_id] at h

end Cover


/-! ### Cartesian along every arrow between flat objects -/

section Cartesian

variable {𝒳 : AlgebraicStacks.{u, w} B S hS}

/-- **A module cartesian along flat arrows between affine objects is cartesian along every arrow
between flat objects over affine schemes.** Let `F` be a presheaf of `O_𝒳`-modules on an
algebraic stack `𝒳` such that for every arrow `φ : z ⟶ x` between objects over affine schemes
lying over a flat morphism of schemes the comparison `O(z) ⊗_{O(x)} F(x) ⟶ F(z)` is bijective.
Then the comparison is bijective along every arrow `f : y ⟶ y'` between flat objects of `𝒳` over
affine schemes.

By `AlgebraicGeometry.Stack.factorizationSieve_mem` and the density of the affine objects
(**Stacks 0H0B**) there is a finite flat covering `q k : z'ₖ ⟶ y` by objects over affine schemes
with factorizations `q k = c k ≫ a k`, `q k ≫ f = c k ≫ b k` through flat arrows `a k`, `b k`;
then `Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_factorizations` applies, the
product of the ring maps along a finite flat covering of affine schemes being faithfully flat. -/
theorem isIso_restrictionBaseChange_of_flatObject
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hF : ∀ ⦃z x : 𝒳.val.val.obj⦄ (φ : z ⟶ x),
      Flat (B.inclusion.map (𝒳.val.val.p.map φ).left) →
      IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj z) →
      IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj x) →
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange
        (R := (structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).obj) F φ.op))
    {y y' : 𝒳.val.val.obj} (hy : flatObject B S hS 𝒳.val y) (hy' : flatObject B S hS 𝒳.val y')
    (hY : IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj y))
    (hY' : IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj y')) (f : y ⟶ y') :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange
      (R := (structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
        (etaleTopology_le_topology B)).obj) F f.op) := by
  classical
  let p := 𝒳.val.val.p
  have hp := 𝒳.val.isFiberedInGroupoids
  have hG := factorizationSieve_mem B S hS (y' := ⟨y', hy'⟩) hy f
  have dense := Stack.AffineCategory.isDenseSubsite_inclusion_siteKind B S hS p hp .fppf
  have := dense.isCoverDense'
  have := dense.isLocallyFull'
  let yA : Stack.AffineCategory B S hS p := ⟨y, hY⟩
  have hGA : (factorizationSieve B S hS f : Sieve ((Stack.AffineCategory.inclusion B S hS p).obj
        yA)).functorPullback (Stack.AffineCategory.inclusion B S hS p) ∈
      associatedAffineTopology B S hS p (BigAffineFppf.siteKindTopology B S hS .fppf) yA := by
    rw [← Functor.IsDenseSubsite.functorPushforward_mem_iff
      (G := Stack.AffineCategory.inclusion B S hS p)
      (K := BigFppfOver.associatedTopology B S hS p .fppf)]
    exact Functor.IsCoverDense.functorPullback_pushforward_covering ⟨_, hG⟩
  obtain ⟨E, hfin, hflat, -, hle⟩ :=
    Stack.AffineCategory.exists_finite_flat_covering B S hS p hp .fppf _ hGA
  obtain ⟨-, hfl⟩ := (Scheme.presieve₀_mem_precoverage_iff _).mp hflat
  have hmem : ∀ k : E.I₀, factorizationSieve B S hS f (E.f k).hom := fun k =>
    hle _ (Sieve.ofArrows_mk _ _ k)
  choose w c a b haff ha hb hca hcb using hmem
  have hff := Stack.AffineCategory.faithfullyFlat_pi_map B S hS p
    ((Stack.AffineCategory.inclusion B S hS p).op ⋙ (structureSheaf B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj) rfl E hfin hflat
  exact Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_factorizations
    (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj) F f
    (fun k => (E.X k).obj) w (fun k => (E.f k).hom) c a b hca hcb hff
    (fun k => hF _ (hfl k) (E.X k).property hY)
    (fun k => hF _ (ha k) (haff k) hY) (fun k => hF _ (hb k) (haff k) hY')

attribute [local instance] FlatFppf.isContinuous_inclusion' FlatFppf.isCocontinuous_inclusion'

/-- **The pullback to the flat-fppf site of a module cartesian along flat arrows between affine
objects is cartesian along every arrow between objects over affine schemes.** Let `M` be a sheaf
of `O_𝒳`-modules on `𝒳_fppf` whose underlying presheaf is cartesian along every arrow between
objects over affine schemes lying over a flat morphism of schemes. Then its pullback `g^{-1}M`
along the morphism of ringed topoi `g` of **Stacks 0788** (2) is cartesian along every arrow of
the flat-fppf site between objects over affine schemes.

`g^{-1}M` is the restriction of `M` to the flat objects
(`AlgebraicGeometry.Stack.subsiteModulePullbackIsoRestriction`), and an arrow of the flat-fppf
site is an arrow between flat objects of `𝒳`, so this is
`AlgebraicGeometry.Stack.isIso_restrictionBaseChange_of_flatObject`. -/
theorem FlatFppf.isIso_restrictionBaseChange_modulePullback
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl))
    (hM : ∀ ⦃z x : 𝒳.val.val.obj⦄ (φ : z ⟶ x),
      Flat (B.inclusion.map (𝒳.val.val.p.map φ).left) →
      IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj z) →
      IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj x) →
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange
        (R := (AlgebraicGeometry.Stack.structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
          (etaleTopology B)
          (etaleTopology_le_topology B)).obj) M.val φ.op))
    ⦃y y' : FlatFppf B S hS 𝒳⦄ (f : y ⟶ y')
    (hy : IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj y.obj))
    (hy' : IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj y'.obj)) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange
      (R := (AlgebraicGeometry.Stack.subsiteStructureSheaf B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids B.topology
        le_rfl (FlatFppf.objectProperty B S hS 𝒳)).obj)
      ((FlatFppf.modulePullback B S hS 𝒳).obj M).val f.op) := by
  have h' : IsIso (Stacks.PresheafOfModules.restrictionBaseChange
      (R := (AlgebraicGeometry.Stack.subsiteStructureSheaf B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids B.topology
        le_rfl (FlatFppf.objectProperty B S hS 𝒳)).obj)
      ((SheafOfModules.forget _).obj
        ((Stacks.SheafOfModules.inverseImage.{u} (subsiteTopology B S hS 𝒳.val.val.p B.topology
        (FlatFppf.objectProperty B S hS 𝒳)) (associatedTopology B S hS 𝒳.val.val.p B.topology)
        (FlatFppf.objectProperty B S hS 𝒳).ι
        (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids B.topology
          le_rfl)).obj M)) f.op) :=
    isIso_restrictionBaseChange_of_flatObject B S hS M.val hM y.property y'.property hy hy' f.hom
  exact @Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_iso _ _
    (AlgebraicGeometry.Stack.subsiteStructureSheaf B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl (FlatFppf.objectProperty B S hS 𝒳)).obj _ _
    ((SheafOfModules.forget _).mapIso
      ((AlgebraicGeometry.Stack.subsiteModulePullbackIsoRestriction B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids B.topology le_rfl
      (FlatFppf.objectProperty B S hS 𝒳)).app M).symm) _ _ f.op h'

end Cartesian

end AlgebraicGeometry.Stack

end
