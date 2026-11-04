module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatObjectCartesian
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmoothObjectDetection
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleSmoothObject
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsitePrimedFactorizations

/-!
# Local factorizations of an arrow of an algebraic stack, in the étale topology

Let `𝒳` be an algebraic stack, `f : y ⟶ y'` an arrow of `𝒳` and `W` a class of morphisms of
schemes, stable under composition and containing the étale morphisms. This file proves that `y`
is covered, *for the étale topology*, by arrows `q : v ⟶ y` which factor as `q = c ≫ a` with
`q ≫ f = c ≫ b`, for arrows `a : w ⟶ y` and `b : w ⟶ y'` out of an object `w` over an affine
scheme lying over members of `W`, as soon as the distinguished object of every smooth atlas of the
2-fibre product `Y' ×_{y', 𝒳} (Sch/Y)` has both of its components over members of `W`.

The argument is that of `AlgebraicGeometry.Stack.factorizationSieve_mem` (the case `W` = flat, in
the fppf topology), run in the étale topology: the graph of `f` is an object of the 2-fibre
product, covered étale locally (**Stacks 06XH**) by arrows into the image of a smooth atlas, whose
distinguished object is covered, for the étale topology, by objects over affine schemes lying over
étale morphisms (`AlgebraicGeometry.Stack.exists_isAffine_etale_covering_of_object`).

The two instances are:

* `W` = smooth, `y` and `y'` smooth objects
  (`AlgebraicGeometry.Stack.LisseEtale.factorizationSieveOf_mem`):
  the two projections of the 2-fibre product are smooth, base changes of the smooth 1-morphisms
  named by `y` and `y'` (**Stacks 075W**). This is the factorization the lisse-étale site needs.
* `W` = flat, `y` and `y'` flat objects
  (`AlgebraicGeometry.Stack.FlatFppf.factorizationSieveOf_mem`),
  which refines `AlgebraicGeometry.Stack.factorizationSieve_mem` from the fppf to the étale
  topology.

## Main results

* `AlgebraicGeometry.Stack.goodGraphSieve_mem`: the graph of `f` is covered by arrows into
  objects of the 2-fibre product over affine schemes with both components over members of `W`.
* `AlgebraicGeometry.Stack.factorizationSieveOf_mem`: the covering above, for a general `W`.

## References

* [Stacks Project, Tag 06XH](https://stacks.math.columbia.edu/tag/06XH)
* [Stacks Project, Tag 075W](https://stacks.math.columbia.edu/tag/075W)
* [Stacks Project, Tag 07B4](https://stacks.math.columbia.edu/tag/07B4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section HomLift

variable {𝒞 : Type v} [Category.{w} 𝒞] (p : 𝒞 ⥤ BigFppfOver B S hS)

/-- An arrow lying over a morphism of schemes in a class `W`, stable under composition and
containing the étale morphisms, has a morphism of schemes in `W` under it. -/
theorem toScheme_map_mem_of_isHomLift (W : MorphismProperty Scheme.{u})
    [W.IsStableUnderComposition]
    (hWo : ∀ ⦃X Y : Scheme.{u}⦄ (g : X ⟶ Y), Etale g → W g) {U V : BigFppfOver B S hS}
    {k : U ⟶ V} {a b : 𝒞} (φ : a ⟶ b) (hφ : p.IsHomLift k φ)
    (hk : W ((BigFppfOver.toScheme B S hS).map k)) :
    W ((BigFppfOver.toScheme B S hS).map (p.map φ)) := by
  rw [IsHomLift.fac' p k φ]
  simp only [Functor.map_comp, eqToHom_map]
  exact W.comp_mem _ _ (hWo _ inferInstance) (W.comp_mem _ _ hk (hWo _ inferInstance))

/-- If an arrow of `Over T` lies over a morphism of schemes in `W` and its target is over a member
of `W`, then so is its source. -/
private theorem toScheme_map_hom_mem_of_isHomLift (W : MorphismProperty Scheme.{u})
    [W.IsStableUnderComposition] (hWo : ∀ ⦃X Y : Scheme.{u}⦄ (g : X ⟶ Y), Etale g → W g)
    {T U V : BigFppfOver B S hS} {k : U ⟶ V} {c d : Over T} (φ : c ⟶ d)
    (hφ : (Over.forget T).IsHomLift k φ) (hk : W ((BigFppfOver.toScheme B S hS).map k))
    (hd : W ((BigFppfOver.toScheme B S hS).map d.hom)) :
    W ((BigFppfOver.toScheme B S hS).map c.hom) := by
  rw [← Over.w φ, Functor.map_comp]
  exact W.comp_mem _ _ (toScheme_map_mem_of_isHomLift B S hS (Over.forget _) W hWo φ hφ hk) hd

end HomLift

section Graph

variable {B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS} {y : 𝒳.val.val.obj}
  {y' : FlatFppf B S hS 𝒳}

/-- An object of the 2-fibre product over an affine scheme whose two components lie over members
of `W`. At `W` = flat this is `AlgebraicGeometry.Stack.IsGoodGraphObj`. -/
def IsGoodGraphObjOf (W : MorphismProperty Scheme.{u}) (d : GraphObj B S hS 𝒳 y y') : Prop :=
  IsAffine ((BigFppfOver.toScheme B S hS).obj d.base) ∧
    W ((BigFppfOver.toScheme B S hS).map d.x.hom) ∧
    W ((BigFppfOver.toScheme B S hS).map d.y.hom)

/-- The sieve on the graph of `f` of the arrows into good objects of the 2-fibre product. -/
def goodGraphSieve (W : MorphismProperty Scheme.{u}) (f : y ⟶ y'.obj) :
    Sieve (graphPoint B S hS f) where
  arrows {ζ} _ := ∃ ω : GraphObj B S hS 𝒳 y y', IsGoodGraphObjOf W ω ∧ Nonempty (ζ ⟶ ω)
  downward_closed := fun {_ _} _ ⟨ω, hω, ⟨t⟩⟩ g => ⟨ω, hω, ⟨g ≫ t⟩⟩

/-- The condition on the 2-fibre product `Y' ×_{y', 𝒳} (Sch/Y)`: the distinguished object of every
smooth atlas has both components over members of `W`. -/
def AtlasComponentsMem (W : MorphismProperty Scheme.{u}) (y : 𝒳.val.val.obj)
    (y' : FlatFppf B S hS 𝒳) : Prop :=
  ∀ (U₀ : BigFppfOver B S hS)
    (a₀ : schemeStack.{u, w} B S hS U₀ ⟶ (ambientSquare B S hS (chart B S hS 𝒳 y) y').pt),
    AlgebraicStacks.IsSmooth B S hS a₀ →
      W ((BigFppfOver.toScheme B S hS).map (a₀.hom.hom.toFunctor.obj (Over.mk (𝟙 U₀))).x.hom) ∧
      W ((BigFppfOver.toScheme B S hS).map (a₀.hom.hom.toFunctor.obj (Over.mk (𝟙 U₀))).y.hom)

/-- **The graph of `f` is covered, for the étale topology, by arrows into good objects of the
2-fibre product.** -/
theorem goodGraphSieve_mem (W : MorphismProperty Scheme.{u}) [W.IsStableUnderComposition]
    (hWo : ∀ ⦃X Y : Scheme.{u}⦄ (g : X ⟶ Y), Etale g → W g)
    (hatlas : AtlasComponentsMem W y y') (f : y ⟶ y'.obj) :
    goodGraphSieve W f ∈ BigFppfOver.associatedTopology B S hS
      (ambientSquare B S hS (chart B S hS 𝒳 y) y').pt.val.val.p .etale (graphPoint B S hS f) := by
  let P := ambientSquare B S hS (chart B S hS 𝒳 y) y'
  obtain ⟨U₀, a₀, hsm, hsurj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS P.pt
  obtain ⟨x'', α, hgen⟩ := exists_etaleLocalLift B S hS a₀ hsurj hsm (graphPoint B S hS f)
  let s₀ : GraphObj B S hS 𝒳 y y' := a₀.hom.hom.toFunctor.obj (Over.mk (𝟙 U₀))
  obtain ⟨hs₀x, hs₀y⟩ := hatlas U₀ a₀ hsm
  refine (BigFppfOver.associatedTopology B S hS P.pt.val.val.p .etale).transitive hgen _ ?_
  rintro ζ g ⟨Y, m, k, hk, rfl⟩
  cases hk
  obtain ⟨I, ω, ψ, hcov, haff, hopen⟩ := exists_isAffine_etale_covering_of_object B S hS P.pt s₀
  let r : ζ ⟶ s₀ := m ≫ a₀.hom.hom.toFunctor.map
    (Over.homMk x''.hom (Category.comp_id _) : x'' ⟶ Over.mk (𝟙 U₀))
  refine (BigFppfOver.associatedTopology B S hS P.pt.val.val.p .etale).superset_covering ?_
    ((BigFppfOver.associatedTopology B S hS P.pt.val.val.p .etale).pullback_stable r hcov)
  intro Z t ht
  obtain ⟨j, e, -⟩ := (Sieve.mem_ofArrows_iff (Y := ω) ψ _).mp ht
  have hb : W ((BigFppfOver.toScheme B S hS).map (ψ j).hbase) := hWo _ (hopen j)
  exact ⟨ω j, ⟨haff j,
    toScheme_map_hom_mem_of_isHomLift B S hS W hWo (ψ j).a (ψ j).ha hb hs₀x,
    toScheme_map_hom_mem_of_isHomLift B S hS W hWo (ψ j).b (ψ j).hb hb hs₀y⟩, ⟨e⟩⟩

end Graph

section Cover

variable {B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}

/-- **The sieve of local factorizations of an arrow through arrows over members of `W`.** For an
arrow `f : y ⟶ y'` of `𝒳`, the arrows `q : v ⟶ y` for which there are an object `w` over an affine
scheme, arrows `a : w ⟶ y` and `b : w ⟶ y'` over members of `W`, and `c : v ⟶ w` with `c ≫ a = q`
and `c ≫ b = q ≫ f`. At `W` = flat this is `AlgebraicGeometry.Stack.factorizationSieve`. -/
def factorizationSieveOf (W : MorphismProperty Scheme.{u}) {y y' : 𝒳.val.val.obj} (f : y ⟶ y') :
    Sieve y where
  arrows {v} q := ∃ (w : 𝒳.val.val.obj) (c : v ⟶ w) (a : w ⟶ y) (b : w ⟶ y'),
    IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj w)) ∧
    W ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map a)) ∧
    W ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map b)) ∧
    c ≫ a = q ∧ c ≫ b = q ≫ f
  downward_closed := by
    rintro _ _ q ⟨w, c, a, b, h₁, h₂, h₃, h₄, h₅⟩ g
    exact ⟨w, g ≫ c, a, b, h₁, h₂, h₃, by rw [Category.assoc, h₄],
      by rw [Category.assoc, h₅, Category.assoc]⟩

/-- **An arrow factors étale locally through pairs of arrows over members of `W`**, given the
condition `AlgebraicGeometry.Stack.AtlasComponentsMem` on the 2-fibre product. -/
theorem factorizationSieveOf_mem (W : MorphismProperty Scheme.{u}) [W.IsStableUnderComposition]
    (hWo : ∀ ⦃X Y : Scheme.{u}⦄ (g : X ⟶ Y), Etale g → W g)
    {y : 𝒳.val.val.obj} {y' : FlatFppf B S hS 𝒳} (hatlas : AtlasComponentsMem W y y')
    (f : y ⟶ y'.obj) :
    factorizationSieveOf W f ∈ BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale y := by
  let P := ambientSquare B S hS (chart B S hS 𝒳 y) y'
  let π : P.pt ⟶ 𝒳 := P.snd ≫ chart B S hS 𝒳 y
  have hcont := (isContinuous_and_isCocontinuous_homFunctor_associatedTopology B S hS π
    (etaleTopology B)).1
  have hpush := (CoverPreserving.of_isContinuous π.hom.hom.toFunctor
    (associatedTopology B S hS P.pt.val.val.p (etaleTopology B))
    (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))).cover_preserve
      (goodGraphSieve_mem W hWo hatlas f)
  let e := chartIso B S hS 𝒳 y
  have hT : (factorizationSieveOf W f).pullback e.hom ∈
      BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale
        (graphPt B S hS 𝒳 y y' (graphPoint B S hS f)) := by
    refine (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale).superset_covering ?_ hpush
    rintro Z k ⟨ζ, h, l, ⟨ω, hω, ⟨c'⟩⟩, rfl⟩
    refine ⟨graphPt B S hS 𝒳 y y' ω, l ≫ (chart B S hS 𝒳 y).hom.hom.toFunctor.map c'.b,
      graphFst B S hS 𝒳 y y' ω, graphSnd B S hS 𝒳 y y' ω, ?_, ?_, ?_, ?_, ?_⟩
    · have hb : 𝒳.val.val.p.obj (graphPt B S hS 𝒳 y y' ω) = ω.base :=
        (Functor.congr_obj (chart B S hS 𝒳 y).hom.hom.w ω.y).trans ω.hy
      exact hb ▸ hω.1
    · exact toScheme_map_mem_of_isHomLift B S hS 𝒳.val.val.p W hWo _ (isHomLift_graphFst ω) hω.2.2
    · exact toScheme_map_mem_of_isHomLift B S hS 𝒳.val.val.p W hWo _ (isHomLift_graphSnd ω) hω.2.1
    · exact (Category.assoc _ _ _).trans ((congrArg (l ≫ ·)
        ((graphFst_naturality c').trans ((graphFst_naturality h).symm.trans
          (congrArg (_ ≫ ·) (graphFst_graphPoint B S hS f))))).trans (Category.assoc _ _ _).symm)
    · exact (Category.assoc _ _ _).trans ((congrArg (l ≫ ·)
        ((graphSnd_naturality c').trans ((graphSnd_naturality h).symm.trans
          (congrArg (_ ≫ ·) (graphSnd_graphPoint B S hS f))))).trans
          ((Category.assoc _ _ _).trans (Category.assoc _ _ _)).symm)
  have h := (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale).pullback_stable e.inv hT
  rwa [← Sieve.pullback_comp, Iso.inv_hom_id, Sieve.pullback_id] at h

end Cover

/-! ### The two instances -/

section Instances

variable {B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}

/-- **The atlas condition for smooth objects.** If `y` and `y'` are smooth objects, the two
projections of `Y' ×_{y', 𝒳} (Sch/Y)` are smooth (**Stacks 075W**), so the distinguished object
of a smooth atlas, a smooth object of the 2-fibre product, has smooth components. -/
theorem LisseEtale.atlasComponentsMem {y : 𝒳.val.val.obj} {y' : FlatFppf B S hS 𝒳}
    (hy : smoothObject.{u, w} B S hS 𝒳 y) (hy' : smoothObject.{u, w} B S hS 𝒳 y'.obj) :
    AtlasComponentsMem @Smooth y y' := by
  intro U₀ a₀ hsm
  let P := ambientSquare B S hS (chart B S hS 𝒳 y) y'
  have hfst : AlgebraicStacks.IsSmooth B S hS P.fst :=
    AlgebraicStacks.isSmooth_baseChange B S hS (chart B S hS 𝒳 y)
      (ambientSliceMorphism B S hS y') P
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS
        (ambientSliceMorphism B S hS y') (chart B S hS 𝒳 y)) hy
  have hsnd : AlgebraicStacks.IsSmooth B S hS P.snd :=
    AlgebraicStacks.isSmooth_baseChange B S hS (ambientSliceMorphism B S hS y')
      (chart B S hS 𝒳 y) P.swap
      (Bicategory.isTwoFibreProduct_swap
        (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS
          (ambientSliceMorphism B S hS y') (chart B S hS 𝒳 y)))
      (hasPropertyOnSomeSmoothDiagram_of_twoIso B S hS _
        (ambientSliceMorphism_twoIso B S hS y') hy')
  have hs₀ : smoothObject.{u, w} B S hS P.pt (a₀.hom.hom.toFunctor.obj (Over.mk (𝟙 U₀))) :=
    LisseEtale.smoothObject_map.{u, w} B S hS a₀ hsm
      ⟨Over.mk (𝟙 U₀), smoothObject_schemeStack_id.{u, w} B S hS U₀⟩
  exact ⟨(smoothObject_schemeStack_iff.{u, w} B S hS _ _).1
      (LisseEtale.smoothObject_map.{u, w} B S hS P.fst hfst ⟨_, hs₀⟩),
    (smoothObject_schemeStack_iff.{u, w} B S hS _ _).1
      (LisseEtale.smoothObject_map.{u, w} B S hS P.snd hsnd ⟨_, hs₀⟩)⟩

/-- **An arrow between smooth objects factors étale locally through pairs of smooth arrows.** -/
theorem LisseEtale.factorizationSieveOf_mem {y : 𝒳.val.val.obj} {y' : FlatFppf B S hS 𝒳}
    (hy : smoothObject.{u, w} B S hS 𝒳 y) (hy' : smoothObject.{u, w} B S hS 𝒳 y'.obj)
    (f : y ⟶ y'.obj) :
    factorizationSieveOf @Smooth f ∈
      BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale y :=
  AlgebraicGeometry.Stack.factorizationSieveOf_mem @Smooth (fun _ _ _ _ => inferInstance)
    (LisseEtale.atlasComponentsMem hy hy') f

/-- **The atlas condition for flat objects.** If `y` and `y'` are flat objects, the two
projections of `Y' ×_{y', 𝒳} (Sch/Y)` are flat, so the distinguished object of a smooth atlas, a
flat object of the 2-fibre product, has flat components. -/
theorem FlatFppf.atlasComponentsMem {y : 𝒳.val.val.obj} {y' : FlatFppf B S hS 𝒳}
    (hy : flatObject B S hS 𝒳.val y) : AtlasComponentsMem @Flat y y' := by
  intro U₀ a₀ hsm
  let P := ambientSquare B S hS (chart B S hS 𝒳 y) y'
  have hfst : AlgebraicStacks.IsFlat B S hS P.fst :=
    AlgebraicStacks.isFlat_baseChange B S hS (chart B S hS 𝒳 y) (ambientSliceMorphism B S hS y')
      P (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS
        (ambientSliceMorphism B S hS y') (chart B S hS 𝒳 y))
        ((AlgebraicStacks.isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS _).2 hy)
  have hs₀ : flatObject B S hS P.pt.val (a₀.hom.hom.toFunctor.obj (Over.mk (𝟙 U₀))) :=
    FlatFppf.flatObject_map B S hS a₀ (AlgebraicStacks.isFlat_of_isSmooth B S hS a₀ hsm)
      ⟨Over.mk (𝟙 U₀), flatObject_schemeStack_id.{u, w} B S hS U₀⟩
  exact ⟨(flatObject_schemeStack_iff.{u, w} B S hS _ _).1
      (FlatFppf.flatObject_map B S hS P.fst hfst ⟨_, hs₀⟩),
    (flatObject_schemeStack_iff.{u, w} B S hS _ _).1
      (FlatFppf.flatObject_map B S hS P.snd
        (FlatFppf.isFlat_ambientSquare_snd B S hS (chart B S hS 𝒳 y) y') ⟨_, hs₀⟩)⟩

/-- **An arrow out of a flat object into a flat object factors étale locally through pairs of
flat arrows.** This refines `AlgebraicGeometry.Stack.factorizationSieve_mem` from the fppf to the
étale topology. -/
theorem FlatFppf.factorizationSieveOf_mem {y : 𝒳.val.val.obj} {y' : FlatFppf B S hS 𝒳}
    (hy : flatObject B S hS 𝒳.val y) (f : y ⟶ y'.obj) :
    factorizationSieveOf @Flat f ∈
      BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale y :=
  AlgebraicGeometry.Stack.factorizationSieveOf_mem @Flat (fun _ _ _ _ => inferInstance)
    (FlatFppf.atlasComponentsMem hy) f

end Instances

end AlgebraicGeometry.Stack

end
