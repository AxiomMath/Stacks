module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BaseSites
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FppfLocalLifts
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveFlatFppfLocalSections
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmoothRefinement

/-!
# Étale-local lifts along a surjective smooth morphism

Along a 1-morphism representable by algebraic spaces, surjective and smooth, every object of the
target lifts étale-locally: it admits an étale covering each member of which is the image of an
object of the source.

## Main results

* `AlgebraicGeometry.exists_etaleRefinement_of_smooth_surjective`: a smooth surjective morphism
  of objects of a big fppf site is refined by an étale covering by objects of the site.
* `AlgebraicGeometry.mem_etaleOverTopology_of_family`: a jointly surjective family of étale
  morphisms generates a covering sieve of the étale topology on the slice over `S`.
* `AlgebraicGeometry.Stack.exists_scheme_lift_of_representable_isSurjective_isSmooth`: every
  object of a fibre of the target lifts along a *single* smooth surjective morphism of the site.
* `AlgebraicGeometry.Stack.exists_etaleLocalLift_of_representable`: along a 1-morphism of
  categories fibred in groupoids representable by algebraic spaces, surjective and smooth, every
  object `y` of the target receives a morphism from the image of an object of the source whose
  singleton generates an étale covering sieve of `y`;
  `AlgebraicGeometry.Stack.exists_etaleCovering_fibre_lift_of_representable` is the family form.
* `AlgebraicGeometry.Stack.exists_etaleLocalLift` and
  `AlgebraicGeometry.Stack.exists_etaleCovering_fibre_lift`: the same two statements for a
  surjective smooth 1-morphism of algebraic stacks.

## References

* [Stacks Project, Tag 06XH](https://stacks.math.columbia.edu/tag/06XH)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u v w

/-- A quasi-compact scheme carrying a morphism locally of finite type to an object of a big fppf
site is itself an object of that site. -/
theorem contains_of_locallyOfFiniteType (B : BigFppfSite.{u}) {U : B.Schemes}
    {X : Scheme.{u}} (f : X ⟶ B.inclusion.obj U) [LocallyOfFiniteType f] [CompactSpace X] :
    B.Contains X :=
  (Scheme.size_le_of_locallyOfFiniteType f).trans_lt U.property

/-- Let `m : T ⟶ U` be a smooth morphism of objects of a big fppf site and let `x` be a point of
`U` in the image of `m`. Then `x` is in the image of an étale morphism to `U` whose source is an
object of the site and which factors through `m`. -/
theorem exists_contains_etale_lift_of_smooth (B : BigFppfSite.{u}) {U T : B.Schemes}
    (m : T ⟶ U) (hsm : Smooth (B.inclusion.map m)) (x : B.inclusion.obj U)
    (hx : x ∈ Set.range (B.inclusion.map m)) :
    ∃ (X : Scheme.{u}) (_ : B.Contains X) (e : X ⟶ B.inclusion.obj U), Etale e ∧
      x ∈ Set.range e ∧ ∃ c : X ⟶ B.inclusion.obj T, c ≫ B.inclusion.map m = e := by
  obtain ⟨N, g, hg⟩ :=
    exists_etaleNeighborhood_lift_of_smooth (B.inclusion.map m) x hx
  obtain ⟨V, hV, hpV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := N.scheme) (x := N.point) (U := ⊤) trivial
  have : IsAffine V.toScheme := hV
  have hcontains : B.Contains V.toScheme := contains_of_locallyOfFiniteType B (V.ι ≫ N.toBase)
  exact ⟨V.toScheme, hcontains, V.ι ≫ N.toBase, inferInstance, ⟨⟨N.point, hpV⟩, N.map_point⟩,
    V.ι ≫ g, by rw [Category.assoc, hg]⟩

/-- A smooth surjective morphism `m : T ⟶ U` of the underlying category of a big fppf site is
refined by an étale covering by objects of that category: there is a family `e i : W i ⟶ U` of
étale morphisms which is jointly surjective and each of whose members factors through `m`. -/
theorem exists_etaleRefinement_of_smooth_surjective
    (B : BigFppfSite.{u}) {U T : B.Schemes} (m : T ⟶ U)
    (hsm : Smooth (B.inclusion.map m)) (hsurj : Surjective (B.inclusion.map m)) :
    ∃ (I : Type (u + 1)) (W : I → B.Schemes) (e : ∀ i, W i ⟶ U),
      (∀ i, Etale (B.inclusion.map (e i))) ∧
      (∀ x : B.inclusion.obj U, ∃ i, x ∈ Set.range (B.inclusion.map (e i))) ∧
      ∀ i, ∃ c : W i ⟶ T, c ≫ m = e i := by
  classical
  have hdata (x : B.inclusion.obj U) :
      ∃ (X : Scheme.{u}) (_ : B.Contains X) (e : X ⟶ B.inclusion.obj U), Etale e ∧
        x ∈ Set.range e ∧ ∃ c : X ⟶ B.inclusion.obj T, c ≫ B.inclusion.map m = e :=
    exists_contains_etale_lift_of_smooth B m hsm x ((B.inclusion.map m).surjective x)
  choose X hX e he hmem c hc using hdata
  refine ⟨ULift.{u + 1} (B.inclusion.obj U), fun i => B.obj (hX i.down),
    fun i => ObjectProperty.homMk (e i.down), fun i => he i.down,
    fun x => ⟨ULift.up x, hmem x⟩, fun i => ⟨ObjectProperty.homMk (c i.down), ?_⟩⟩
  exact ObjectProperty.hom_ext _ (hc i.down)


namespace Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A surjective smooth 1-morphism between the algebraic stacks represented by two objects of
the site comes from a surjective smooth morphism of those objects, up to 2-isomorphism. -/
theorem exists_schemeMap_of_isSurjective_isSmooth {V U : BigFppfOver B S hS}
    (h : schemeStack.{u, w} B S hS V ⟶ schemeStack.{u, w} B S hS U)
    (hsurj : IsSurjective B S hS h)
    (hsm : AlgebraicStacks.IsSmooth B S hS h) :
    ∃ q : V ⟶ U,
      Smooth ((BigFppfOver.toScheme B S hS).map q) ∧
        Surjective ((BigFppfOver.toScheme B S hS).map q) ∧
          Nonempty (h.hom ≅ schemeFibredCategoryMap B S hS q) := by
  obtain ⟨q, hq⟩ : ∃ q : V ⟶ U, yoneda.map q =
      representingMap B S hS (schemeFibredCategory B S hS V) (schemeFibredCategory B S hS U)
        (yoneda.obj V) (yoneda.obj U) (representedChart B S hS V) (representedChart B S hS U)
        h.hom :=
    ⟨yoneda.preimage _, yoneda.map_preimage _⟩
  refine ⟨q, ?_, ?_, ?_⟩
  · refine (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      Smooth.isEtaleLocalOnSourceAndTarget q).1 ?_
    rw [hq]
    exact (hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS
      (fun _ _ k => Space.IsSmooth B S hS k) (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS)
      (schemeStack.{u, w} B S hS V).property (schemeStack.{u, w} B S hS U).property
      (yoneda.obj V) (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS V) (isAlgebraicSpace_yoneda B S hS U)
      (representedChart B S hS V) (representedChart B S hS U) h.hom).1 hsm
  · refine (Space.presheaf_yoneda_map_iff B S hS
      (inferInstance : MorphismProperty.IsStableUnderBaseChange
        (@Surjective.{u} : MorphismProperty Scheme.{u})) q).1 ?_
    refine (Space.surjective_yonedaMap_iff_surjective_pointsMap B S hS q).2 ?_
    rw [hq]
    exact isSurjective_representingMap_of_isSurjective B S hS
      (𝒳 := schemeStack.{u, w} B S hS V) (𝒴 := schemeStack.{u, w} B S hS U)
      (yoneda.obj V) (yoneda.obj U)
      (representedChart B S hS V) (representedChart B S hS U) h hsurj
  · obtain ⟨hu⟩ := nonempty_unique_twoIso_of_representingMap_eq B S hS
      (schemeFibredCategory B S hS V) (schemeFibredCategory B S hS U)
      (yoneda.obj V) (yoneda.obj U) (representedChart B S hS V) (representedChart B S hS U)
      (f := h.hom) (g := schemeFibredCategoryMap B S hS q)
      (by rw [representingMap_schemeFibredCategoryMap]; exact hq.symm)
    exact ⟨hu.default⟩

/-- Along a surjective smooth 1-morphism of algebraic stacks, every object of the target lifts
after a single surjective smooth base change by an object of the site. -/
theorem exists_scheme_lift_of_isSurjective_isSmooth
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hsurj : IsSurjective B S hS f)
    (hsm : AlgebraicStacks.IsSmooth B S hS f)
    (U : BigFppfOver B S hS) (y : 𝒴.val.val.p.Fiber U) :
    ∃ (T : B.Schemes) (m : T ⟶ U.left),
      Smooth (B.inclusion.map m) ∧ Surjective (B.inclusion.map m) ∧
        ∃ (x : 𝒳.val.val.obj) (α : (CatFiberedInGroupoids.homFunctor f.hom).obj x ⟶ y.1),
          𝒴.val.val.p.IsHomLift
            (Over.homMk m rfl : (Over.mk (m ≫ U.hom) : BigFppfOver B S hS) ⟶ U) α := by
  classical
  let Y : schemeFibredCategory B S hS U ⟶ 𝒴.val :=
    Bicategory.InducedBicategory.mkHom
      (Functor.TwoYoneda.liftBased 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids U y)
  let b : schemeStack.{u, w} B S hS U ⟶ 𝒴 := Bicategory.InducedBicategory.mkHom Y
  let P : Bicategory.TwoCommSq b f := twoFibreProductSquareAlgebraicStacks B S hS b f
  have hP : Bicategory.IsTwoFibreProduct P :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS b f
  have hPsurj : IsSurjective B S hS P.fst :=
    isSurjective_of_isTwoFibreProduct B S hS P.swap
      (Bicategory.isTwoFibreProduct_swap hP) hsurj
  have hPsm : AlgebraicStacks.IsSmooth B S hS P.fst :=
    AlgebraicStacks.isSmooth_baseChange B S hS f b P hP hsm
  obtain ⟨V, c, hcsm, hcsurj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS P.pt
  have hwsurj : IsSurjective B S hS (c ≫ P.fst) :=
    isSurjective_comp B S hS c P.fst hcsurj hPsurj
  have hwsm : AlgebraicStacks.IsSmooth B S hS (c ≫ P.fst) :=
    AlgebraicStacks.isSmooth_comp B S hS c P.fst hcsm hPsm
  obtain ⟨q, hqsm, hqsurj, ⟨e⟩⟩ :=
    exists_schemeMap_of_isSurjective_isSmooth B S hS (c ≫ P.fst) hwsurj hwsm
  refine ⟨V.left, q.left, hqsm, hqsurj, ?_⟩
  obtain ⟨x, α, hα⟩ := exists_fibre_lift_of_twoCell 𝒳.val.val.p 𝒴.val.val.p
    y q f.hom.hom (c ≫ P.snd).hom.hom
    (Functor.TwoYoneda.liftBased 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids U y)
    (Functor.TwoYoneda.chosenLift 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids U y
      (Over.mk (𝟙 U))).φ
    ((Functor.TwoYoneda.chosenLift 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids U y
      (Over.mk (𝟙 U))).isStronglyCartesian.toIsHomLift)
    ((Bicategory.whiskerLeft c P.iso.inv).hom.hom ≫
      (Bicategory.whiskerRight e.hom Y).hom)
  exact ⟨x.1, α, isHomLift_homMk_left B S hS 𝒴.val.val.p q α hα⟩

end Stack


/-- A jointly surjective family of étale morphisms `e i : W i ⟶ U.left` of objects of a big fppf
site generates a covering sieve of the étale topology on the slice over `S` at `U`. -/
theorem mem_etaleOverTopology_of_family
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U : BigFppfOver B S hS} {I : Type (u + 1)} (W : I → B.Schemes)
    (e : ∀ i, W i ⟶ U.left)
    (hetale : ∀ i, Etale (B.inclusion.map (e i)))
    (hsurj : ∀ x : B.inclusion.obj U.left, ∃ i, x ∈ Set.range (B.inclusion.map (e i))) :
    Sieve.ofArrows (fun i => (Over.mk (e i ≫ U.hom) : BigFppfOver B S hS))
        (fun i => (Over.homMk (e i) : Over.mk (e i ≫ U.hom) ⟶ U))
      ∈ BigFppfOver.baseOverTopology B S hS .etale U := by
  rw [BigFppfOver.baseOverTopology, GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  change Sieve.generate (Presieve.ofArrows W e) ∈ B.etaleTopology U.left
  refine Precoverage.generate_mem_toGrothendieck ?_
  rw [BigFppfSite.etalePrecoverage_eq_comap B, Precoverage.mem_comap_iff,
    Presieve.map_ofArrows]
  exact (Scheme.ofArrows_mem_precoverage_iff _).mpr ⟨hsurj, hetale⟩

namespace Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A factorisation `c ≫ m = e` through `m` lets every arrow into `Over.mk (e ≫ U.hom)` be
refined to an arrow into `Over.mk (m ≫ U.hom)` over `U`. -/
private theorem exists_comp_homMk_eq_of_factors {U : BigFppfOver B S hS} {T W : B.Schemes}
    {m : T ⟶ U.left} {e : W ⟶ U.left} (c : W ⟶ T) (hc : c ≫ m = e) {V : BigFppfOver B S hS}
    (a : V ⟶ (Over.mk (e ≫ U.hom) : BigFppfOver B S hS)) :
    ∃ b : V ⟶ (Over.mk (m ≫ U.hom) : BigFppfOver B S hS),
      b ≫ (Over.homMk m rfl : (Over.mk (m ≫ U.hom) : BigFppfOver B S hS) ⟶ U) =
        a ≫ (Over.homMk e : (Over.mk (e ≫ U.hom) : BigFppfOver B S hS) ⟶ U) :=
  ⟨a ≫ Over.homMk c (by simp [← hc]), by
    rw [Category.assoc]
    congr 1
    exact Over.OverMorphism.ext (by simp [hc])⟩

/-- If the object `y` of a fibre lifts along a smooth surjective morphism `m` of the site, then
the base carries an étale covering sieve over each arrow of which `y` lifts along `f`. -/
private theorem exists_etaleCovering_fibre_lift_of_scheme_lift
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (U : BigFppfOver B S hS) (y : 𝒴.val.p.Fiber U)
    (h : ∃ (T : B.Schemes) (m : T ⟶ U.left),
      Smooth (B.inclusion.map m) ∧ Surjective (B.inclusion.map m) ∧
        ∃ (z : 𝒳.val.obj) (φ : (CatFiberedInGroupoids.homFunctor f).obj z ⟶ y.1),
          𝒴.val.p.IsHomLift
            (Over.homMk m rfl : (Over.mk (m ≫ U.hom) : BigFppfOver B S hS) ⟶ U) φ) :
    ∃ R ∈ BigFppfOver.baseOverTopology B S hS .etale U,
      ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
        ∃ (x : 𝒳.val.obj) (α : (CatFiberedInGroupoids.homFunctor f).obj x ⟶ y.1),
          𝒴.val.p.IsHomLift k α := by
  obtain ⟨T, m, hmsm, hmsurj, z, φ, hφ⟩ := h
  obtain ⟨I, W, e, hetale, hjs, hfacs⟩ :=
    exists_etaleRefinement_of_smooth_surjective B m hmsm hmsurj
  refine ⟨_, mem_etaleOverTopology_of_family B S hS W e hetale hjs, ?_⟩
  rintro V k ⟨V', a, bb, ⟨i⟩, rfl⟩
  obtain ⟨c, hc⟩ := hfacs i
  obtain ⟨b, hb⟩ := exists_comp_homMk_eq_of_factors B S hS c hc a
  have hw : CatFiberedInGroupoids.homFunctor f ⋙ 𝒴.val.p = 𝒳.val.p := f.hom.w
  have hzbase : 𝒳.val.p.obj z = Over.mk (m ≫ U.hom) := by
    rw [← hw]
    exact IsHomLift.domain_eq 𝒴.val.p
      (Over.homMk m rfl : (Over.mk (m ≫ U.hom) : BigFppfOver B S hS) ⟶ U) φ
  obtain ⟨z', ρ, hρ⟩ := 𝒳.isFiberedInGroupoids.exists_lift b z hzbase
  refine ⟨z', (CatFiberedInGroupoids.homFunctor f).map ρ ≫ φ, ?_⟩
  rw [← hb]
  have h₁ : 𝒴.val.p.IsHomLift b ((CatFiberedInGroupoids.homFunctor f).map ρ) :=
    PresheafOfCategories.isHomLift_map_of_comp hw b ρ hρ
  exact IsHomLift.comp 𝒴.val.p b
    (Over.homMk m rfl : (Over.mk (m ≫ U.hom) : BigFppfOver B S hS) ⟶ U)
    ((CatFiberedInGroupoids.homFunctor f).map ρ) φ

/-- If every object of the fibre lifts along a smooth surjective morphism of the site, then each
object `y` of `𝒴` receives a morphism `f(x) ⟶ y` whose singleton generates an étale covering
sieve. -/
private theorem exists_etaleLocalLift_of_scheme_lift
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (y : 𝒴.val.obj)
    (h : ∃ (T : B.Schemes) (m : T ⟶ (𝒴.val.p.obj y).left),
      Smooth (B.inclusion.map m) ∧ Surjective (B.inclusion.map m) ∧
        ∃ (x : 𝒳.val.obj) (α : (CatFiberedInGroupoids.homFunctor f).obj x ⟶ y),
          𝒴.val.p.IsHomLift
            (Over.homMk m rfl :
              (Over.mk (m ≫ (𝒴.val.p.obj y).hom) : BigFppfOver B S hS) ⟶ 𝒴.val.p.obj y) α) :
    ∃ (x : 𝒳.val.obj) (a : (CatFiberedInGroupoids.homFunctor f).obj x ⟶ y),
      Sieve.generate (Presieve.singleton a) ∈
        BigFppfOver.associatedTopology B S hS 𝒴.val.p .etale y := by
  obtain ⟨T, m, hmsm, hmsurj, x, α, hα⟩ := h
  obtain ⟨I, W, e, hetale, hjs, hfacs⟩ :=
    exists_etaleRefinement_of_smooth_surjective B m hmsm hmsurj
  have : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  refine ⟨x, α, ?_⟩
  refine Functor.generate_singleton_mem_inheritedTopology_of_isHomLift 𝒴.val.p
    (BigFppfOver.baseOverTopology B S hS .etale) α
    (𝒴.isFiberedInGroupoids.isStronglyCartesian α) _ hα
    (mem_etaleOverTopology_of_family B S hS W e hetale hjs) ?_
  rintro V u ⟨V', b, -, ⟨i⟩, rfl⟩
  obtain ⟨c, hc⟩ := hfacs i
  exact exists_comp_homMk_eq_of_factors B S hS c hc b


/-- Let `f : 𝒳 ⟶ 𝒴` be a surjective smooth 1-morphism of algebraic stacks. Then every object `y`
of `𝒴` admits an object `x` of `𝒳` and a morphism `f(x) ⟶ y` whose singleton generates a covering
sieve of the étale topology that `𝒴` inherits from the site. -/
@[stacks 06XH "part (2): étale-local lifts along a surjective smooth morphism"]
theorem exists_etaleLocalLift {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hsurj : IsSurjective B S hS f)
    (hsmooth : AlgebraicStacks.IsSmooth B S hS f)
    (y : 𝒴.val.val.obj) :
    ∃ (x : 𝒳.val.val.obj) (a : (CatFiberedInGroupoids.homFunctor f.hom).obj x ⟶ y),
      Sieve.generate (Presieve.singleton a) ∈
        BigFppfOver.associatedTopology B S hS 𝒴.val.val.p .etale y := by
  exact exists_etaleLocalLift_of_scheme_lift B S hS f.hom y
    (exists_scheme_lift_of_isSurjective_isSmooth B S hS f hsurj hsmooth _ (Functor.Fiber.mk rfl))

/-- Along a surjective smooth 1-morphism of algebraic stacks, every object of the base carries a
covering sieve of the étale topology over each of whose arrows the given object of the fibre
lifts. -/
@[stacks 06XH "part (2): étale covering of the base with a lift over every arrow"]
theorem exists_etaleCovering_fibre_lift {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hsurj : IsSurjective B S hS f)
    (hsmooth : AlgebraicStacks.IsSmooth B S hS f)
    (U : BigFppfOver B S hS) (y : 𝒴.val.val.p.Fiber U) :
    ∃ R ∈ BigFppfOver.baseOverTopology B S hS .etale U,
      ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
        ∃ (x : 𝒳.val.val.obj) (α : (CatFiberedInGroupoids.homFunctor f.hom).obj x ⟶ y.1),
          𝒴.val.val.p.IsHomLift k α := by
  exact exists_etaleCovering_fibre_lift_of_scheme_lift B S hS f.hom U y
    (exists_scheme_lift_of_isSurjective_isSmooth B S hS f hsurj hsmooth U y)

/-- Let `g : 𝒲 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf site of
`S` which is representable by algebraic spaces, and suppose that every algebraic space
representing the base change of `g` along a scheme-valued point of `𝒴` has surjective and smooth
structural morphism. Then every object `y` of every fibre of `𝒴` admits a *single* morphism
`m : T ⟶ U` of the underlying category of the site, smooth and surjective on the underlying
schemes, along which `y` lifts to `𝒲`. -/
theorem exists_scheme_lift_of_representable_isSurjective_isSmooth
    {𝒲 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (g : 𝒲 ⟶ 𝒴)
    (hg : IsRepresentableByAlgebraicSpaces B S hS g.hom)
    (hprop : ∀ (V : BigFppfOver B S hS)
      (yv : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒴.val.obj)
      (_hyv : yv ⋙ 𝒴.val.p = Over.map V.hom)
      (F : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B V.left.1 V.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom) 𝒲.val.p 𝒴.val.p yv
          (CatFiberedInGroupoids.homFunctor g))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      (let h := (algebraicSpaceMap B S hS V
        ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom
       Space.IsSurjective B S hS h ∧ Space.IsSmooth B S hS h)) :
    ∀ (U : BigFppfOver B S hS) (y : 𝒴.val.p.Fiber U),
      ∃ (T : B.Schemes) (m : T ⟶ U.left),
        Smooth (B.inclusion.map m) ∧ Surjective (B.inclusion.map m) ∧
          ∃ (z : 𝒲.val.obj) (φ : (CatFiberedInGroupoids.homFunctor g).obj z ⟶ y.1),
            𝒴.val.p.IsHomLift
              (Over.homMk m rfl : (Over.mk (m ≫ U.hom) : BigFppfOver B S hS) ⟶ U) φ := by
  intro U y
  obtain ⟨F, hF, e⟩ := hg U (fibrePoint B S hS 𝒴 U y) (fibrePoint_comp B S hS 𝒴 U y)
  obtain ⟨hsurj, hsm⟩ :=
    hprop U (fibrePoint B S hS 𝒴 U y) (fibrePoint_comp B S hS 𝒴 U y) F hF e
  set X : AlgebraicSpaces B U.left.1 U.left.2 := ⟨F, hF⟩ with hX
  set G := (spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj X with hG
  set I := spacesOverSmallerBaseFunctorForgetIso B U.left.1 S U.left.2 hS U.hom with hI
  obtain ⟨T, a, hasurj, haetale⟩ := G.property.exists_atlas
  have hae : Space.IsEtale B S hS a := (Space.isEtale_iff_presheaf_of_yoneda B S hS a).2 haetale
  set t := (I.hom.app X).app (Opposite.op T) (yonedaEquiv a) with ht
  have hm : yonedaEquiv (a ≫ G.obj.hom) = Over.homMk t.1.1 t.2 := by
    rw [yonedaEquiv_comp]
    have hround : (I.inv.app X).app (Opposite.op T) t = yonedaEquiv a :=
      ((I.app X).app (Opposite.op T)).toEquiv.symm_apply_apply _
    rw [ht] at hround ⊢
    rw [← hround]
    exact spacesOverSmallerBaseFunctor_hom_app_forgetIso_inv_app B U.left.1 S U.left.2 hS U.hom
      X (Opposite.op T) _
  have hrw : (Over.homMk t.1.1 t.2 : T ⟶ U) = yoneda.preimage (a ≫ G.obj.hom) := by
    rw [← hm, ← yonedaEquiv_yoneda_map (yoneda.preimage (a ≫ G.obj.hom)), yoneda.map_preimage]
  refine ⟨T.left, t.1.1, ?_, ?_, ?_⟩
  · refine (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      Smooth.isEtaleLocalOnSourceAndTarget (Over.homMk t.1.1 t.2 : T ⟶ U)).1 ?_
    rw [hrw, yoneda.map_preimage]
    exact Space.isSmooth_comp B S hS (isAlgebraicSpace_yoneda B S hS T) G.property
      (isAlgebraicSpace_yoneda B S hS U) a G.obj.hom
      (Space.isSmooth_of_isEtale B S hS G.property hae) hsm
  · refine (Space.presheaf_yoneda_map_iff B S hS
      (inferInstance : MorphismProperty.IsStableUnderBaseChange
        (@Surjective.{u} : MorphismProperty Scheme.{u}))
      (Over.homMk t.1.1 t.2 : T ⟶ U)).1 ?_
    refine (Space.surjective_yonedaMap_iff_surjective_pointsMap B S hS _).2 ?_
    rw [hrw, yoneda.map_preimage]
    exact Space.isSurjective_comp B S hS
      ((Space.surjective_iff_surjective_pointsMap B S hS G.obj.left G.property T a).1 hasurj)
      hsurj
  · obtain ⟨P, hP, _⟩ := PresheafOfCategories.exists_sectionOfObj e.some
      (W := (Over.mk t.1.1 : BigFppfOver B U.left.1 U.left.2)) t.1.2
    exact exists_lift_of_fst_obj B S hS g U y P hP

/-- Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf site of
`S` which is representable by algebraic spaces, and suppose that every algebraic space
representing the base change of `f` along a scheme-valued point of `𝒴` has surjective and smooth
structural morphism. Then every object `y` of `𝒴` admits an object `x` of `𝒳` and a morphism
`a : f(x) ⟶ y` whose singleton generates a covering sieve of the étale topology `𝒴` inherits from
the site. -/
@[stacks 06XH "part (2) in full generality: étale-local lifts along a 1-morphism of CFGs"]
theorem exists_etaleLocalLift_of_representable
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hprop : ∀ (V : BigFppfOver B S hS)
      (yv : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒴.val.obj)
      (_hyv : yv ⋙ 𝒴.val.p = Over.map V.hom)
      (F : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B V.left.1 V.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom) 𝒳.val.p 𝒴.val.p yv
          (CatFiberedInGroupoids.homFunctor f))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      (let h := (algebraicSpaceMap B S hS V
        ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom
       Space.IsSurjective B S hS h ∧ Space.IsSmooth B S hS h))
    (y : 𝒴.val.obj) :
    ∃ (x : 𝒳.val.obj) (a : (CatFiberedInGroupoids.homFunctor f).obj x ⟶ y),
      Sieve.generate (Presieve.singleton a) ∈
        BigFppfOver.associatedTopology B S hS 𝒴.val.p .etale y := by
  exact exists_etaleLocalLift_of_scheme_lift B S hS f y
    (exists_scheme_lift_of_representable_isSurjective_isSmooth B S hS f hf hprop _
      (Functor.Fiber.mk rfl))

/-- Along a 1-morphism of categories fibred in groupoids representable by algebraic spaces whose
base change along every scheme-valued point is surjective and smooth, every object of the base
carries a covering sieve of the étale topology over each of whose arrows the given object of the
fibre lifts. -/
@[stacks 06XH "part (2) in full generality, family form: an étale covering of the base"]
theorem exists_etaleCovering_fibre_lift_of_representable
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hprop : ∀ (V : BigFppfOver B S hS)
      (yv : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒴.val.obj)
      (_hyv : yv ⋙ 𝒴.val.p = Over.map V.hom)
      (F : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B V.left.1 V.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom) 𝒳.val.p 𝒴.val.p yv
          (CatFiberedInGroupoids.homFunctor f))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      (let h := (algebraicSpaceMap B S hS V
        ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom
       Space.IsSurjective B S hS h ∧ Space.IsSmooth B S hS h))
    (U : BigFppfOver B S hS) (y : 𝒴.val.p.Fiber U) :
    ∃ R ∈ BigFppfOver.baseOverTopology B S hS .etale U,
      ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
        ∃ (x : 𝒳.val.obj) (α : (CatFiberedInGroupoids.homFunctor f).obj x ⟶ y.1),
          𝒴.val.p.IsHomLift k α := by
  exact exists_etaleCovering_fibre_lift_of_scheme_lift B S hS f U y
    (exists_scheme_lift_of_representable_isSurjective_isSmooth B S hS f hf hprop U y)

end Stack

end AlgebraicGeometry

end
