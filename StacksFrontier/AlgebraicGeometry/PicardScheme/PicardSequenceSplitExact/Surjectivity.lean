module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSequenceSplitExact.SplittingExactness

/-!
# Surjectivity onto the Picard functor

For a morphism `f : X ⟶ S` of a big fppf site with a section `σ`: normalisation of Picard classes
by the section, local lifts, chosen fibre products of test schemes and of their base changes,
and surjectivity of the map `Pic(X_T) ⟶ Pic_{X/S}(T)`
(`Stacks.PicardFunctor.surjective_toPicardFunctorHom`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open CategoryTheory.Pseudofunctor CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe u v w z u' v'

namespace Stacks.PicardFunctor

variable (B : BigFppfSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (f : B.obj hX ⟶ B.obj hS) (σ : S ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 S)

/-! ### Normalisation by the section, and local lifts -/

/-- Two Picard classes of `X_T` that die on the restriction along the induced section and have
the same class in the Picard functor are equal: the kernel of `σ_T^*` meets the image of
pullback from `Pic(T)` in zero. -/
theorem eq_of_schemePullbackClass_baseChangeSection_eq_zero
    (hOiso : ∀ U : BigFppfOver B S hS,
      IsIso (baseChangeProj B hX hS f U).toLRSHom.toHom.c)
    (T : BigFppfOver B S hS) (a b : picardAt B hX hS f T)
    (ha : Stacks.Picard.schemePullbackClass (baseChangeSection B hX hS f σ hσ T) a = 0)
    (hb : Stacks.Picard.schemePullbackClass (baseChangeSection B hX hS f σ hσ T) b = 0)
    (hab : toPicardFunctorHom B hX hS f T a = toPicardFunctorHom B hX hS f T b) : a = b := by
  have hz : toPicardFunctorHom B hX hS f T (a - b) = 0 := by rw [map_sub, hab, sub_self]
  obtain ⟨N, hN⟩ :=
    (exact_schemePullbackClass_baseChangeProj_toPicardFunctorHom B hX hS f σ hσ hOiso T
      (a - b)).1 hz
  have hsplit := schemePullbackClass_baseChangeSection_baseChangeProj B hX hS f σ hσ T N
  rw [hN] at hsplit
  have hNzero : N = 0 := by
    rw [← hsplit]
    exact (map_sub (Stacks.Picard.schemePullbackClassHom
      (baseChangeSection B hX hS f σ hσ T)) a b).trans (sub_eq_zero.2 (ha.trans hb.symm))
  exact sub_eq_zero.1 ((hNzero ▸ hN).symm.trans
    (map_zero (Stacks.Picard.schemePullbackClassHom (baseChangeProj B hX hS f T))))

/-- The normalisation of a Picard class of `X_T` by the induced section: subtracting the pullback
of its restriction along the section. -/
def normalizedClass (T : BigFppfOver B S hS) (x : picardAt B hX hS f T) :
    picardAt B hX hS f T :=
  x - Stacks.Picard.schemePullbackClassHom (baseChangeProj B hX hS f T)
    (Stacks.Picard.schemePullbackClassHom (baseChangeSection B hX hS f σ hσ T) x)

/-- The normalisation of a Picard class dies on the restriction along the induced section. -/
theorem schemePullbackClass_baseChangeSection_normalizedClass (T : BigFppfOver B S hS)
    (x : picardAt B hX hS f T) :
    Stacks.Picard.schemePullbackClass (baseChangeSection B hX hS f σ hσ T)
      (normalizedClass B hX hS f σ hσ T x) = 0 := by
  have hsplit := schemePullbackClass_baseChangeSection_baseChangeProj B hX hS f σ hσ T
    (Stacks.Picard.schemePullbackClassHom (baseChangeSection B hX hS f σ hσ T) x)
  change Stacks.Picard.schemePullbackClassHom (baseChangeSection B hX hS f σ hσ T)
    (normalizedClass B hX hS f σ hσ T x) = 0
  exact (map_sub _ _ _).trans (sub_eq_zero.2 hsplit.symm)

/-- Normalising a Picard class does not change its class in the Picard functor. -/
theorem toPicardFunctorHom_normalizedClass (T : BigFppfOver B S hS)
    (x : picardAt B hX hS f T) :
    toPicardFunctorHom B hX hS f T (normalizedClass B hX hS f σ hσ T x) =
      toPicardFunctorHom B hX hS f T x := by
  rw [normalizedClass, map_sub,
    show toPicardFunctorHom B hX hS f T
        (Stacks.Picard.schemePullbackClassHom (baseChangeProj B hX hS f T)
          (Stacks.Picard.schemePullbackClassHom
            (baseChangeSection B hX hS f σ hσ T) x)) = 0 from
      toPicardFunctorHom_schemePullbackClass_baseChangeProj B hX hS f T _, sub_zero]


include σ hσ in
/-- **Every section of the Picard functor is locally the class of an invertible module that is
trivial along the induced section.** The sheafification unit is locally surjective, and a local
lift may be normalised by the induced section without changing its class. -/
theorem exists_isCovering_normalizedClass (T : BigFppfOver B S hS)
    (y : (picardFunctor B hX hS f).obj (op T)) :
    ∃ E : PreZeroHypercover.{u + 1} T, BigFppfOver.IsCovering B S hS ⟨T, E⟩ ∧
      ∃ x : ∀ i, picardAt B hX hS f (E.X i),
        (∀ i, Stacks.Picard.schemePullbackClass
            (baseChangeSection B hX hS f σ hσ (E.X i)) (x i) = 0) ∧
          ∀ i, toPicardFunctorHom B hX hS f (E.X i) (x i) =
            (picardFunctor B hX hS f).map (op (E.f i)) y := by
  classical
  have hls : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (toSheafify (BigFppfOver.topology B S hS) (picardPresheaf B hX hS f)) := inferInstance
  have hmem := Presheaf.imageSieve_mem (BigFppfOver.topology B S hS)
    (toSheafify (BigFppfOver.topology B S hS) (picardPresheaf B hX hS f)) (U := op T) y
  obtain ⟨E, hE, hle⟩ := BigFppfOver.exists_isCovering_sieve₀_le B S hS hmem
  have hex : ∀ i, ∃ t : picardAt B hX hS f (E.X i),
      (toPicardFunctor B hX hS f).app (op (E.X i)) t =
        (picardFunctor B hX hS f).map (op (E.f i)) y := fun i => hle _ (E.sieve₀_f i)
  choose x hx using hex
  refine ⟨E, hE, fun i => normalizedClass B hX hS f σ hσ (E.X i) (x i),
    fun i => schemePullbackClass_baseChangeSection_normalizedClass B hX hS f σ hσ (E.X i) (x i),
    fun i => ?_⟩
  rw [toPicardFunctorHom_normalizedClass, toPicardFunctorHom_apply]
  exact hx i


/-- The base change of `X ⟶ S` along the test schemes of the site, as a functor: it sends a
test scheme `T` to `X_T` and a morphism of test schemes to the transition map of the base
changes. -/
def baseChangeFunctor : BigFppfOver B S hS ⥤ Scheme.{u} where
  obj T := baseChange B hX hS f T
  map g := baseChangeMap B hX hS f g
  map_id T := baseChangeMap_id B hX hS f T
  map_comp g h := baseChangeMap_comp B hX hS f g h

include hσ in
/-- The induced sections of the base changes, as a natural transformation from the forgetful
functor on test schemes to the base change functor. -/
def baseChangeSectionNatTrans :
    BigFppfOver.toScheme B S hS ⟶ baseChangeFunctor B hX hS f where
  app T := baseChangeSection B hX hS f σ hσ T
  naturality _ _ g := (baseChangeSection_comp_baseChangeMap B hX hS f σ hσ g).symm

/-- The sieve generated by a covering family of test schemes is a covering sieve. -/
private theorem sieve₀_mem_topology (T : BigFppfOver B S hS)
    (E : PreZeroHypercover.{u + 1} T) (hE : BigFppfOver.IsCovering B S hS ⟨T, E⟩) :
    E.sieve₀ ∈ BigFppfOver.topology B S hS T := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact Precoverage.generate_mem_toGrothendieck ⟨E.map (BigFppfOver.forget B S hS), rfl, hE⟩

/-- Two sections of an fppf sheaf on the `S`-schemes of the site that agree on the members of a
covering family agree. -/
private theorem eq_of_isCovering {F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F')
    (T : BigFppfOver B S hS) (E : PreZeroHypercover.{u + 1} T)
    (hE : BigFppfOver.IsCovering B S hS ⟨T, E⟩) {x y : F'.obj (op T)}
    (h : ∀ i, F'.map (op (E.f i)) x = F'.map (op (E.f i)) y) : x = y := by
  have heq : (TypeCat.ofHom (fun _ : PUnit.{u + 2} => x)) =
      TypeCat.ofHom (fun _ : PUnit.{u + 2} => y) := by
    refine hF.hom_ext_ofArrows (X := E.X) E.f (sieve₀_mem_topology B hS T E hE) fun i => ?_
    ext z
    exact h i
  exact ConcreteCategory.congr_hom heq PUnit.unit


/-- A trivialisation along the induced section of a Picard class of `X_U` that dies on that
restriction, with the structure sheaf of the base pulled back along `U ⟶ T` as target. -/
private theorem nonempty_sectionTrivialization {T U : BigFppfOver B S hS} (g : U ⟶ T)
    (x : picardAt B hX hS f U)
    (hx : Stacks.Picard.schemePullbackClass (baseChangeSection B hX hS f σ hσ U) x = 0) :
    Nonempty ((modulePullbackPseudofunctor.map
          (baseChangeSection B hX hS f σ hσ U).op.toLoc).toFunctor.obj
        (Stacks.Picard.picardRepresentative (baseChange B hX hS f U).toRingedSpace x).obj ≅
      (modulePullbackPseudofunctor.map
          (B.inclusion.map g.left).op.toLoc).toFunctor.obj
        (SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf)) :=
  ((Stacks.Picard.schemePullbackClass_eq_zero_iff_nonempty_iso_unit
    (baseChangeSection B hX hS f σ hσ U) x).1 hx).map
      (fun e => e ≪≫
        (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (B.inclusion.map g.left)).symm)

/-! ### Chosen fibre products of test schemes and of their base changes -/

/-- The chosen fibre product of two morphisms of the underlying category of a big fppf site: the
fibre product of schemes, which satisfies the site's size bound. -/
def bigFppfSiteChosenPullback {U V T : B.Schemes} (a : U ⟶ T) (b : V ⟶ T) :
    ChosenPullback a b := by
  let W := B.obj (Scheme.size_pullback_lt a.hom b.hom U.property V.property)
  let p : W ⟶ U := ObjectProperty.homMk (pullback.fst a.hom b.hom)
  let q : W ⟶ V := ObjectProperty.homMk (pullback.snd a.hom b.hom)
  have h : p ≫ a = q ≫ b := by
    apply ObjectProperty.hom_ext
    exact pullback.condition
  refine ⟨W, p, q, h, ?_, p ≫ a, rfl⟩
  refine PullbackCone.IsLimit.mk _
    (fun c => ObjectProperty.homMk
      (pullback.lift c.fst.hom c.snd.hom (congrArg (fun k => k.hom) c.condition)))
    (fun c => ?_) (fun c => ?_) (fun c m hm hn => ?_)
  · apply ObjectProperty.hom_ext
    exact pullback.lift_fst _ _ _
  · apply ObjectProperty.hom_ext
    exact pullback.lift_snd _ _ _
  · apply ObjectProperty.hom_ext
    apply pullback.hom_ext
    · change m.hom ≫ pullback.fst a.hom b.hom =
        pullback.lift c.fst.hom c.snd.hom _ ≫ _
      rw [pullback.lift_fst]
      exact congrArg (fun k => k.hom) hm
    · change m.hom ≫ pullback.snd a.hom b.hom =
        pullback.lift c.fst.hom c.snd.hom _ ≫ _
      rw [pullback.lift_snd]
      exact congrArg (fun k => k.hom) hn

/-- The chosen fibre product of two morphisms of test schemes over `S`, carried by the chosen
fibre product of the underlying morphisms of the site. -/
def bigFppfOverChosenPullback {U V T : BigFppfOver B S hS} (a : U ⟶ T)
    (b : V ⟶ T) : ChosenPullback a b := by
  let c := bigFppfSiteChosenPullback B a.left b.left
  let W := Over.mk (c.p₁ ≫ U.hom)
  let p : W ⟶ U := Over.homMk c.p₁
  let q : W ⟶ V := Over.homMk c.p₂ (by
    change c.p₂ ≫ V.hom = c.p₁ ≫ U.hom
    rw [← Over.w a, ← Over.w b, ← Category.assoc, ← Category.assoc, c.condition])
  have h : p ≫ a = q ≫ b := Over.OverMorphism.ext c.condition
  refine ⟨W, p, q, h, ?_, p ≫ a, rfl⟩
  apply isLimitOfReflects (Over.forget (B.obj hS))
  exact (isLimitMapConePullbackConeEquiv (Over.forget (B.obj hS)) h).symm c.isLimit

/-- The chosen fibre product of the base changes of two morphisms of test schemes: the base
change `X_{U ×_T V}` of the chosen fibre product, with the base changes of the projections. -/
def baseChangeChosenPullback {U V T : BigFppfOver B S hS} (a : U ⟶ T) (b : V ⟶ T) :
    ChosenPullback (baseChangeMap B hX hS f a) (baseChangeMap B hX hS f b) :=
  let c := bigFppfOverChosenPullback B hS a b
  let h := baseChangeMap_isPullback B hX hS f c.p₁ c.p₂ a b
    (IsPullback.of_hasPullback (B.inclusion.map a.left) (B.inclusion.map b.left)) c.condition
  { pullback := baseChange B hX hS f c.pullback
    p₁ := baseChangeMap B hX hS f c.p₁
    p₂ := baseChangeMap B hX hS f c.p₂
    condition := h.w
    isLimit := h.isLimit }

/-- The chosen wide fibre product of three morphisms of test schemes over `S`. -/
def bigFppfOverChosenPullback₃ {U V W T : BigFppfOver B S hS} (a : U ⟶ T)
    (b : V ⟶ T) (c : W ⟶ T) :
    ChosenPullback₃ (bigFppfOverChosenPullback B hS a b)
      (bigFppfOverChosenPullback B hS b c) (bigFppfOverChosenPullback B hS a c) :=
  Stacks.Limits.chosenPullback₃OfChosenPullback _ _ _
    (bigFppfOverChosenPullback B hS (bigFppfOverChosenPullback B hS a b).p₂
      (bigFppfOverChosenPullback B hS b c).p₁)

/-- The chosen wide fibre product of the base changes of three morphisms of test schemes: the
base change of the chosen wide fibre product `X_{U ×_T V ×_T W}`. -/
def baseChangeChosenPullback₃ {U V W T : BigFppfOver B S hS} (a : U ⟶ T)
    (b : V ⟶ T) (c : W ⟶ T) :
    ChosenPullback₃ (baseChangeChosenPullback B hX hS f a b)
      (baseChangeChosenPullback B hX hS f b c) (baseChangeChosenPullback B hX hS f a c) :=
  Stacks.Limits.chosenPullback₃OfChosenPullback _ _ _
    (baseChangeChosenPullback B hX hS f (bigFppfOverChosenPullback B hS a b).p₂
      (bigFppfOverChosenPullback B hS b c).p₁)

/-! ### Surjectivity onto the Picard functor -/

/-- The base change of a covering family of test schemes, as a zero-hypercover of `X_T`. -/
def baseChangeHypercover (T : BigFppfOver B S hS) (E : PreZeroHypercover.{u + 1} T) :
    PreZeroHypercover.{u + 1} (baseChange B hX hS f T) where
  I₀ := E.I₀
  X i := baseChange B hX hS f (E.X i)
  f i := baseChangeMap B hX hS f (E.f i)

/-- The square of base changes attached to the chosen fibre product of two morphisms of test
schemes is a fibre-product square. -/
private theorem isPullback_baseChangeChosen {U V T : BigFppfOver B S hS} (a : U ⟶ T)
    (b : V ⟶ T) :
    IsPullback (baseChangeMap B hX hS f (bigFppfOverChosenPullback B hS a b).p₁)
      (baseChangeMap B hX hS f (bigFppfOverChosenPullback B hS a b).p₂)
      (baseChangeMap B hX hS f a) (baseChangeMap B hX hS f b) :=
  (baseChangeChosenPullback B hX hS f a b).isPullback

/-- The square of base changes attached to the chosen wide fibre product of three morphisms of
test schemes is a fibre-product square. -/
private theorem isPullback_baseChangeChosen₃ {U V W T : BigFppfOver B S hS} (a : U ⟶ T)
    (b : V ⟶ T) (c : W ⟶ T) :
    IsPullback (baseChangeMap B hX hS f (bigFppfOverChosenPullback₃ B hS a b c).p₁₂)
      (baseChangeMap B hX hS f (bigFppfOverChosenPullback₃ B hS a b c).p₂₃)
      (baseChangeMap B hX hS f (bigFppfOverChosenPullback B hS a b).p₂)
      (baseChangeMap B hX hS f (bigFppfOverChosenPullback B hS b c).p₁) :=
  isPullback_baseChangeChosen B hX hS f (bigFppfOverChosenPullback B hS a b).p₂
    (bigFppfOverChosenPullback B hS b c).p₁

/-- Two Picard classes on base changes of test schemes whose pullbacks to a common base change
agree have isomorphic representatives there. -/
private theorem nonempty_iso_pullback_representative {V U U' : BigFppfOver B S hS}
    (a : V ⟶ U) (b : V ⟶ U') (xi : picardAt B hX hS f U) (xj : picardAt B hX hS f U')
    (h : picardMap B hX hS f a xi = picardMap B hX hS f b xj) :
    Nonempty ((modulePullbackPseudofunctor.map
          (baseChangeMap B hX hS f a).op.toLoc).toFunctor.obj
        (Stacks.Picard.picardRepresentative
          (baseChange B hX hS f U).toRingedSpace xi).obj ≅
      (modulePullbackPseudofunctor.map
          (baseChangeMap B hX hS f b).op.toLoc).toFunctor.obj
        (Stacks.Picard.picardRepresentative
          (baseChange B hX hS f U').toRingedSpace xj).obj) := by
  refine (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _
    (Stacks.RingedSpace.modulePullback_isInvertible_of
      (baseChangeMap B hX hS f a).toLRSHom.toShHom _
      (Stacks.Picard.picardRepresentative (baseChange B hX hS f U).toRingedSpace xi).property)
    (Stacks.RingedSpace.modulePullback_isInvertible_of
      (baseChangeMap B hX hS f b).toLRSHom.toShHom _
      (Stacks.Picard.picardRepresentative
        (baseChange B hX hS f U').toRingedSpace xj).property)).1 ?_
  refine ((Stacks.Picard.pullbackClass_classOf
    (baseChangeMap B hX hS f a).toLRSHom.toShHom _
      (Stacks.Picard.picardRepresentative
        (baseChange B hX hS f U).toRingedSpace xi).property).symm.trans ?_).trans
    (Stacks.Picard.pullbackClass_classOf (baseChangeMap B hX hS f b).toLRSHom.toShHom _
      (Stacks.Picard.picardRepresentative
        (baseChange B hX hS f U').toRingedSpace xj).property)
  rw [Stacks.Picard.classOf_picardRepresentative,
    Stacks.Picard.classOf_picardRepresentative]
  exact h

include σ hσ in
/-- **The normalised local classes assemble into a quasi-coherent descent datum.** The chosen
trivialisations along the induced sections determine, over the base change of the chosen fibre
product of two members of the family, a unique comparison morphism of the two pullbacks, and
these satisfy the cocycle condition because their restrictions along the sections do. -/
private theorem exists_quasicoherentDescentData
    (hOiso : ∀ U : BigFppfOver B S hS,
      IsIso (baseChangeProj B hX hS f U).toLRSHom.toHom.c)
    (T : BigFppfOver B S hS) (E : PreZeroHypercover.{u + 1} T)
    (x : ∀ i, picardAt B hX hS f (E.X i))
    (hx0 : ∀ i, Stacks.Picard.schemePullbackClass
      (baseChangeSection B hX hS f σ hσ (E.X i)) (x i) = 0)
    (hagree : ∀ (V : BigFppfOver B S hS) (i j : E.I₀) (a : V ⟶ E.X i) (b : V ⟶ E.X j),
      a ≫ E.f i = b ≫ E.f j →
      picardMap B hX hS f a (x i) = picardMap B hX hS f b (x j)) :
    ∃ D : QuasicoherentDescentData (baseChangeHypercover B hX hS f T E).f,
      ∀ i, Nonempty (D.component i ≅ (Stacks.Picard.picardRepresentative
        (baseChange B hX hS f (E.X i)).toRingedSpace (x i)).obj) := by
  classical
  have hLinv : ∀ i, Stacks.SheafOfModules.IsInvertible
      (baseChange B hX hS f (E.X i)).presheaf
      (baseChange B hX hS f (E.X i)).ringCatSheaf.2
      (Stacks.Picard.picardRepresentative
        (baseChange B hX hS f (E.X i)).toRingedSpace (x i)).obj := fun i =>
    (Stacks.Picard.picardRepresentative
      (baseChange B hX hS f (E.X i)).toRingedSpace (x i)).property
  refine ⟨⟨(Pseudofunctor.DescentData'.toDescentDataFunctor modulePullbackPseudofunctor
      (fun i j => Stacks.Picard.mapChosenPullback (baseChangeFunctor B hX hS f)
        (bigFppfOverChosenPullback B hS (E.f i) (E.f j))
        (isPullback_baseChangeChosen B hX hS f (E.f i) (E.f j)))
      (Stacks.Picard.mapChosenPullback₃ (baseChangeFunctor B hX hS f)
        (fun i j => bigFppfOverChosenPullback B hS (E.f i) (E.f j))
        (fun i j k => bigFppfOverChosenPullback₃ B hS (E.f i) (E.f j) (E.f k))
        (fun i j => isPullback_baseChangeChosen B hX hS f (E.f i) (E.f j))
        (fun i j k => isPullback_baseChangeChosen₃ B hX hS f (E.f i) (E.f j) (E.f k)))).obj
      (Stacks.Picard.diagramDescentData (F := modulePullbackPseudofunctor)
        (baseChangeFunctor B hX hS f)
        (fun i j => bigFppfOverChosenPullback B hS (E.f i) (E.f j))
        (fun i j k => bigFppfOverChosenPullback₃ B hS (E.f i) (E.f j) (E.f k))
        (fun i j => isPullback_baseChangeChosen B hX hS f (E.f i) (E.f j))
        (fun i j k => isPullback_baseChangeChosen₃ B hX hS f (E.f i) (E.f j) (E.f k))
        (fun i => (Stacks.Picard.picardRepresentative
          (baseChange B hX hS f (E.X i)).toRingedSpace (x i)).obj)
        (fun {V} q {i j} a b ha hb =>
          Stacks.Picard.normalizedHom (F := modulePullbackPseudofunctor)
            (BigFppfOver.toScheme B S hS) (baseChangeFunctor B hX hS f)
            (baseChangeSectionNatTrans B hX hS f σ hσ) E.f
            (fun i => (Stacks.Picard.picardRepresentative
              (baseChange B hX hS f (E.X i)).toRingedSpace (x i)).obj)
            (SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf)
            (fun i =>
              (nonempty_sectionTrivialization B hX hS f σ hσ (E.f i) (x i) (hx0 i)).some)
            (fun {V'} q' {i' j'} a' b' ha' hb' =>
              Stacks.Picard.bijective_pullHom_section' (baseChangeMap B hX hS f a')
                (baseChangeMap B hX hS f b') (baseChangeProj B hX hS f V')
                (baseChangeSection B hX hS f σ hσ V')
                (baseChangeSection_comp_snd B hX hS f σ hσ V') (hOiso V') _ _
                (hLinv i') (hLinv j')
                (nonempty_iso_pullback_representative B hX hS f a' b' (x i') (x j')
                  (hagree V' i' j' a' b' (ha'.trans hb'.symm))).some _ _ rfl rfl)
            q a b ha hb)
        (fun {V} q {i} a ha => Stacks.Picard.normalizedHom_self _ _ _ _ _ _ _ _ q a ha)
        (fun {V} q {i j k} a b c ha hb hc =>
          Stacks.Picard.normalizedHom_comp _ _ _ _ _ _ _ _ q a b c ha hb hc)
        (fun {V W} r q {i j} a b ha hb =>
          Stacks.Picard.normalizedHom_pull _ _ _ _ _ _ _ _ r q a b ha hb)),
    fun i => Stacks.Picard.isQuasicoherent_of_isInvertible _ (hLinv i)⟩,
    fun i => ⟨Iso.refl _⟩⟩

include σ hσ in
/-- **Stacks Project, Tag 0B9N.** Every section of the Picard functor over a test scheme `T` is
the class of an invertible module on `X_T`: pullback `Pic(X_T) ⟶ Pic_{X/S}(T)` is surjective.
This is exactness at `Pic_{X/S}(T)` of `0 ⟶ Pic(T) ⟶ Pic(X_T) ⟶ Pic_{X/S}(T) ⟶ 0`.

A section is locally the class of an invertible module; normalising those local classes by the
induced sections makes them agree on the overlaps of the covering family, so they form a
quasi-coherent descent datum for the base-changed family, which is an fpqc covering of `X_T`.
Effectivity of fpqc descent produces a module on `X_T`, invertible because its pullbacks are,
and its class restricts to the given section on the covering family. -/
@[stacks 0B9N "surjectivity"]
theorem surjective_toPicardFunctorHom
    (hOiso : ∀ U : BigFppfOver B S hS,
      IsIso (baseChangeProj B hX hS f U).toLRSHom.toHom.c)
    (T : BigFppfOver B S hS) :
    Function.Surjective (toPicardFunctorHom B hX hS f T) := by
  classical
  intro y
  obtain ⟨E, hE, x, hx0, hxy⟩ := exists_isCovering_normalizedClass B hX hS f σ hσ T y
  have hfun : ∀ {V : BigFppfOver B S hS} {i : E.I₀} (a : V ⟶ E.X i),
      (picardFunctor B hX hS f).map (op a)
          ((picardFunctor B hX hS f).map (op (E.f i)) y) =
        (picardFunctor B hX hS f).map (op (a ≫ E.f i)) y := by
    intro V i a
    have hop : (op (E.f i) ≫ op a : Opposite.op T ⟶ Opposite.op V) = op (a ≫ E.f i) := rfl
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, hop]
  have hnorm : ∀ (V : BigFppfOver B S hS) (i : E.I₀) (a : V ⟶ E.X i),
      Stacks.Picard.schemePullbackClass (baseChangeSection B hX hS f σ hσ V)
        (picardMap B hX hS f a (x i)) = 0 := by
    intro V i a
    rw [schemePullbackClass_baseChangeSection_natural B hX hS f σ hσ a (x i),
      show Stacks.Picard.schemePullbackClass
        (baseChangeSection B hX hS f σ hσ (E.X i)) (x i) = 0 from hx0 i]
    exact map_zero (Stacks.Picard.schemePullbackClassHom
      ((BigFppfOver.toScheme B S hS).map a))
  have hagree : ∀ (V : BigFppfOver B S hS) (i j : E.I₀) (a : V ⟶ E.X i) (b : V ⟶ E.X j),
      a ≫ E.f i = b ≫ E.f j →
      picardMap B hX hS f a (x i) = picardMap B hX hS f b (x j) := by
    intro V i j a b hab
    refine eq_of_schemePullbackClass_baseChangeSection_eq_zero B hX hS f σ hσ hOiso V _ _
      (hnorm V i a) (hnorm V j b) ?_
    rw [toPicardFunctorHom_apply, toPicardFunctorHom_apply,
      toPicardFunctor_app_naturality, toPicardFunctor_app_naturality,
      ← toPicardFunctorHom_apply, ← toPicardFunctorHom_apply, hxy i, hxy j,
      hfun a, hfun b, hab]
  obtain ⟨D, hD⟩ := exists_quasicoherentDescentData B hX hS f σ hσ hOiso T E x hx0 hagree
  have h𝒰 : (baseChangeHypercover B hX hS f T E).presieve₀ ∈
      Scheme.fpqcPrecoverage.{u} (baseChange B hX hS f T) :=
    baseChange_presieve_mem_fpqcPrecoverage B hX hS f T E hE
  obtain ⟨M, hMqc, hMiso⟩ := Stacks.Picard.exists_isQuasicoherent_nonempty_iso_component
    (baseChangeHypercover B hX hS f T E) h𝒰 D
  have hMinv : Stacks.SheafOfModules.IsInvertible (baseChange B hX hS f T).presheaf
      (baseChange B hX hS f T).ringCatSheaf.2 M := by
    refine Stacks.Picard.isInvertible_of_pullback_fpqcCover M hMqc
      ⟨baseChangeHypercover B hX hS f T E, h𝒰⟩ fun i => ?_
    refine Stacks.Picard.isInvertible_of_iso (((hMiso i).some.trans (hD i).some).symm) ?_
    exact (Stacks.Picard.picardRepresentative
      (baseChange B hX hS f (E.X i)).toRingedSpace (x i)).property
  set c : picardAt B hX hS f T :=
    Stacks.SheafOfModules.picardClass (baseChange B hX hS f T).presheaf
      (baseChange B hX hS f T).ringCatSheaf.2 M hMinv with hc
  refine ⟨c, ?_⟩
  refine eq_of_isCovering B hS (isSheaf_picardFunctor B hX hS f) T E hE fun i => ?_
  have hclass : picardMap B hX hS f (E.f i) c = x i :=
    (Stacks.Picard.pullbackClass_classOf
        (baseChangeMap B hX hS f (E.f i)).toLRSHom.toShHom M hMinv).trans
      (((Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2
          ⟨(hMiso i).some.trans (hD i).some⟩).trans
        (Stacks.Picard.classOf_picardRepresentative
          (baseChange B hX hS f (E.X i)).toRingedSpace (x i)))
  calc (picardFunctor B hX hS f).map (op (E.f i)) (toPicardFunctorHom B hX hS f T c)
      = (toPicardFunctor B hX hS f).app (op (E.X i)) (picardMap B hX hS f (E.f i) c) :=
        (toPicardFunctor_app_naturality B hX hS f (E.f i) c).symm
    _ = (toPicardFunctor B hX hS f).app (op (E.X i)) (x i) := by rw [hclass]
    _ = (picardFunctor B hX hS f).map (op (E.f i)) y := hxy i

end Stacks.PicardFunctor

end
