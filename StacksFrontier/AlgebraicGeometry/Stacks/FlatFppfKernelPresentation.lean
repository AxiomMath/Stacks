module

public import StacksFrontier.AlgebraicGeometry.Stacks.PresentationAlongFunctor
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfCoherator
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherenceConditionsEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts

/-!
# `Q(Ker φ)` is coherent on a locally Noetherian algebraic stack (towards Stacks 0GR9 (3))

Let `𝒳` be an algebraic stack, `φ : ℱ ⟶ 𝒢` a map of quasi-coherent `𝒪_𝒳`-modules with `ℱ` of
finite type, and `y` a flat object of `𝒳` lying over an affine scheme `T` with Noetherian ring
of functions. On the flat-fppf site of `(Sch/T)` the restriction of `Ker φ` is the module
attached to the finitely presented `𝒪(T)`-module `Ker(φ)(y)`: along a flat `W ⟶ T` with `W`
affine, sections of `ℱ` and `𝒢` base change, and so do those of `Ker φ`, tensoring with a flat
algebra being exact. Hence `(f')^{-1}g^{-1}Ker φ` has a finite global presentation, and so does
`(g_!g^{-1}Ker φ)|_{𝒳/y}`. When `𝒳` is locally Noetherian, objects mapping to such `y` cover,
so `Q(Ker φ) = g_!g^{-1}Ker φ` is of finite presentation, i.e. coherent: this is the coherence
half of Stacks 0GR9 (3), for which the source invokes Stacks 0779 (2) and 0GR5.

## Main results

* `FlatFppf.isFinitelyPresentedByGlobalSections_restrictedModuleRestrictionAlong_kernel`:
  the restriction of `Ker φ` along a flat object over a Noetherian affine scheme is finitely
  presented by global sections.
* `FlatFppf.isCoherent_coherator_kernel`: `Q(Ker φ)` is coherent.

## References

* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
* [Stacks Project, Tag 0GR5](https://stacks.math.columbia.edu/tag/0GR5)
* [Stacks Project, Tag 0GR9](https://stacks.math.columbia.edu/tag/0GR9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.SheafOfModules

universe u v r

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- **A finite global presentation at the universe of the sections is a finite global
presentation**: the finite analogue of
`Stacks.SheafOfModules.hasGlobalPresentation_of_isPresentedByGlobalSections`. -/
theorem hasFiniteGlobalPresentation_of_isFinitelyPresentedByGlobalSections
    [HasWeakSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    {M : _root_.SheafOfModules.{r} R} (h : M.IsFinitelyPresentedByGlobalSections) :
    M.HasFiniteGlobalPresentation := by
  obtain ⟨n, k, P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hc⟩⟩ := h
  have : PreservesColimitsOfSize.{r, r}
      (_root_.SheafOfModules.uliftForPresentationFunctor.{u, v, r, r, max u v r} (R := R)) :=
    _root_.SheafOfModules.preservesColimitsOfSize_uliftForPresentationFunctor' R
  have : PreservesColimitsOfSize.{0, 0}
      (_root_.SheafOfModules.uliftForPresentationFunctor.{u, v, r, r, max u v r} (R := R)) :=
    preservesColimitsOfSize_shrink _
  exact ⟨n, k, _, _,
    fun i ↦ (_root_.SheafOfModules.uliftForPresentationFunctor.{u, v, r, r, max u v r}
      (R := R)).map (ι i),
    fun i ↦ (_root_.SheafOfModules.uliftForPresentationFunctor.{u, v, r, r, max u v r}
      (R := R)).map (κ i),
    ⟨(Cofan.isColimitMapCoconeEquiv _ _ (Cofan.mk P ι)) (isColimitOfPreserves _ hP)⟩,
    ⟨(Cofan.isColimitMapCoconeEquiv _ _ (Cofan.mk Q κ)) (isColimitOfPreserves _ hQ)⟩,
    _, _, _, ⟨isColimitCoforkMapOfIsColimit' _ hab hc⟩⟩

end Stacks.SheafOfModules

/-- A finitely presented module has a finite generating family and a finite family generating
its relations, both indexed by `ULift (Fin _)` in the universe of the module. -/
theorem Module.FinitePresentation.exists_ulift_fin_generating_relations.{u₁, u₂} (A : Type u₁)
    (M : Type u₂) [CommRing A] [AddCommGroup M] [Module A M] [Module.FinitePresentation A M] :
    ∃ (n k : ℕ) (s : ULift.{u₂} (Fin n) → M) (ρ : ULift.{u₂} (Fin k) → ULift.{u₂} (Fin n) →₀ A),
      Submodule.span A (Set.range s) = ⊤ ∧
        Submodule.span A (Set.range ρ) = LinearMap.ker (Finsupp.linearCombination A s) := by
  obtain ⟨n, s₀, hs₀⟩ := Module.Finite.exists_fin (R := A) (M := M)
  let s : ULift.{u₂} (Fin n) → M := fun i ↦ s₀ i.down
  have hs : Submodule.span A (Set.range s) = ⊤ := by
    exact (congrArg (Submodule.span A) (ULift.down_surjective.range_comp s₀)).trans hs₀
  have hsurj : Function.Surjective (Finsupp.linearCombination A s) := by
    rwa [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
  obtain ⟨k, ρ₀, hρ₀⟩ := Submodule.fg_iff_exists_fin_generating_family.1
    (Module.FinitePresentation.fg_ker _ hsurj)
  let ρ : ULift.{u₂} (Fin k) → ULift.{u₂} (Fin n) →₀ A := fun i ↦ ρ₀ i.down
  refine ⟨n, k, s, ρ, hs, ?_⟩
  exact (congrArg (Submodule.span A) (ULift.down_surjective.range_comp ρ₀)).trans hρ₀

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A flat object of the stack of a scheme `U` is a flat scheme over `U`.** -/
theorem flat_of_flatObject_schemeStack (U : BigFppfOver B S hS) (x : Over U)
    (hx : flatObject B S hS (schemeStack.{u, w} B S hS U).val x) :
    Flat ((BigFppfOver.toScheme B S hS).map x.hom) := by
  have heq := representingMap_eq_yoneda_map_baseMap B S hS
    (Functor.TwoYoneda.liftBased (Over.forget U)
      (Functor.IsFiberedInGroupoids.over_forget U) x.left (Functor.Fiber.mk (a := x) rfl))
  rw [baseMapOfBasedFunctor_liftBased] at heq
  have key := hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS
    (fun _ _ h => Space.IsFlat B S hS h)
    (Space.isSmoothLocalOnSourceAndTarget_flat B S hS)
    (schemeStack.{u, w} B S hS x.left).property
    (schemeStack.{u, w} B S hS U).property
    (yoneda.obj x.left) (yoneda.obj U)
    (isAlgebraicSpace_yoneda B S hS x.left) (isAlgebraicSpace_yoneda B S hS U)
    (PresheafOfCategories.sliceElementsEquivalenceOver x.left)
    (PresheafOfCategories.sliceElementsEquivalenceOver U)
    (objectMorphism B S hS (schemeFibredCategory B S hS U)
      (Functor.Fiber.mk (a := x) rfl))
  have h2 : Space.IsFlat B S hS (yoneda.map x.hom) :=
    (Iff.of_eq (congrArg (fun f => Space.IsFlat B S hS f) heq)).1 (key.1 hx)
  exact h2 x.left U (𝟙 _) (𝟙 _) x.hom (Space.presheaf_etale_id B S hS x.left)
    (Space.presheaf_etale_id B S hS U) (by simp)

/-- Flatness of the scheme morphism below a morphism of `BigFppfOver` is unchanged by
conjugating with the comparison isomorphisms of equalities of objects. -/
theorem flat_toScheme_map_of_eq {X Y X' Y' : BigFppfOver B S hS} (hX : X = X') (hY : Y = Y')
    (m : X' ⟶ Y') (m' : X ⟶ Y) (h : m' = eqToHom hX ≫ m ≫ eqToHom hY.symm)
    (hm : Flat ((BigFppfOver.toScheme B S hS).map m)) :
    Flat ((BigFppfOver.toScheme B S hS).map m') := by
  subst hX hY h
  simpa using hm

/-- Flatness of the scheme morphism below a morphism of `BigFppfOver` is unchanged by
precomposition with the comparison isomorphism of an equality of objects. -/
alias flat_left_eqToHom_comp' := flat_left_eqToHom_comp

/-- Local finite presentation of the scheme morphism below a morphism of `BigFppfOver` is
unchanged by precomposition with the comparison isomorphism of an equality of objects. -/
theorem locallyOfFinitePresentation_left_eqToHom_comp {V V' X : BigFppfOver B S hS}
    (h : V = V') (m : V' ⟶ X) (hm : LocallyOfFinitePresentation (B.inclusion.map m.left)) :
    LocallyOfFinitePresentation (B.inclusion.map (eqToHom h ≫ m).left) := by
  subst h
  simpa using hm

section Fibred

variable (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))

/-- **An object is covered by objects over affine schemes, along morphisms lying over flat
morphisms locally of finite presentation.** The variant of
`AlgebraicGeometry.Stack.exists_isAffine_covering_of_object` which also records local finite
presentation of the covering morphisms. -/
theorem exists_isAffine_lfp_covering_of_object (x : 𝒳.val.obj) :
    ∃ (I : Type (u + 1)) (y : I → 𝒳.val.obj) (f : ∀ i, y i ⟶ x),
      Sieve.generate (Presieve.ofArrows y f) ∈ fppfTopology B S hS 𝒳 x ∧
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.p.obj (y i)))) ∧
      (∀ i, Flat (B.inclusion.map (𝒳.val.p.map (f i)).left)) ∧
      ∀ i, LocallyOfFinitePresentation (B.inclusion.map (𝒳.val.p.map (f i)).left) := by
  classical
  have hfib := 𝒳.isFiberedInGroupoids.isFibered
  set X : BigFppfOver B S hS := 𝒳.val.p.obj x
  let T : B.Schemes := X.left
  let U := (B.inclusion.obj T).affineOpenCover.openCover
  obtain ⟨W, hW, hWU⟩ := exists_isCovering_tautologicallyEquivalent_openCover B T U
  rcases hWU with ⟨⟨α, hα⟩, ⟨β, hβ⟩⟩
  have hpre : W.presieve₀ ∈ B.precoverage T := ⟨W, rfl, hW⟩
  have hWaff : ∀ j, IsAffine (B.inclusion.obj (W.X j)) := by
    intro j
    obtain ⟨e, _⟩ := hβ j
    have : IsAffine (U.X (β j)) := by
      show IsAffine (Spec ((B.inclusion.obj T).affineOpenCover.X (β j)))
      exact isAffine_Spec _
    exact @IsAffine.of_isIso _ _ e.hom e.isIso_hom inferInstance
  have hWfl : ∀ j, Flat (B.inclusion.map (W.f j)) ∧
      LocallyOfFinitePresentation (B.inclusion.map (W.f j)) := fun j =>
    flat_and_locallyOfFinitePresentation_of_mem_precoverage B _ hpre _ (Presieve.ofArrows.mk j)
  let Vobj (j : W.I₀) : BigFppfOver B S hS := Over.mk (W.f j ≫ X.hom)
  let vmap (j : W.I₀) : Vobj j ⟶ X := Over.homMk (W.f j)
  let y (j : W.I₀) : 𝒳.val.obj :=
    Functor.IsPreFibered.pullbackObj (p := 𝒳.val.p) (a := x) rfl (vmap j)
  let g (j : W.I₀) : y j ⟶ x :=
    Functor.IsPreFibered.pullbackMap (p := 𝒳.val.p) (a := x) rfl (vmap j)
  have hproj : ∀ j, 𝒳.val.p.obj (y j) = Vobj j := fun j =>
    Functor.IsPreFibered.pullbackObj_proj (p := 𝒳.val.p) (a := x) rfl (vmap j)
  have hfac : ∀ j, 𝒳.val.p.map (g j) = eqToHom (hproj j) ≫ vmap j := by
    intro j
    simpa using IsHomLift.fac' 𝒳.val.p (vmap j) (g j)
  refine ⟨W.I₀, y, g, ?_, fun j => (hproj j) ▸ hWaff j, fun j => ?_, fun j => ?_⟩
  · rw [fppfTopology, associatedTopology, Functor.inheritedTopology_eq]
    refine Precoverage.generate_mem_toGrothendieck
      ⟨fun _ q _ => Functor.IsFiberedInGroupoids.isStronglyCartesian
        𝒳.isFiberedInGroupoids q, ?_⟩
    rw [GrothendieckTopology.mem_toPrecoverage_iff, Presieve.map_ofArrows]
    have hBcover : Sieve.ofArrows Vobj vmap ∈ BigFppfOver.topology B S hS X := by
      rw [BigFppfOver.topology, GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
      show Sieve.ofArrows W.X W.f ∈ B.topology T
      simpa [PreZeroHypercover.presieve₀] using Precoverage.generate_mem_toGrothendieck hpre
    refine (BigFppfOver.topology B S hS).superset_covering ?_ hBcover
    rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro j
    exact ⟨𝒳.val.p.obj (y j), eqToHom (hproj j).symm, 𝒳.val.p.map (g j),
      Presieve.ofArrows.mk j, by simp [hfac j]⟩
  · rw [hfac j]
    exact flat_left_eqToHom_comp' B S hS (hproj j) (vmap j) (hWfl j).1
  · rw [hfac j]
    exact locallyOfFinitePresentation_left_eqToHom_comp B S hS (hproj j) (vmap j) (hWfl j).2

end Fibred

namespace FlatFppf

attribute [local instance] isContinuous_inclusion_topology isCocontinuous_inclusion_topology
  hasSheafify_addCommGrpCat wEqualsLocallyBijective_addCommGrpCat

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

section Local

variable {B S hS} {𝒳 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **The local computation.** For a map `φ : ℱ ⟶ 𝒢` of modules cartesian between affine objects
with `ℱ` of finite type, and a flat object `y` lying over an affine scheme with Noetherian ring of
functions, the restriction `(f')^{-1}g^{-1}Ker φ` of `Ker φ` to the flat-fppf site of the scheme
below `y` has a finite global presentation. -/
theorem isFinitelyPresentedByGlobalSections_restrictedModuleRestrictionAlong_kernel
    {F G : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳)} (φ : F ⟶ G)
    (hF : IsCartesianBetweenAffines 𝒳.val.isFiberedInGroupoids F)
    (hG : IsCartesianBetweenAffines 𝒳.val.isFiberedInGroupoids G)
    (hft : F.IsFiniteTypeOnSite) (y : FlatFppf B S hS 𝒳)
    (hyaff : IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj y.obj))
    (hnoeth : IsNoetherianRing (fibredSectionRing B S hS 𝒳.val.val.p y.obj)) :
    ((restrictedModuleRestrictionAlong B S hS (ambientSliceMorphism B S hS y)
      (isFlat_ambientSliceMorphism B S hS y)).obj
        ((moduleInverseImageU B S hS 𝒳).obj (kernel φ))).IsFinitelyPresentedByGlobalSections := by
  classical
  let p := 𝒳.val.val.p
  let hp := 𝒳.val.isFiberedInGroupoids
  let f := ambientSliceMorphism B S hS y
  let hf := isFlat_ambientSliceMorphism B S hS y
  let 𝒵 := schemeStack.{u, w} B S hS (p.obj y.obj)
  have : (primedSiteFunctor B S hS f hf).IsContinuous (topology B S hS 𝒵)
      (topology B S hS 𝒳) := siteFunctor_isContinuous B S hS f hf
  let Fn : FlatFppf B S hS 𝒵 ⥤ 𝒳.val.val.obj :=
    primedSiteFunctor B S hS f hf ⋙ (objectProperty B S hS 𝒳).ι
  have : Fn.IsContinuous (topology B S hS 𝒵) (associatedTopology B S hS p B.topology) :=
    Functor.isContinuous_comp _ _ _ (topology B S hS 𝒳) _
  let K := kernel φ
  let t : FlatFppf B S hS 𝒵 := ⟨Over.mk (𝟙 _), flatObject_schemeStack_id.{u, w} B S hS _⟩
  let ht : IsTerminal t := ObjectProperty.isTerminalFullSubcategory _ (Over.isTerminalMkId _) _
  have hpobj : ∀ V : FlatFppf B S hS 𝒵, p.obj (Fn.obj V) = V.obj.left := fun V ↦
    Functor.congr_obj f.hom.hom.w V.obj
  have hpmap : ∀ {V W : FlatFppf B S hS 𝒵} (h : V ⟶ W),
      p.map (Fn.map h) = eqToHom (hpobj V) ≫ h.hom.left ≫ eqToHom (hpobj W).symm :=
    fun h ↦ Functor.congr_hom f.hom.hom.w h.hom
  have haffV : ∀ V : FlatFppf B S hS 𝒵,
      IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒵.val.val.p.obj V.obj)) →
      IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj (Fn.obj V)) := fun V hV ↦ by
    show IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj (Fn.obj V)))
    rwa [hpobj V]
  have hy₀aff : IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj (Fn.obj t)) := haffV t hyaff
  have hflat : ∀ V : FlatFppf B S hS 𝒵,
      IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒵.val.val.p.obj V.obj)) →
      let := fibredSectionAlgebra (B := B) (S := S) (hS := hS) (p := p) (Fn.map (ht.from V))
      Module.Flat (fibredSectionRing B S hS p (Fn.obj t))
        (fibredSectionRing B S hS p (Fn.obj V)) := by
    intro V hV
    have hm : Flat ((BigFppfOver.toScheme B S hS).map (p.map (Fn.map (ht.from V)))) :=
      flat_toScheme_map_of_eq B S hS (hpobj V) (hpobj t) _ _ (hpmap _)
        (flat_of_flatObject_schemeStack.{u, w} B S hS _ V.obj V.property)
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj (Fn.obj V))) := haffV V hV
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj (Fn.obj t))) := hy₀aff
    exact Scheme.Hom.flat_appTop _
  let A := fibredSectionRing B S hS p (Fn.obj t)
  have : IsNoetherianRing A := by
    show IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Fn.obj t)), ⊤)
    rwa [hpobj t]
  let := fibredSectionsModule hp F (Fn.obj t)
  let := fibredSectionsModule hp K (Fn.obj t)
  have : Module.Finite A (F.val.obj (op (Fn.obj t))) :=
    moduleFinite_sections_of_isFiniteTypeOnSite_fibred hp F hF hft hy₀aff
  have : _root_.IsNoetherian A (F.val.obj (op (Fn.obj t))) :=
    isNoetherian_of_isNoetherianRing_of_finite A _
  let iK : K.val.obj (op (Fn.obj t)) →ₗ[A] F.val.obj (op (Fn.obj t)) :=
    ((kernel.ι φ).val.app (op (Fn.obj t))).hom
  have : Module.Finite A (K.val.obj (op (Fn.obj t))) :=
    Module.Finite.of_injective iK (SheafOfModules.kernel_ι_val_app_injective φ (op (Fn.obj t)))
  have : Module.FinitePresentation A (K.val.obj (op (Fn.obj t))) :=
    Module.finitePresentation_of_finite _ _
  obtain ⟨n, k, s, ρ, hs, hρspan⟩ :=
    Module.FinitePresentation.exists_ulift_fin_generating_relations A (K.val.obj (op (Fn.obj t)))
  have hρ : ∀ i, ((ρ i).sum fun j r ↦ r • s j) = 0 := fun i ↦ by
    have hmem : ρ i ∈ LinearMap.ker (Finsupp.linearCombination A s) :=
      hρspan ▸ Submodule.subset_span ⟨i, rfl⟩
    simpa [Finsupp.linearCombination_apply] using hmem
  have hbc : ∀ W : FlatFppf B S hS 𝒵,
      IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒵.val.val.p.obj W.obj)) →
      Function.Bijective (fibredSectionsBaseChange hp K (Fn.map (ht.from W))) := fun W hW ↦
    bijective_fibredSectionsBaseChange_kernel hp φ (Fn.map (ht.from W))
      (hF _ hy₀aff (haffV W hW)) (hG _ hy₀aff (haffV W hW)) (hflat W hW)
  have := hasSheafify_addCommGrpCat B S hS 𝒵
  have := wEqualsLocallyBijective_addCommGrpCat B S hS 𝒵
  have h : (Fn.sheafPushforwardContinuous RingCat.{u} (topology B S hS 𝒵)
      (associatedTopology B S hS p B.topology)).obj (ambientRingStructureSheaf B S hS 𝒳) =
      subsiteRingStructureSheaf B S hS 𝒵 := inverseImageRing_primedSiteFunctor B S hS f hf
  have main :=
    (Stacks.SheafOfModules.FreeSheafification.isPresentedByGlobalSections_pushforward_of_terminal
    Fn h K t ht (ULift.{u} (Fin n)) (ULift.{u} (Fin k)) s ρ hρ ?_ ?_).2 inferInstance inferInstance
  · refine Stacks.SheafOfModules.isFinitelyPresentedByGlobalSections_of_iso ?_ main
    exact ((_root_.SheafOfModules.pushforwardComp (F := primedSiteFunctor B S hS f hf)
      (G := (objectProperty B S hS 𝒳).ι)
      (eqToHom (inverseImageRing_primedSiteFunctor B S hS f hf).symm)
      (𝟙 (((objectProperty B S hS 𝒳).ι.sheafPushforwardContinuous RingCat.{u}
        (topology B S hS 𝒳) (associatedTopology B S hS p B.topology)).obj
          (ambientRingStructureSheaf B S hS 𝒳)))).app K ≪≫
      (_root_.SheafOfModules.pushforwardCongr
        (by rw [CategoryTheory.Functor.map_id]; exact Category.comp_id _)).app K).symm
  · intro V x
    obtain ⟨T, hT, haff⟩ := FlatFppf.isCoveringFamily_isAffine B S hS 𝒵 V
    refine ⟨T, hT, fun W g hg ↦ ?_⟩
    let := fibredSectionAlgebra (B := B) (S := S) (hS := hS) (p := p) (Fn.map (ht.from W))
    let := fibredSectionsModule hp K (Fn.obj W)
    let := fibredSectionsModuleOver hp K (Fn.map (ht.from W))
    have : IsScalarTower A (fibredSectionRing B S hS p (Fn.obj W)) (K.val.obj (op (Fn.obj W))) :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    exact Module.BaseChange.exists_finsupp_of_surjective_liftBaseChange_of_span
      (fibredSectionsRestrict hp K (Fn.map (ht.from W))) s hs (hbc W (haff hg)).2
      (K.val.map (Fn.map g).op x)
  · intro V c hc
    obtain ⟨T, hT, haff⟩ := FlatFppf.isCoveringFamily_isAffine B S hS 𝒵 V
    refine ⟨T, hT, fun W g hg ↦ ?_⟩
    let := fibredSectionAlgebra (B := B) (S := S) (hS := hS) (p := p) (Fn.map (ht.from W))
    let := fibredSectionsModule hp K (Fn.obj W)
    let := fibredSectionsModuleOver hp K (Fn.map (ht.from W))
    have : IsScalarTower A (fibredSectionRing B S hS p (Fn.obj W)) (K.val.obj (op (Fn.obj W))) :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    let c' : ULift.{u} (Fin n) →₀ fibredSectionRing B S hS p (Fn.obj W) :=
      c.mapRange (fibredSectionRestrict (Fn.map g)) (map_zero _)
    have hc' :
        (c'.sum fun i r ↦ r • fibredSectionsRestrict hp K (Fn.map (ht.from W)) (s i)) = 0 := by
      have h0 := (Stacks.SheafOfModules.FreeSheafification.map_finsupp_sum_smul K.val
        (Fn.map g).op c (fun i ↦ (show K.val.obj (op (Fn.obj V)) from
          K.val.map (Fn.map (ht.from V)).op (s i)))).symm.trans
        ((congrArg (fun m ↦ K.val.map (Fn.map g).op m) hc).trans (map_zero _))
      refine Eq.trans (Finset.sum_congr rfl fun i _ ↦ ?_) h0
      refine congrArg (c' i • ·) ?_
      refine (K.val.congr_map_apply (congrArg (fun m ↦ (Fn.map m).op)
        (ht.hom_ext (ht.from W) (g ≫ ht.from V))) (s i)).trans ?_
      rw [Functor.map_comp, op_comp]
      exact K.val.map_comp_apply _ _ (s i)
    exact Module.BaseChange.exists_finsupp_relations_of_bijective_liftBaseChange_of_span
      (fibredSectionsRestrict hp K (Fn.map (ht.from W))) s hs ρ hρspan (hbc W (haff hg)) c' hc'

end Local

section Coherent

variable {B S hS} (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

/-- The sieve of arrows into `W` whose source maps to a flat object lying over an affine scheme
with Noetherian ring of functions. -/
def noetherianFlatSieve (W : 𝒳.val.val.obj) : Sieve W where
  arrows w _ := ∃ y : FlatFppf B S hS 𝒳,
    IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj y.obj) ∧
      IsNoetherianRing (fibredSectionRing B S hS 𝒳.val.val.p y.obj) ∧ Nonempty (w ⟶ y.obj)
  downward_closed := by
    rintro _ _ _ ⟨y, h₁, h₂, ⟨c⟩⟩ g
    exact ⟨y, h₁, h₂, ⟨g ≫ c⟩⟩

/-- **On a locally Noetherian algebraic stack, objects mapping to Noetherian affine flat objects
cover.** A smooth surjective chart `a : U ⟶ 𝒳` from a locally Noetherian scheme carries the
terminal object of `(Sch/U)` to a flat object `y_U` lying over `U`; the objects of an affine open
covering of `y_U` are flat, affine and locally of finite type over `U`, hence Noetherian; and every
object of `𝒳` is covered by objects of the image of `a`, which all map to `y_U`. -/
theorem noetherianFlatSieve_mem
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    (W : 𝒳.val.val.obj) :
    noetherianFlatSieve 𝒳 W ∈ associatedTopology B S hS 𝒳.val.val.p B.topology W := by
  obtain ⟨U, a, hsurj, hsm, hU⟩ := h𝒳
  let yU := (CatFiberedInGroupoids.homFunctor a.hom).obj (Over.mk (𝟙 U))
  have hyU : flatObject B S hS 𝒳.val yU :=
    flatObject_of_smoothObject.{u, w} B S hS 𝒳 (smoothObject_atlas_obj.{u, w} B S hS a hsm)
  have hpU : 𝒳.val.val.p.obj yU = U := Functor.congr_obj a.hom.hom.w (Over.mk (𝟙 U))
  have hstep : ∀ {z : 𝒳.val.val.obj} (m : z ⟶ yU),
      noetherianFlatSieve 𝒳 z ∈ associatedTopology B S hS 𝒳.val.val.p B.topology z := by
    intro z m
    obtain ⟨I, yi, fi, hcov, haff, hfl, hlfp⟩ :=
      exists_isAffine_lfp_covering_of_object B S hS 𝒳.val yU
    refine GrothendieckTopology.superset_covering _ ?_
      ((associatedTopology B S hS 𝒳.val.val.p B.topology).pullback_stable m hcov)
    rintro w g ⟨w', e, _, ⟨i⟩, -⟩
    have : IsLocallyNoetherian (B.inclusion.obj (𝒳.val.val.p.obj yU).left) := by
      show IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj yU))
      rwa [hpU]
    have := hlfp i
    have : IsLocallyNoetherian (B.inclusion.obj (𝒳.val.val.p.obj (yi i)).left) :=
      LocallyOfFiniteType.isLocallyNoetherian (B.inclusion.map (𝒳.val.val.p.map (fi i)).left)
    have := haff i
    have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj (yi i))) :=
      inferInstanceAs (IsLocallyNoetherian (B.inclusion.obj (𝒳.val.val.p.obj (yi i)).left))
    exact ⟨⟨yi i, flatObject_of_flat B S hS 𝒳 (fi i) (hfl i) hyU⟩, haff i,
      IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩, ⟨e⟩⟩
  obtain ⟨x, α, hα⟩ := exists_etaleLocalLift B S hS a hsurj hsm W
  refine GrothendieckTopology.transitive _
    (BigFppfOver.associatedTopology_le_fppf B S hS 𝒳.val.val.p SiteKind.etale _ hα) _ ?_
  rintro Y g ⟨Y', h, _, ⟨⟩, rfl⟩
  exact hstep (h ≫ (CatFiberedInGroupoids.homFunctor a.hom).map (Over.homMk x.hom (by simp)))

/-- **`Q(Ker φ)` is coherent** (the coherence half of Stacks 0GR9 (3)): for a map `φ : ℱ ⟶ 𝒢` of
coherent modules on a locally Noetherian algebraic stack, `Q(Ker φ) = g_!g^{-1}(Ker φ)` is
coherent. Over every object mapping to a flat object `y` lying over a Noetherian affine scheme it
has a finite global presentation, and those objects cover. -/
theorem isCoherent_coherator_kernel
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    {F G : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳)}
    (hF : IsCoherent B S hS 𝒳 F) (hG : IsCoherent B S hS 𝒳 G) (φ : F ⟶ G) :
    IsCoherent B S hS 𝒳 ((lowerShriekInverseImageCoherator B S hS 𝒳).obj (kernel φ)) := by
  refine (isCoherent_iff_isCoherentModule B S hS 𝒳 h𝒳 _).2 ⟨fun U ↦ ?_⟩
  refine ⟨Σ w : 𝒳.val.val.obj, {g : w ⟶ U // noetherianFlatSieve 𝒳 U g}, fun i ↦ i.1,
    fun i ↦ i.2.1, ?_, fun i ↦ ?_⟩
  · refine GrothendieckTopology.superset_covering _ ?_ (noetherianFlatSieve_mem 𝒳 h𝒳 U)
    intro Y h hh
    exact ⟨Y, 𝟙 Y, h, Presieve.ofArrows.mk (⟨Y, h, hh⟩ :
      Σ w : 𝒳.val.val.obj, {g : w ⟶ U // noetherianFlatSieve 𝒳 U g}), Category.id_comp h⟩
  · obtain ⟨w, g, y, hyaff, hnoeth, ⟨c⟩⟩ := i
    exact Stacks.SheafOfModules.FinitePresentationTransport.hasFiniteGlobalPresentation_overMap _ c
      (Stacks.SheafOfModules.hasFiniteGlobalPresentation_of_isFinitelyPresentedByGlobalSections
        (isFinitelyPresentedByGlobalSections_over_moduleLowerShriekU B S hS y _
          (isFinitelyPresentedByGlobalSections_restrictedModuleRestrictionAlong_kernel φ
            (isCartesianBetweenAffines_of_isQuasicoherentOnSite _ F hF.1.1)
            (isCartesianBetweenAffines_of_isQuasicoherentOnSite _ G hG.1.1) hF.1.2 y hyaff
            hnoeth)))

end Coherent

end FlatFppf

end AlgebraicGeometry.Stack

end
