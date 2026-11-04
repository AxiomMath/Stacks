module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekGlobalPresentationOfTerminal
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfModuleDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfModuleLowerShriekLargeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreEssentialSmallness
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatObjectAtlasCovers
public import StacksFrontier.AlgebraicGeometry.Stacks.ObjectStackMapSlicePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStackTerminalSubsite
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalChartSmoothBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.JointlySurjectiveDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentModuleUniverse

/-!
# Stacks 07B0 (2) at module universe `u + 1`: `g_!` preserves quasi-coherence

Let `𝒳` be an algebraic stack and `g : Sh(𝒳_{flat,fppf}) ⟶ Sh(𝒳_{fppf})` the morphism of ringed
topoi of **Stacks 0788** (2). **Stacks 07B0** (2) says that for a quasi-coherent module `ℋ` on
the flat-fppf site, `g_!ℋ` is a quasi-coherent module on `𝒳`. This file proves it at module
universe `u + 1` — sections one universe above the structure sheaf, the universe of the derived
direct image of **Stacks 07BC** and of the coherator of **Stacks 0778** — with no hypothesis.

The proof is the source's. Quasi-coherence is local, so it is enough to present `g_!ℋ` globally
over the flat objects `z` over which `ℋ` has a global presentation, and those cover the site.
For such a `z`, lying over the scheme `U`, let `f : (Sch/U) ⟶ 𝒳` be the flat 1-morphism `z` names
and `f'` its restriction to the flat-fppf sites.

* `f^{-1} g_! ℋ = g'_! (f')^{-1} ℋ` (the underived form of **Stacks 07AV**'s second identity,
  `AlgebraicGeometry.Stack.FlatFppf.moduleLowerShriekSuccBaseChangeIso`): it is the conjugate of
  the exchange `f_* g^* = (g')^* f'_*` of **Stacks 07AT** (2) across the four adjunctions.
* `(f')^{-1} ℋ` has a global presentation, the flat-fppf site of `(Sch/U)` having the final object
  `U/U` carried to an object mapping to `z`
  (`Stacks.SheafOfModules.hasGlobalPresentation_pushforward_of_isTerminal_succ`).
* `g'_!` carries it to a module with a global presentation, because `U/U` is final in both sites
  of `(Sch/U)`, so that `g'_! O = O` (the step "Lemma 078A shows that `g_!O = O_𝒳`" of the
  source; `Stacks.SheafOfModules.hasGlobalPresentation_lowerShriek_of_isTerminal`).
* a global presentation of `f^{-1}(g_!ℋ)` over `U/U` is one of `g_!ℋ` over `f(U/U) ≅ z`.

## Main results

* `AlgebraicGeometry.Stack.FlatFppf.moduleLowerShriekSuccBaseChangeIso`.
* `AlgebraicGeometry.Stack.FlatFppf.isQuasicoherentOnSite_moduleLowerShriekSucc`:
  **Stacks 07B0** (2) at module universe `u + 1`.

## References

* [Stacks Project, Tag 07B0](https://stacks.math.columbia.edu/tag/07B0)
* [Stacks Project, Tag 07AT](https://stacks.math.columbia.edu/tag/07AT)
* [Stacks Project, Tag 07AV](https://stacks.math.columbia.edu/tag/07AV)
* [Stacks Project, Tag 078A](https://stacks.math.columbia.edu/tag/078A)
* [Stacks Project, Tag 07AZ](https://stacks.math.columbia.edu/tag/07AZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.SheafOfModules

namespace AlgebraicGeometry.Stack

universe u w

/-- **A global presentation of the inverse image descends to the image object**, at module
universe `u + 1`. Let `F : 𝒵 ⥤ 𝒳` be a 1-morphism of categories fibred in groupoids over the big
fppf category of `S` and `M` a sheaf of modules on `𝒳` with sections in `Type (u + 1)`. If the
restriction of `F^{-1}M` to the slice at `z` has a global presentation, so does the restriction
of `M` to the slice at `F z`: the slice `𝒵/z ⥤ 𝒳/F z` is an equivalence of sites
(**Stacks 06W0**), and reindexing along an equivalence of sites reflects global presentations
at any module universe (`Stacks.SheafOfModules.hasGlobalPresentation_of_reindex'`). This is
`AlgebraicGeometry.Stack.hasGlobalPresentation_of_modulePullback` one module universe up. -/
theorem hasGlobalPresentation_over_of_modulePullbackSucc (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {𝒵 : Type (u + 1)} [Category.{u} 𝒵] {𝒳 : Type (u + 1)} [Category.{u} 𝒳]
    (p : 𝒵 ⥤ BigFppfOver B S hS) (q : 𝒳 ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (F : 𝒵 ⥤ 𝒳) (hF : F ⋙ q = p)
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
    (M : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS q hq τ hτ)) (z : 𝒵)
    (h : (((modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS p q hp hq F hF τ hτ).obj
      M).over z).HasGlobalPresentation) :
    (M.over (F.obj z)).HasGlobalPresentation := by
  subst hF
  have hfibq : q.IsFibered := hq.isFibered
  have hfibp : (F ⋙ q).IsFibered := hp.isFibered
  have hone : (F ⋙ q).IsFibredOneMorphism q F := hq.isFibredOneMorphism rfl
  obtain ⟨hcont, hcocont⟩ : F.IsContinuous (associatedTopology B S hS (F ⋙ q) τ)
      (associatedTopology B S hS q τ) ∧ F.IsCocontinuous (associatedTopology B S hS (F ⋙ q) τ)
      (associatedTopology B S hS q τ) :=
    hone.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))
  have hsl : (Over.post (X := z) F).IsEquivalence := by
    have h₁ : (Over.post (X := F.obj z) (q ⋙ Over.forget (B.obj hS))).IsEquivalence :=
      isEquivalence_overPost B S hS q hq (F.obj z)
    have h₂ : (Over.post (X := z) F ⋙
        Over.post (q ⋙ Over.forget (B.obj hS))).IsEquivalence := by
      rw [← Over.post_comp]
      exact isEquivalence_overPost B S hS (F ⋙ q) hp z
    exact Functor.isEquivalence_of_comp_right (Over.post (X := z) F)
      (Over.post (q ⋙ Over.forget (B.obj hS)))
  let e : Over z ≌ Over (F.obj z) := (Over.post (X := z) F).asEquivalence
  have hec : e.functor.IsContinuous ((associatedTopology B S hS (F ⋙ q) τ).over z)
      ((associatedTopology B S hS q τ).over (F.obj z)) :=
    Functor.isContinuous_overPost _ _ F z
  have hecc : e.functor.IsCocontinuous ((associatedTopology B S hS (F ⋙ q) τ).over z)
      ((associatedTopology B S hS q τ).over (F.obj z)) :=
    inferInstanceAs ((Over.post (X := z) F).IsCocontinuous
      ((associatedTopology B S hS (F ⋙ q) τ).over z)
      ((associatedTopology B S hS q τ).over (F.obj z)))
  have hei : e.inverse.IsContinuous ((associatedTopology B S hS q τ).over (F.obj z))
      ((associatedTopology B S hS (F ⋙ q) τ).over z) :=
    e.toAdjunction.isContinuous_of_isCocontinuous _ _
  exact Stacks.SheafOfModules.hasGlobalPresentation_of_reindex'
    (J := (associatedTopology B S hS q τ).over (F.obj z))
    (J' := (associatedTopology B S hS (F ⋙ q) τ).over z) e
    ((ringStructureSheafCore B S hS q hq τ hτ).over (F.obj z)) (M.over (F.obj z)) h

namespace FlatFppf

attribute [local instance] GrothendieckTopology.hasSheafify_addCommGrpCat
  GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat
  isContinuous_inclusion_topology isCocontinuous_inclusion_topology
  AlgebraicGeometry.Stack.instHasPointwiseRightKanExtensionRingCat
  AlgebraicGeometry.Stack.instHasPointwiseRightKanExtensionAddCommGrpCat

section BaseChange

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
  (hf : AlgebraicStacks.IsFlat B S hS f)

/-- **The underived base change of the lower shriek along a flat 1-morphism**, at module
universe `u + 1`: `f^{-1} ∘ g_! ≅ g'_! ∘ (f')^{-1}`, i.e. `g_! ⋙ f^{-1} ≅ (f')^{-1} ⋙ g'_!`. It is
the conjugate, across `g_! ⊣ g^*`, `f^{-1} ⊣ f_*` and their primed versions, of the exchange
`f_* ∘ g^* ≅ (g')^* ∘ f'_*` of **Stacks 07AT** (2)
(`AlgebraicGeometry.Stack.FlatFppf.isIso_moduleSquareComparison`). -/
def moduleLowerShriekSuccBaseChangeIso :
    moduleLowerShriekSucc B S hS 𝒴 ⋙
        AlgebraicGeometry.Stack.modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS 𝒳.val.val.p
          𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids f.hom.hom.toFunctor
          f.hom.hom.w B.topology le_rfl ≅
      moduleSubsiteInverseImage B S hS f hf ⋙ moduleLowerShriekSucc B S hS 𝒳 :=
  haveI := (isContinuous_and_isCocontinuous_homFunctor B S hS f).2
  haveI := isCocontinuous_subsiteFunctor_topology B S hS f hf
  haveI := isIso_moduleSquareComparison B S hS f hf
  (conjugateIsoEquiv ((moduleSubsiteInverseImageAdjunction B S hS f hf).comp
      (moduleLowerShriekSuccAdjunction B S hS 𝒳))
    ((moduleLowerShriekSuccAdjunction B S hS 𝒴).comp
      (modulePullbackPushforwardAdjunction B S hS f))).symm
    (asIso (squareComparison (J' := topology B S hS 𝒳) (K' := topology B S hS 𝒴)
      (structureMapHomFunctor B S hS B.topology le_rfl f)
      (primedSiteFunctor_comp_ι B S hS f hf))).symm

end BaseChange

section Presentation

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

/-- The chosen cartesian arrow from the image of the final object `U/U` under the 1-morphism
`y : (Sch/U) ⟶ 𝒳` to `y` lies over the identity of `U`, hence is an isomorphism. -/
theorem isIso_primedSiteFunctorTerminalHom_hom (z : FlatFppf B S hS 𝒳) :
    IsIso (primedSiteFunctorTerminalHom B S hS 𝒳 z).hom := by
  show IsIso (Functor.TwoYoneda.chosenLift 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    (𝒳.val.val.p.obj z.obj) (Functor.Fiber.mk (a := z.obj) rfl) (Over.mk (𝟙 _))).φ
  have : IsIso (Over.mk (𝟙 (𝒳.val.val.p.obj z.obj))).hom :=
    inferInstanceAs (IsIso (𝟙 (𝒳.val.val.p.obj z.obj)))
  exact Functor.IsStronglyCartesian.isIso_of_base_isIso 𝒳.val.val.p
    (f := (Over.mk (𝟙 (𝒳.val.val.p.obj z.obj))).hom)
    (Functor.TwoYoneda.chosenLift 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      (𝒳.val.val.p.obj z.obj) (Functor.Fiber.mk (a := z.obj) rfl) (Over.mk (𝟙 _))).φ

/-- **`g_!ℋ` has a global presentation over every flat object over which `ℋ` has one**, at
module universe `u + 1`. With `f : (Sch/U) ⟶ 𝒳` the flat 1-morphism `z` names:
`(f')^{-1}ℋ` is globally presented on the flat-fppf site of `(Sch/U)`, which has the final object
`U/U` over `z`; `g'_!` carries it to a globally presented module, `U/U` being final in both sites
of `(Sch/U)`; that module is `f^{-1}g_!ℋ`; and its presentation over `U/U` is one of `g_!ℋ` over
`f(U/U) ≅ z`. -/
theorem hasGlobalPresentation_over_moduleLowerShriekSucc (z : FlatFppf B S hS 𝒳)
    (H : SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳))
    (hH : (H.over z).HasGlobalPresentation) :
    (((moduleLowerShriekSucc B S hS 𝒳).obj H).over z.obj).HasGlobalPresentation := by
  let f := objectStackMap B S hS 𝒳 z.obj
  have hf : AlgebraicStacks.IsFlat B S hS f := z.property
  let T := 𝒳.val.val.p.obj z.obj
  let 𝒯 := schemeStack.{u, w} B S hS T
  let e' : FlatFppf B S hS 𝒯 := ⟨Over.mk (𝟙 T), flatObject_schemeStack_id.{u, w} B S hS T⟩
  have he' : IsTerminal e' := isTerminalFlatObjectSchemeStackId.{u, w} B S hS T
  have hC : ((moduleSubsiteInverseImage B S hS f hf).obj H).HasGlobalPresentation := by
    have := isContinuous_subsiteFunctor_topology B S hS f hf
    have := isCocontinuous_subsiteFunctor_topology B S hS f hf
    exact Stacks.SheafOfModules.hasGlobalPresentation_pushforward_of_isTerminal_succ
      (subsiteRingStructureSheaf B S hS 𝒳) he' (primedSiteFunctor B S hS f hf) z
      (primedSiteFunctorTerminalHom B S hS 𝒳 z)
      (eqToHom (subsiteRingStructureSheaf_inverseImageRing B S hS f hf).symm) H hH
  have hD : ((moduleLowerShriekSucc B S hS 𝒯).obj
      ((moduleSubsiteInverseImage B S hS f hf).obj H)).HasGlobalPresentation := by
    have := isContinuous_inclusion_topology B S hS 𝒯
    have := isCocontinuous_inclusion_topology B S hS 𝒯
    have : EssentiallySmall.{u} 𝒯.val.val.obj := essentiallySmall_obj_algebraicStack B S hS 𝒯
    have : HasSheafify (topology B S hS 𝒯) AddCommGrpCat.{u} := hasSheafify_addCommGrpCat B S hS 𝒯
    have : (topology B S hS 𝒯).WEqualsLocallyBijective AddCommGrpCat.{u} :=
      wEqualsLocallyBijective_addCommGrpCat B S hS 𝒯
    have : HasSheafify (associatedTopology B S hS 𝒯.val.val.p B.topology) AddCommGrpCat.{u} :=
      hasSheafifyEssentiallySmallSite.{u, u, u + 1, u + 1, u} _ _
    have : (associatedTopology B S hS 𝒯.val.val.p B.topology).WEqualsLocallyBijective
        AddCommGrpCat.{u} :=
      GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u, u + 1, u + 1, u} _
    exact Stacks.SheafOfModules.hasGlobalPresentation_lowerShriek_of_isTerminal
      (topology B S hS 𝒯) (associatedTopology B S hS 𝒯.val.val.p B.topology)
      (objectProperty B S hS 𝒯).ι (ambientRingStructureSheaf B S hS 𝒯) he' Over.mkIdTerminal _ hC
  have hE : ((AlgebraicGeometry.Stack.modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS
      𝒯.val.val.p 𝒳.val.val.p 𝒯.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
      f.hom.hom.toFunctor f.hom.hom.w B.topology le_rfl).obj
        ((moduleLowerShriekSucc B S hS 𝒳).obj H)).HasGlobalPresentation :=
    SheafOfModules.HasGlobalPresentation.of_iso
      ((moduleLowerShriekSuccBaseChangeIso B S hS f hf).app H).symm hD
  have := isIso_primedSiteFunctorTerminalHom_hom B S hS 𝒳 z
  exact Stacks.SheafOfModules.hasGlobalPresentation_overMap _
    (inv (primedSiteFunctorTerminalHom B S hS 𝒳 z).hom)
    (hasGlobalPresentation_over_of_modulePullbackSucc B S hS 𝒯.val.val.p 𝒳.val.val.p
      𝒯.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids f.hom.hom.toFunctor f.hom.hom.w
      B.topology le_rfl ((moduleLowerShriekSucc B S hS 𝒳).obj H) (Over.mk (𝟙 T))
      (Stacks.SheafOfModules.hasGlobalPresentation_over _ _ hE))

/-- **Stacks 07B0 (2) at module universe `u + 1`.** Let `𝒳` be an algebraic stack and `ℋ` a
quasi-coherent module on the flat-fppf site of `𝒳`, with sections in `Type (u + 1)`. Then
`g_!ℋ` is a quasi-coherent module on `𝒳`.

Quasi-coherence is local: it is enough that for every object `x` the arrows into `x` from objects
over which `g_!ℋ` is globally presented cover `x`. The flat objects over which `ℋ` is globally
presented cover the site (`ℋ` being quasi-coherent, and the flat objects covering every object),
and over each of them `g_!ℋ` is globally presented
(`AlgebraicGeometry.Stack.FlatFppf.hasGlobalPresentation_over_moduleLowerShriekSucc`). -/
theorem isQuasicoherentOnSite_moduleLowerShriekSucc
    (H : SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳))
    (hH : H.IsQuasicoherentOnSite) :
    ((moduleLowerShriekSucc B S hS 𝒳).obj H).IsQuasicoherentOnSite := by
  let M := (moduleLowerShriekSucc B S hS 𝒳).obj H
  let P : 𝒳.val.val.obj → Prop := fun z =>
    ∃ hz : flatObject B S hS 𝒳.val z, (H.over ⟨z, hz⟩).HasGlobalPresentation
  have hP : ∀ x, flatObject B S hS 𝒳.val x →
      Sieve.ofObjects (fun z : {z // flatObject B S hS 𝒳.val z ∧ P z} => z.1) x ∈
        AlgebraicGeometry.Stack.fppfTopology B S hS 𝒳.val x := by
    intro x hx
    obtain ⟨I, V, g, hcov, hpres⟩ := hH.locally_hasGlobalPresentation ⟨x, hx⟩
    refine (AlgebraicGeometry.Stack.fppfTopology B S hS 𝒳.val).superset_covering ?_
      ((CoverPreserving.of_isContinuous (objectProperty B S hS 𝒳).ι (topology B S hS 𝒳)
        (associatedTopology B S hS 𝒳.val.val.p B.topology)).cover_preserve hcov)
    rintro W k ⟨A, d, c, hd, rfl⟩
    obtain ⟨i, b, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hd
    exact (Sieve.mem_ofObjects_iff _ _).2
      ⟨⟨(V i).obj, (V i).property, (V i).property,
        Stacks.SheafOfModules.hasGlobalPresentation_overMap H (𝟙 (V i)) (hpres i)⟩,
        ⟨c ≫ (objectProperty B S hS 𝒳).ι.map b⟩⟩
  refine Stacks.SheafOfModules.isQuasicoherentOnSite_of_presentedSieve_mem M fun x => ?_
  refine (AlgebraicGeometry.Stack.fppfTopology B S hS 𝒳.val).transitive
    (coversTop_flatObject_of_local B S hS 𝒳 P hP x) _ fun y m hm => ?_
  obtain ⟨⟨z, hzP⟩, ⟨c⟩⟩ := (Sieve.mem_ofObjects_iff _ _).1 hm
  obtain ⟨hz, hpz⟩ := hzP.2
  rw [Stacks.SheafOfModules.presentedSieve_pullback]
  exact Stacks.SheafOfModules.presentedSieve_mem_of_hom M c
    ((AlgebraicGeometry.Stack.fppfTopology B S hS 𝒳.val).superset_covering
      (fun W g _ => Stacks.SheafOfModules.hasGlobalPresentation_overMap M g
        (hasGlobalPresentation_over_moduleLowerShriekSucc B S hS 𝒳 ⟨z, hz⟩ H hpz))
      ((AlgebraicGeometry.Stack.fppfTopology B S hS 𝒳.val).top_mem z))

end Presentation

end AlgebraicGeometry.Stack.FlatFppf
