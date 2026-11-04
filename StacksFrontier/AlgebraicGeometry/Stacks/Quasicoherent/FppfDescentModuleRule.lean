module

public import Mathlib.CategoryTheory.Limits.Shapes.SplitEqualizer
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuleSheafFunctoriality
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfModulesDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageFppfWeakSerre
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FppfLocalLifts
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveFlatFppfLocalSections

/-!
# Descent of a module rule along a covering 1-morphism (Stacks 06XE, 07AP, 07AQ)

Let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf site of a
scheme `S` whose image covers `𝒴` locally for a topology `τ`: every object of `𝒴` has a
`τ`-covering family whose members have sources isomorphic to objects `f x`. Write `f^*` for the
inverse image of sheaves of modules and `f_*` for the direct image (**Stacks 06WE**), and
`η : 1 ⟶ f_* f^*` for the unit. For every sheaf of modules `F` on `𝒴` the fork

`F ⟶ f_* f^* F ⇉ f_* f^* f_* f^* F`, with the two maps `f_* f^* η_F` and `η_{f_* f^* F}`,

is an equalizer. This is the exactness of the beginning of the relative Čech complex of
**Stacks 06XE**, in the form the source's proofs of **Stacks 07AP** and **Stacks 07AQ** part (2)
use it: a module rule closed under direct image along `f`, inverse image along `f` and
equalizers contains `F` as soon as it contains `f^* F`.

## Main results

* `CategoryTheory.Adjunction.isLimitForkUnit`: for an adjunction `L ⊣ R` whose left adjoint
  reflects isomorphisms and preserves equalizers, `X ⟶ R L X ⇉ R L R L X` is an equalizer.
* `AlgebraicGeometry.Stack.isIso_of_isIso_modulePullback_map`: the inverse image along a
  1-morphism with locally covering image reflects isomorphisms of sheaves of modules.
* `AlgebraicGeometry.Stack.isLimitForkModuleSheafAdjunctionUnit`: the equalizer above.
* `AlgebraicGeometry.Stack.exists_presieve_of_isSurjective_isFlat_isLocallyOfFinitePresentation`:
  a surjective, flat, locally finitely presented 1-morphism of algebraic stacks has locally
  covering image for the fppf topology (**Stacks 06QA**).
* `AlgebraicGeometry.Stack.AlgebraicStacks.ModuleRule.mem_of_mem_fppfModulePullback`: the descent
  step of the proofs of **Stacks 07AP** and **Stacks 07AQ** part (2), for a rule of
  `AlgebraicGeometry.Stack.AlgebraicStacks.ModuleRule`.
* `AlgebraicGeometry.Stack.mem_of_mem_fppfModulesPullback`: the same descent step at module
  universe `u`, through `AlgebraicGeometry.Stack.fppfModulesPullbackPushforwardAdjunction`.

## Implementation notes

The source writes the second term of the sequence as `b_* b^* F` with
`b : 𝒰 ×_𝒳 𝒰 ⟶ 𝒳`. The fork used here has `f_* f^* f_* f^* F` there instead, the second term of
the cobar construction of the adjunction. Its membership in a rule follows from closure under
`f_*` and `f^*` alone, so no 2-fibre product and no comparison of `b^*` with the inverse image
along a projection is needed. Exactness is proved formally: after applying `f^*` the fork is
split by the counit (`CategoryTheory.Adjunction.isSplitEqualizerMapUnit`), `f^*` preserves
equalizers because it is restriction of presheaves, and `f^*` reflects isomorphisms because a
map of sheaves which is bijective on the objects of a covering family is locally bijective.

## References

* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 06XE](https://stacks.math.columbia.edu/tag/06XE)
* [Stacks Project, Tag 06QA](https://stacks.math.columbia.edu/tag/06QA)
* [Stacks Project, Tag 07AP](https://stacks.math.columbia.edu/tag/07AP)
* [Stacks Project, Tag 07AQ](https://stacks.math.columbia.edu/tag/07AQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Adjunction

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L : D ⥤ C} {R : C ⥤ D} (adj : L ⊣ R)

/-- The unit `η` equalizes the two maps `R L η_X` and `η_{R L X}` out of `R L X`: this is the
naturality of `η` at `η_X`. -/
theorem unit_comp_map_map_unit (F : D) :
    adj.unit.app F ≫ R.map (L.map (adj.unit.app F)) =
      adj.unit.app F ≫ adj.unit.app (R.obj (L.obj F)) :=
  (adj.unit.naturality (adj.unit.app F)).symm

/-- After applying the left adjoint, the fork `X ⟶ R L X ⇉ R L R L X` is a split equalizer,
split by the counit at `L X` and at `L R L X`. -/
noncomputable def isSplitEqualizerMapUnit (F : D) :
    IsSplitEqualizer (L.map (R.map (L.map (adj.unit.app F))))
      (L.map (adj.unit.app (R.obj (L.obj F)))) (L.map (adj.unit.app F)) where
  leftRetraction := adj.counit.app (L.obj F)
  rightRetraction := adj.counit.app (L.obj (R.obj (L.obj F)))
  condition := by rw [← L.map_comp, ← L.map_comp, unit_comp_map_map_unit]
  ι_leftRetraction := adj.left_triangle_components F
  bottom_rightRetraction := adj.left_triangle_components (R.obj (L.obj F))
  top_rightRetraction := adj.counit.naturality (L.map (adj.unit.app F))

/-- For an adjunction `L ⊣ R` whose left adjoint reflects isomorphisms and preserves
equalizers, the fork `X ⟶ R L X ⇉ R L R L X` of the unit is an equalizer: its image under `L` is
split, hence a limit, and `L` reflects that limit. -/
noncomputable def isLimitForkUnit [HasEqualizers D] [L.ReflectsIsomorphisms]
    [PreservesLimitsOfShape WalkingParallelPair L] (F : D) :
    IsLimit (Fork.ofι (adj.unit.app F) (adj.unit_comp_map_map_unit F)) :=
  haveI : ReflectsLimitsOfShape WalkingParallelPair L :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  isLimitOfReflects L ((isLimitMapConeForkEquiv L _).symm
    (adj.isSplitEqualizerMapUnit F).isEqualizer)

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Stack

universe u v w m v' w'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)

/-- The inverse image of sheaves of modules along a 1-morphism preserves equalizers: on underlying
abelian presheaves it is precomposition, and the underlying abelian presheaf functor reflects
equalizers. -/
instance preservesLimitsOfShape_walkingParallelPair_modulePullback :
    PreservesLimitsOfShape WalkingParallelPair
      (modulePullback.{u, v, w, m, v', w'} B S hS p q hp hq f hf τ hτ) := by
  let G𝒴 := SheafOfModules.forget.{m} (ringStructureSheafCore B S hS q hq τ hτ) ⋙
    PresheafOfModules.toPresheaf _
  let G𝒳 := SheafOfModules.forget.{m} (ringStructureSheafCore B S hS p hp τ hτ) ⋙
    PresheafOfModules.toPresheaf _
  have e : G𝒴 ⋙ (Functor.whiskeringLeft _ _ _).obj f.op ≅
      modulePullback.{u, v, w, m, v', w'} B S hS p q hp hq f hf τ hτ ⋙ G𝒳 :=
    NatIso.ofComponents (fun _ => Iso.refl _)
  have : PreservesLimitsOfShape WalkingParallelPair
      (modulePullback.{u, v, w, m, v', w'} B S hS p q hp hq f hf τ hτ ⋙ G𝒳) :=
    preservesLimitsOfShape_of_natIso e
  exact preservesLimitsOfShape_of_reflects_of_preserves _ G𝒳

variable {p f} in
include hp hq hf in
/-- **The inverse image along a 1-morphism with locally covering image reflects isomorphisms.**
If every object of `𝒴` has a covering family whose members have sources isomorphic to images
under `f`, a map `φ` of sheaves of modules on `𝒴` whose inverse image is an isomorphism is an
isomorphism: it is bijective on sections over every image object, hence locally injective and
locally surjective, and a locally bijective map of sheaves is an isomorphism. -/
theorem isIso_of_isIso_modulePullback_map
    (hcover : ∀ y : 𝒴, ∃ R : Presieve y,
      Sieve.generate R ∈ associatedTopology B S hS q τ y ∧
        ∀ ⦃z : 𝒴⦄ (g : z ⟶ y), R g → ∃ x : 𝒳, Nonempty (z ≅ f.obj x))
    {F G : SheafOfModules.{m} (ringStructureSheafCore B S hS q hq τ hτ)} (φ : F ⟶ G)
    (hφ : IsIso ((modulePullback.{u, v, w, m, v', w'} B S hS p q hp hq f hf τ hτ).map φ)) :
    IsIso φ := by
  let P := (PresheafOfModules.toPresheaf _).map φ.val
  have hPx : ∀ x : 𝒳, IsIso (P.app (op (f.obj x))) := fun x => by
    set φ' := (modulePullback.{u, v, w, m, v', w'} B S hS p q hp hq f hf τ hτ).map φ
    have : IsIso φ'.val := Functor.map_isIso (SheafOfModules.forget _) φ'
    exact inferInstanceAs (IsIso (((PresheafOfModules.toPresheaf _).map φ'.val).app (op x)))
  have hbij : ∀ (z : 𝒴) (x : 𝒳), Nonempty (z ≅ f.obj x) →
      Function.Bijective (P.app (op z)) := by
    rintro z x ⟨e⟩
    have : IsIso (P.app (op z)) := by
      have : P.app (op z) = ((PresheafOfModules.toPresheaf _).obj F.val).map e.inv.op ≫
          P.app (op (f.obj x)) ≫ ((PresheafOfModules.toPresheaf _).obj G.val).map e.hom.op := by
        rw [P.naturality_assoc, ← Functor.map_comp, ← op_comp, e.hom_inv_id, op_id,
          CategoryTheory.Functor.map_id, Category.comp_id]
      rw [this]
      have := hPx x
      infer_instance
    exact ConcreteCategory.bijective_of_isIso (P.app (op z))
  have hloc : ∀ (U : 𝒴) (T : Sieve U),
      (∀ ⦃z : 𝒴⦄ (g : z ⟶ U), Function.Bijective (P.app (op z)) → T g) →
        T ∈ associatedTopology B S hS q τ U := fun U T hT => by
    obtain ⟨R, hR, hRiso⟩ := hcover U
    refine (associatedTopology B S hS q τ).superset_covering ?_ hR
    rw [Sieve.generate_le_iff]
    intro z g hg
    obtain ⟨x, hx⟩ := hRiso g hg
    exact hT g (hbij z x hx)
  have hinj : Presheaf.IsLocallyInjective (associatedTopology B S hS q τ) P := by
    refine ⟨fun {X} s t hst => hloc X.unop _ fun z g hz => ?_⟩
    apply hz.1
    have h := congrArg (((PresheafOfModules.toPresheaf _).obj G.val).map g.op) hst
    rwa [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, ← P.naturality] at h
  have hsurj : Presheaf.IsLocallySurjective (associatedTopology B S hS q τ) P :=
    ⟨fun {U} t => hloc U _ fun z g hz => hz.2 _⟩
  have : IsIso ((SheafOfModules.toSheaf _).map φ) :=
    (Sheaf.isLocallyBijective_iff_isIso ((SheafOfModules.toSheaf _).map φ)).1 ⟨hinj, hsurj⟩
  have : IsIso P := inferInstanceAs (IsIso ((sheafToPresheaf _ _).map
    ((SheafOfModules.toSheaf _).map φ)))
  have : IsIso φ.val := isIso_of_reflects_iso φ.val (PresheafOfModules.toPresheaf _)
  have : IsIso ((SheafOfModules.forget _).map φ) := this
  exact isIso_of_reflects_iso φ (SheafOfModules.forget _)

variable {p f} in
include hp hq hf in
/-- The inverse image along a 1-morphism with locally covering image reflects isomorphisms. -/
theorem reflectsIsomorphisms_modulePullback
    (hcover : ∀ y : 𝒴, ∃ R : Presieve y,
      Sieve.generate R ∈ associatedTopology B S hS q τ y ∧
        ∀ ⦃z : 𝒴⦄ (g : z ⟶ y), R g → ∃ x : 𝒳, Nonempty (z ≅ f.obj x)) :
    (modulePullback.{u, v, w, m, v', w'} B S hS p q hp hq f hf τ hτ).ReflectsIsomorphisms :=
  ⟨fun φ hφ => isIso_of_isIso_modulePullback_map B S hS q hp hq hf τ hτ hcover φ hφ⟩

variable {p f} in
/-- **Stacks 06XE, the beginning of the relative Čech complex, for sheaves of modules.** For a
1-morphism `f` with locally covering image and a sheaf of modules `F` on `𝒴`, the unit
`F ⟶ f_* f^* F` is the equalizer of `f_* f^* η_F` and `η_{f_* f^* F}`. -/
noncomputable def isLimitForkModuleSheafAdjunctionUnit
    (hcover : ∀ y : 𝒴, ∃ R : Presieve y,
      Sieve.generate R ∈ associatedTopology B S hS q τ y ∧
        ∀ ⦃z : 𝒴⦄ (g : z ⟶ y), R g → ∃ x : 𝒳, Nonempty (z ≅ f.obj x))
    (F : SheafOfModules.{max u v w m v' w'} (ringStructureSheafCore B S hS q hq τ hτ)) :
    IsLimit (Fork.ofι _ (Adjunction.unit_comp_map_map_unit
      (moduleSheafAdjunction.{u, v, w, m, v', w'} B S hS p q hp hq f hf τ hτ) F)) :=
  haveI := reflectsIsomorphisms_modulePullback.{u, v, w, max u v w m v' w', v', w'}
    B S hS q hp hq hf τ hτ hcover
  (moduleSheafAdjunction.{u, v, w, m, v', w'} B S hS p q hp hq f hf τ hτ).isLimitForkUnit F

section AlgebraicStacks

universe t

variable {B S hS}

/-- A surjective, flat, locally finitely presented 1-morphism `a : 𝒰 ⟶ 𝒳` of algebraic stacks
has locally covering image for the fppf topology: every object of `𝒳` has an fppf covering
family whose members have sources isomorphic to objects `a x`. This is **Stacks 06QA** read on
the fppf site of `𝒳`. -/
theorem exists_presieve_of_isSurjective_isFlat_isLocallyOfFinitePresentation
    {𝒰 𝒳 : AlgebraicStacks.{u, t} B S hS} (a : 𝒰 ⟶ 𝒳) (hsurj : IsSurjective B S hS a)
    (hflat : AlgebraicStacks.IsFlat B S hS a)
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS a) (y : 𝒳.val.val.obj) :
    ∃ R : Presieve y,
      Sieve.generate R ∈ associatedTopology B S hS 𝒳.val.val.p B.topology y ∧
        ∀ ⦃z : 𝒳.val.val.obj⦄ (g : z ⟶ y), R g →
          ∃ x : 𝒰.val.val.obj, Nonempty (z ≅ (CatFiberedInGroupoids.homFunctor a.hom).obj x) := by
  have hX := 𝒳.val.isFiberedInGroupoids
  have : 𝒳.val.val.p.IsFibered := hX.isFibered
  obtain ⟨R₀, hR₀, hlift⟩ := exists_fppfCovering_fibre_lift B S hS a hsurj hflat hlfp
    (𝒳.val.val.p.obj y) ⟨y, rfl⟩
  refine ⟨fun z _ => ∃ x : 𝒰.val.val.obj,
    Nonempty (z ≅ (CatFiberedInGroupoids.homFunctor a.hom).obj x), ?_, fun _ _ h => h⟩
  refine (associatedTopology B S hS 𝒳.val.val.p B.topology).superset_covering ?_
    (𝒳.val.val.p.functorPullback_mem_inheritedTopology _ y hR₀)
  intro z g hg
  obtain ⟨x, α, hα⟩ := hlift (k := 𝒳.val.val.p.map g) hg
  have : 𝒳.val.val.p.IsStronglyCartesian (𝒳.val.val.p.map g) α :=
    Functor.IsFiberedInGroupoids.isStronglyCartesian_homLift hX _ α
  exact ⟨_, Functor.IsStronglyCartesian.map 𝒳.val.val.p (𝒳.val.val.p.map g) α
      (g := 𝟙 _) (Category.id_comp _).symm g, α, ⟨x, ⟨Iso.refl _⟩⟩,
    Functor.IsStronglyCartesian.fac 𝒳.val.val.p (𝒳.val.val.p.map g) α _ g⟩

/-- **The descent step of Stacks 07AP and Stacks 07AQ part (2).** Let `M` be a rule assigning to
every algebraic stack a class of modules on its fppf site, and let `a : 𝒰 ⟶ 𝒳` be a 1-morphism
with locally covering image. If `M` is closed under inverse image along `a`, under direct image
along `a` and under equalizers on `𝒳`, then every module `F` on `𝒳` with `a^* F` in `M` is in
`M`. -/
theorem AlgebraicStacks.ModuleRule.mem_of_mem_fppfModulePullback
    (M : AlgebraicStacks.ModuleRule.{u, t} B S hS) {𝒰 𝒳 : AlgebraicStacks.{u, t} B S hS}
    (a : 𝒰 ⟶ 𝒳)
    (hcover : ∀ y : 𝒳.val.val.obj, ∃ R : Presieve y,
      Sieve.generate R ∈ associatedTopology B S hS 𝒳.val.val.p B.topology y ∧
        ∀ ⦃z : 𝒳.val.val.obj⦄ (g : z ⟶ y), R g →
          ∃ x : 𝒰.val.val.obj, Nonempty (z ≅ (CatFiberedInGroupoids.homFunctor a.hom).obj x))
    (hpull : ∀ G, M 𝒳 G → M 𝒰 ((AlgebraicStacks.fppfModulePullback B S hS a).obj G))
    (hpush : ∀ G, M 𝒰 G → M 𝒳 ((moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS
      𝒰.val.val.p 𝒳.val.val.p 𝒰.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor a.hom) (CatFiberedInGroupoids.homFunctor_comp_p a.hom)
      B.topology le_rfl).obj G))
    (heq : ∀ {G₁ G₂ K : AlgebraicStacks.fppfModules B S hS 𝒳} (g h : G₁ ⟶ G₂) (ι : K ⟶ G₁)
      (w : ι ≫ g = ι ≫ h), IsLimit (Fork.ofι ι w) → M 𝒳 G₁ → M 𝒳 G₂ → M 𝒳 K)
    (F : AlgebraicStacks.fppfModules B S hS 𝒳)
    (hF : M 𝒰 ((AlgebraicStacks.fppfModulePullback B S hS a).obj F)) : M 𝒳 F :=
  heq _ _ _ _ (isLimitForkModuleSheafAdjunctionUnit.{u, u + 1, u, u, u + 1, u} B S hS
      𝒳.val.val.p 𝒰.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor_comp_p a.hom) B.topology le_rfl hcover F)
    (hpush _ hF) (hpush _ (hpull _ (hpush _ hF)))

/-- **The descent step of Stacks 07AP and Stacks 07AQ part (2), at module universe `u`.** Let
`M` assign to every algebraic stack a class of modules on its fppf site with sections in `u`,
and let `a : 𝒰 ⟶ 𝒳` be a 1-morphism with locally covering image. If `M` is closed under the
inverse image `AlgebraicGeometry.Stack.fppfModulesPullback` along `a`, under the direct image
`AlgebraicGeometry.Stack.fppfModulesPushforward` along `a` and under equalizers on `𝒳`, then
every module `F` on `𝒳` with `a^* F` in `M` is in `M`. -/
theorem mem_of_mem_fppfModulesPullback
    (M : ∀ 𝒳 : AlgebraicStacks.{u, t} B S hS, ObjectProperty (fppfModules B S hS 𝒳))
    {𝒰 𝒳 : AlgebraicStacks.{u, t} B S hS} (a : 𝒰 ⟶ 𝒳)
    (hcover : ∀ y : 𝒳.val.val.obj, ∃ R : Presieve y,
      Sieve.generate R ∈ associatedTopology B S hS 𝒳.val.val.p B.topology y ∧
        ∀ ⦃z : 𝒳.val.val.obj⦄ (g : z ⟶ y), R g →
          ∃ x : 𝒰.val.val.obj, Nonempty (z ≅ (CatFiberedInGroupoids.homFunctor a.hom).obj x))
    (hpull : ∀ G, M 𝒳 G → M 𝒰 ((fppfModulesPullback B S hS a).obj G))
    (hpush : ∀ G, M 𝒰 G → M 𝒳 ((fppfModulesPushforward B S hS a).obj G))
    (heq : ∀ {G₁ G₂ K : fppfModules B S hS 𝒳} (g h : G₁ ⟶ G₂) (ι : K ⟶ G₁)
      (w : ι ≫ g = ι ≫ h), IsLimit (Fork.ofι ι w) → M 𝒳 G₁ → M 𝒳 G₂ → M 𝒳 K)
    (F : fppfModules B S hS 𝒳) (hF : M 𝒰 ((fppfModulesPullback B S hS a).obj F)) : M 𝒳 F :=
  have : (fppfModulesPullback B S hS a).ReflectsIsomorphisms :=
    reflectsIsomorphisms_modulePullback.{u, u + 1, u, u, u + 1, u} B S hS 𝒳.val.val.p
      𝒰.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor_comp_p a.hom) B.topology le_rfl hcover
  have : PreservesLimitsOfShape WalkingParallelPair (fppfModulesPullback B S hS a) :=
    preservesLimitsOfShape_walkingParallelPair_modulePullback.{u, u + 1, u, u, u + 1, u} B S hS
      𝒰.val.val.p 𝒳.val.val.p 𝒰.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor a.hom) (CatFiberedInGroupoids.homFunctor_comp_p a.hom)
      B.topology le_rfl
  heq _ _ _ _ ((fppfModulesPullbackPushforwardAdjunction B S hS a).isLimitForkUnit F)
    (hpush _ hF) (hpush _ (hpull _ (hpush _ hF)))

end AlgebraicStacks

end AlgebraicGeometry.Stack
