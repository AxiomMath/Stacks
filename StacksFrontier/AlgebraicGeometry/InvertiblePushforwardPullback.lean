module

public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.SectionGenerator
public import StacksFrontier.AlgebraicGeometry.Divisors.NonvanishingLocusRestrict
public import StacksFrontier.AlgebraicGeometry.TwistPullbackRatio.Comparison
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjModuleBaseChangeIso
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.StalkBasisGenericPoint
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleQuotients.Basic

/-!
# Pulling back and pushing forward an invertible module along `𝒪_Y ≅ f_* 𝒪_X`

Let `f : X ⟶ Y` be a morphism of schemes for which the comorphism `𝒪_Y ⟶ f_* 𝒪_X` is an
isomorphism. Then for every invertible `𝒪_Y`-module `𝒜` the unit `𝒜 ⟶ f_* f^* 𝒜` of the
adjunction `f^* ⊣ f_*` is an isomorphism. Consequently `f^*` is injective on isomorphism classes of
invertible modules, and the pullback `Pic(Y) ⟶ Pic(X)` is injective.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isIso_restrictFunctor_map_of_bijective_smul`: a morphism of
  `𝒪_Y`-modules is an isomorphism over an open subscheme as soon as, near every point of it, some
  local section `a` of the source and its image both generate the sections over every smaller open.
* `AlgebraicGeometry.Scheme.Modules.isIso_unit_app_of_isIso_c`: the unit `𝒜 ⟶ f_* f^* 𝒜` is an
  isomorphism for `𝒜` invertible and `𝒪_Y ⟶ f_* 𝒪_X` an isomorphism.
* `AlgebraicGeometry.Scheme.Modules.nonempty_iso_of_pullback_iso_of_isIso_c`: `f^*` reflects
  isomorphy of invertible modules.
* `AlgebraicGeometry.Scheme.Modules.injective_schemePullbackClass_of_isIso_c`: the pullback on
  Picard groups is injective.

## References

* [Stacks Project, Tag 0C5L](https://stacks.math.columbia.edu/tag/0C5L)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Let `φ : 𝒜 ⟶ ℬ` be a morphism of `𝒪_Y`-modules and `f : Z ⟶ Y` an open immersion. Suppose every
point of `Z` lies over an open `K ⊆ f(Z)` carrying a section `a` of `𝒜` such that, over every open
`W ⊆ K`, both `c ↦ c • a|_W` and `c ↦ c • φ(a)|_W` are bijections out of `𝒪_Y(W)`. Then the
restriction of `φ` to `Z` is an isomorphism. -/
public theorem isIso_restrictFunctor_map_of_bijective_smul {Y Z : Scheme.{u}} (f : Z ⟶ Y)
    [IsOpenImmersion f] {A B : Y.Modules} (φ : A ⟶ B)
    (h : ∀ z : Z, ∃ (K : Y.Opens) (_ : f.base z ∈ K) (_ : K ≤ f.opensRange) (a : Γ(A, K)),
      ∀ (W : Y.Opens) (hW : W ≤ K),
        Function.Bijective (fun c : Γ(Y, W) => c • A.presheaf.map (homOfLE hW).op a) ∧
        Function.Bijective (fun c : Γ(Y, W) => c • B.presheaf.map (homOfLE hW).op (φ.app K a))) :
    IsIso ((restrictFunctor f).map φ) := by
  choose K hzK hKf a ha using h
  refine isIso_of_isIso_restrictFunctor_map _ (fun z => (f ⁻¹ᵁ K z).ι)
    (fun z => ⟨z, ⟨z, hzK z⟩, rfl⟩) fun z => ?_
  set g := (f ⁻¹ᵁ K z).ι
  have key : IsIso ((restrictFunctor (g ≫ f)).map φ) := by
    rw [Hom.isIso_iff_isIso_app]
    intro U
    have hW : (g ≫ f) ''ᵁ U ≤ K z := by
      rintro _ ⟨w, -, rfl⟩
      exact w.2
    obtain ⟨hp, hq⟩ := ha z _ hW
    show IsIso (φ.app ((g ≫ f) ''ᵁ U))
    rw [ConcreteCategory.isIso_iff_bijective]
    refine (Function.Bijective.of_comp_iff _ hp).mp ?_
    convert hq using 1
    funext c
    show φ.app _ (c • A.presheaf.map (homOfLE hW).op (a z)) = _
    rw [Hom.app_smul]
    congr 1
    exact PresheafOfModules.naturality_apply φ.val (homOfLE hW).op (a z)
  exact (NatIso.isIso_map_iff (restrictFunctorComp g f) φ).mp key

/-- Let `φ : 𝒜 ⟶ ℬ` be a morphism of `𝒪_Y`-modules. Suppose every point of `Y` lies in an open `K`
carrying a section `a` of `𝒜` such that, over every open `W ⊆ K`, both `c ↦ c • a|_W` and
`c ↦ c • φ(a)|_W` are bijections out of `𝒪_Y(W)`. Then `φ` is an isomorphism. -/
public theorem isIso_of_bijective_smul {Y : Scheme.{u}} {A B : Y.Modules} (φ : A ⟶ B)
    (h : ∀ y : Y, ∃ (K : Y.Opens) (_ : y ∈ K) (a : Γ(A, K)),
      ∀ (W : Y.Opens) (hW : W ≤ K),
        Function.Bijective (fun c : Γ(Y, W) => c • A.presheaf.map (homOfLE hW).op a) ∧
        Function.Bijective (fun c : Γ(Y, W) => c • B.presheaf.map (homOfLE hW).op (φ.app K a))) :
    IsIso φ := by
  have key : IsIso ((restrictFunctor (𝟙 Y)).map φ) :=
    isIso_restrictFunctor_map_of_bijective_smul (𝟙 Y) φ fun y => by
      obtain ⟨K, hy, a, ha⟩ := h y
      exact ⟨K, hy, fun x _ => ⟨x, rfl⟩, a, ha⟩
  exact (NatIso.isIso_map_iff restrictFunctorId φ).mp key

/-- A local section generating the sections over every smaller open does not vanish at any point
of its domain. -/
theorem germ_notMem_maximalSmul_of_bijective_smul {Y : Scheme.{u}} (A : Y.Modules)
    [Stacks.Ample.IsInvertibleModule Y A] {K : Y.Opens} (a : Γ(A, K))
    (ha : ∀ (W : Y.Opens) (hW : W ≤ K),
      Function.Bijective (fun c : Γ(Y, W) => c • A.presheaf.map (homOfLE hW).op a))
    (y : Y) (hy : y ∈ K) :
    (A.presheaf.germ K y hy).hom a ∉ Stacks.ModuleStalk.maximalSmul A y := by
  refine Stacks.SectionProduct.notMem_maximalSmul_of_generates A y fun w => ?_
  obtain ⟨r, hr⟩ := (Stacks.Divisors.isStalkBasis_germ_of_bijective_smul a ha y hy).surjective w
  exact ⟨r, hr.symm⟩

/-- An invertible `𝒪_S`-module is invertible as a sheaf of modules on the underlying ringed
space. -/
private theorem isInvertible_of_isInvertibleModule {S : Scheme.{u}} (M : S.Modules)
    [Stacks.Ample.IsInvertibleModule S M] :
    Stacks.SheafOfModules.IsInvertible S.toRingedSpace.presheaf
      (structureSheafRing S.toRingedSpace).property M :=
  (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ M).mpr ‹_›

/-- The unit of `f^* ⊣ f_*` is an isomorphism at an invertible module when `𝒪_Y ⟶ f_* 𝒪_X` is
an isomorphism. -/
public theorem isIso_unit_app_of_isIso_c {X Y : Scheme.{u}} (b : X ⟶ Y) [IsIso b.c]
    (A : Y.Modules) [Stacks.Ample.IsInvertibleModule Y A] :
    IsIso ((pullbackPushforwardAdjunction b).unit.app A) := by
  refine isIso_of_bijective_smul _ fun y => ?_
  obtain ⟨K, hy, a, ha⟩ :=
    @Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible Y.toRingedSpace _ A
      (isInvertible_of_isInvertibleModule A) y
  refine ⟨K, hy, a, fun W hW => ⟨ha W hW, ?_⟩⟩
  have : Stacks.Ample.IsInvertibleModule X
      ((RingedSpaceModuleAdjunction.modulePullback b.toLRSHom.toShHom).obj A) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback b A
  have hpb' := isInvertible_of_isInvertibleModule
    ((RingedSpaceModuleAdjunction.modulePullback b.toLRSHom.toShHom).obj A)
  have hle : b ⁻¹ᵁ W ≤ b ⁻¹ᵁ K := (Opens.map b.base).monotone hW
  have hgen : Function.Bijective fun c : Γ(X, b ⁻¹ᵁ W) =>
      c • ((RingedSpaceModuleAdjunction.modulePullback b.toLRSHom.toShHom).obj A).val.map
        (homOfLE hle).op
        (Stacks.RingedSpace.pullbackUnit b.toLRSHom.toShHom A (op K) a) := by
    refine Stacks.SheafOfModules.bijective_smul_of_forall_germ_notMem_maximalIdeal_smul_top
      (X := X.toRingedSpace) _ _ _ hle fun x hx => ?_
    have h1 := germ_notMem_maximalSmul_of_bijective_smul A a ha (b.base x) (hle hx)
    rw [← Stacks.NonvanishingLocusRestrict.mem_maximalSmul_germ_pullbackUnit_iff b A a x
      (hle hx)] at h1
    rwa [Stacks.NonvanishingPullback.mem_maximalSmul_iff] at h1
  have hc : IsIso (b.c.app (op W)) := inferInstance
  exact hgen.comp ((ConcreteCategory.isIso_iff_bijective (b.app W)).mp hc)

/-- Global sections of an invertible module pull back bijectively along a morphism with
`𝒪_Y ≅ f_* 𝒪_X`. -/
public theorem bijective_pullbackGlobalSection_of_isIso_c {X Y : Scheme.{u}} (b : X ⟶ Y)
    [IsIso b.c] (A : Y.Modules) [Stacks.Ample.IsInvertibleModule Y A] :
    Function.Bijective (Stacks.NonvanishingPullback.pullbackGlobalSection b A) := by
  have := isIso_unit_app_of_isIso_c b A
  have h : IsIso (((pullbackPushforwardAdjunction b).unit.app A).app ⊤) := inferInstance
  exact (ConcreteCategory.isIso_iff_bijective _).mp h

/-- Pullback along a morphism with `𝒪_Y ≅ f_* 𝒪_X` reflects isomorphy of invertible modules. -/
public theorem nonempty_iso_of_pullback_iso_of_isIso_c {X Y : Scheme.{u}} (b : X ⟶ Y)
    [IsIso b.c] {A A' : Y.Modules} [Stacks.Ample.IsInvertibleModule Y A]
    [Stacks.Ample.IsInvertibleModule Y A']
    (e : (pullback b).obj A ≅ (pullback b).obj A') : Nonempty (A ≅ A') :=
  have := isIso_unit_app_of_isIso_c b A
  have := isIso_unit_app_of_isIso_c b A'
  ⟨asIso ((pullbackPushforwardAdjunction b).unit.app A) ≪≫ (pushforward b).mapIso e ≪≫
    (asIso ((pullbackPushforwardAdjunction b).unit.app A')).symm⟩

/-- The pullback on Picard groups is injective along a morphism with `𝒪_Y ≅ f_* 𝒪_X`. -/
public theorem injective_schemePullbackClass_of_isIso_c {X Y : Scheme.{u}} (b : X ⟶ Y)
    [IsIso b.c] : Function.Injective (Stacks.Picard.schemePullbackClass b) := by
  intro x y hxy
  rw [← Stacks.Picard.classOf_picardRepresentative _ x,
    ← Stacks.Picard.classOf_picardRepresentative _ y] at hxy ⊢
  have hxy' := (Stacks.Picard.pullbackClass_classOf b.toLRSHom.toShHom _
      (Stacks.Picard.picardRepresentative Y.toRingedSpace x).property).symm.trans
    (hxy.trans (Stacks.Picard.pullbackClass_classOf b.toLRSHom.toShHom _
      (Stacks.Picard.picardRepresentative Y.toRingedSpace y).property))
  obtain ⟨e⟩ := (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).1 hxy'
  refine (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2 ?_
  have h1 : Stacks.Ample.IsInvertibleModule Y
      (Stacks.Picard.picardRepresentative Y.toRingedSpace x).obj :=
    (Stacks.Picard.picardRepresentative Y.toRingedSpace x).property.toAlgebraicGeometry
  have h2 : Stacks.Ample.IsInvertibleModule Y
      (Stacks.Picard.picardRepresentative Y.toRingedSpace y).obj :=
    (Stacks.Picard.picardRepresentative Y.toRingedSpace y).property.toAlgebraicGeometry
  exact nonempty_iso_of_pullback_iso_of_isIso_c b
    ((Stacks.ProjectiveBundleQuotients.pullbackIso b).app _ ≪≫ e ≪≫
      ((Stacks.ProjectiveBundleQuotients.pullbackIso b).app _).symm)

end AlgebraicGeometry.Scheme.Modules

end
