module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraPullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraAmbient
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureMap
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModulePullbackEpi
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.CategoryTheory.Sites.AbelianSheavesAbelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicPullback

/-!
# The conormal sequence of a morphism followed by a closed immersion

Let `i : Z ⟶ Y` be a morphism and `c : Y ⟶ U` a closed immersion of algebraic spaces over a scheme
`S` contained in a big fppf site `B`.  Write `Ker(f^♯) ⊆ 𝒪` for the kernel ideal sheaf of the
structure map of a morphism `f` (`AlgebraicGeometry.Space.kernelIdealSheaf`), and
`𝒞_f = f^*Ker(f^♯)` for the degree-one piece of its conormal algebra.  The sequence

`i^*𝒞_{Y/U} ⟶ 𝒞_{Z/U} ⟶ 𝒞_{Z/Y} ⟶ 0`,

that is `i^*c^*Ker(c^♯) ⟶ (i ≫ c)^*Ker((i ≫ c)^♯) ⟶ i^*Ker(i^♯) ⟶ 0`, is exact.  It is the
inverse image along `i` of the sequence of `𝒪_Y`-modules

`c^*Ker(c^♯) ⟶ c^*Ker((i ≫ c)^♯) ⟶ Ker(i^♯) ⟶ 0`,

which is the inverse image along `c` of the short exact sequence of `𝒪_U`-modules

`0 ⟶ Ker(c^♯) ⟶ Ker((i ≫ c)^♯) ⟶ c_*Ker(i^♯) ⟶ 0`

followed by the counit `c^*c_*Ker(i^♯) ⟶ Ker(i^♯)`.

## Main definitions

* `AlgebraicGeometry.Space.kernelConormalSequenceFirstMap`: the comparison `i^*c^* ≅ (i ≫ c)^*`
  followed by the inverse image of the inclusion `Ker(c^♯) ⊆ Ker((i ≫ c)^♯)`.
* `AlgebraicGeometry.Space.kernelConormalSequenceSecondMap`: the comparison
  `(i ≫ c)^* ≅ i^*c^*` followed by the inverse image along `i` of the map
  `c^*Ker((i ≫ c)^♯) ⟶ Ker(i^♯)` given by pullback of regular functions along `c`.

## Main results

* `AlgebraicGeometry.Space.kernelIdealSheafShortComplex_exact` and
  `AlgebraicGeometry.Space.epi_kernelIdealSheafPushforwardMap`: the sequence on `U`.
* `AlgebraicGeometry.Space.kernelIdealSheafPullbackShortComplex_exact`: the sequence on `Y`.
* `AlgebraicGeometry.Space.kernelConormalSequenceFirstMap_comp_secondMap`: the two maps compose to
  zero, for arbitrary `i` and `c`.
* `AlgebraicGeometry.Space.kernelConormalSequenceShortComplex_exact`: the conormal sequence of a
  morphism followed by a closed immersion is exact, and its second map is surjective.

## References

* [Stacks Project, Tag 06BD](https://stacks.math.columbia.edu/tag/06BD)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 09RS](https://stacks.math.columbia.edu/tag/09RS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] preservesZeroMorphisms_modulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z Y U : AlgebraicSpaces B S hS}

/-- The degree-one kernel ideal sheaf of a morphism, as an `𝒪`-module of the target. -/
noncomputable abbrev kerIdealOneModule {Y' X' : AlgebraicSpaces B S hS} (f : Y' ⟶ X') :
    Modules.{u, u} B S hS X'.1 X'.2 :=
  (kernelIdealSheafZPow B S hS f 1).toSheafOfModules

/-- Membership in the first power of the kernel ideal sheaf is membership in the kernel ideal
sheaf. -/
theorem mem_kernelIdealSheafZPow_one_iff {Y' X' : AlgebraicSpaces B S hS} (f : Y' ⟶ X')
    (V : (SmallEtale B S hS X'.1)ᵒᵖ) (a : ToType ((structureRingSheaf B S hS X').obj.obj V)) :
    a ∈ (kernelIdealSheafZPow B S hS f 1).obj V ↔ a ∈ (kernelIdealSheaf B S hS f).obj V := by
  rw [kernelIdealSheafZPow_one]

section Pushforward

variable (i : Z ⟶ Y) (c : Y ⟶ U)

/-- The map `Ker((i ≫ c)^♯) ⟶ c_*Ker(i^♯)`: the transpose, under the chartwise universal property
of the direct image, of pullback of regular functions along `c`. -/
noncomputable def kernelIdealSheafPushforwardMap :
    kerIdealOneModule B S hS (i ≫ c) ⟶
      (modulePushforward B S hS c).obj (kerIdealOneModule B S hS i) :=
  moduleFMapHom B S hS c _ _ (kernelIdealSheafZPowFMap B S hS i c 1)

/-- The degree-one ambient map `c^*Ker((i ≫ c)^♯) ⟶ Ker(i^♯)`, with its source and target
spelled as modules of the small étale ringed sites. -/
noncomputable abbrev kernelIdealSheafPullbackMap :
    (modulePullback B S hS c).obj (kerIdealOneModule B S hS (i ≫ c)) ⟶ kerIdealOneModule B S hS i :=
  kernelIdealSheafZPowPullbackMap B S hS i c 1

/-- The map into the direct image is the adjoint transpose of the ambient map. -/
theorem kernelIdealSheafPushforwardMap_eq :
    kernelIdealSheafPushforwardMap B S hS i c =
      (modulePullbackAdjunction B S hS c).homEquiv _ _
        (kernelIdealSheafPullbackMap B S hS i c) := by
  rw [kernelIdealSheafPullbackMap, kernelIdealSheafZPowPullbackMap, Equiv.apply_symm_apply]
  rfl

/-- The chart projections of the map into the direct image are pullback of regular functions
along the induced morphisms of charts. -/
theorem moduleChartProjection_kernelIdealSheafPushforwardMap (V : SmallEtale B S hS U.1)
    (j : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS Y).op)
    (x : (kerIdealOneModule B S hS (i ≫ c)).val.obj (op V)) :
    (moduleChartProjection B S hS c V j).app
        (moduleSetSheaf B S hS Y (kerIdealOneModule B S hS i))
        ((kernelIdealSheafPushforwardMap B S hS i c).val.app (op V) x) =
      (kernelIdealSheafZPowFMap B S hS i c 1).app (chartDiagramOfIndex B S hS c V j) x :=
  moduleChartProjection_app_moduleFMapSection B S hS c _ _ _ V j x

/-- The kernel of the map into the direct image is `Ker(c^♯)`: a section of `Ker((i ≫ c)^♯)` is
sent to zero exactly when it is killed by `c^♯`. -/
theorem kernelIdealSheafPushforwardMap_app_eq_zero_iff (V : SmallEtale B S hS U.1)
    (x : (kerIdealOneModule B S hS (i ≫ c)).val.obj (op V)) :
    (kernelIdealSheafPushforwardMap B S hS i c).val.app (op V) x = 0 ↔
      x.1 ∈ (kernelIdealSheaf B S hS c).obj (op V) := by
  have hq0 : (kernelIdealSheafPushforwardMap B S hS i c).val.app (op V) 0 = 0 := map_zero _
  have hproj : ∀ (j : StructuredArrow (op (chartBaseChange B S hS c V))
      (comparisonFunctor B S hS Y).op)
      (y : (kerIdealOneModule B S hS (i ≫ c)).val.obj (op V)),
      ((moduleChartProjection B S hS c V j).app
        (moduleSetSheaf B S hS Y (kerIdealOneModule B S hS i))
        ((kernelIdealSheafPushforwardMap B S hS i c).val.app (op V) y)).1 =
        chartPullbackRingHom B S hS c V j y.1 := fun j y =>
    (congrArg Subtype.val
      (moduleChartProjection_kernelIdealSheafPushforwardMap B S hS i c V j y)).trans rfl
  refine ⟨fun h ↦ (mem_ker_structureSharp_iff B S hS c V x.1).2 fun j ↦ ?_, fun h ↦ ?_⟩
  · have h' := congrArg (fun z => ((moduleChartProjection B S hS c V j).app
      (moduleSetSheaf B S hS Y (kerIdealOneModule B S hS i)) z).1)
      (h.trans hq0.symm)
    rw [hproj, hproj] at h'
    exact RingHom.mem_ker.2 (h'.trans (map_zero (chartPullbackRingHom B S hS c V j)))
  · refine Eq.trans ?_ hq0
    refine moduleChartProjection_ext B S hS c V _ fun j => Subtype.ext ?_
    rw [hproj, hproj]
    exact ((mem_ker_structureSharp_iff B S hS c V x.1).1 h j).trans (map_zero _).symm

/-- The inclusion of `Ker(c^♯)` into `Ker((i ≫ c)^♯)`, in degree one. -/
noncomputable abbrev kernelIdealSheafCompInclusion :
    kerIdealOneModule B S hS c ⟶ kerIdealOneModule B S hS (i ≫ c) :=
  (kernelIdealGradedAlgebraCompHom B S hS i c i c rfl).app 1

/-- The inclusion does not change the underlying regular function. -/
theorem kernelIdealSheafCompInclusion_app_coe (V : SmallEtale B S hS U.1)
    (x : (kerIdealOneModule B S hS c).val.obj (op V)) :
    ((kernelIdealSheafCompInclusion B S hS i c).val.app (op V) x).1 = x.1 :=
  SheafOfModules.reesGradedAlgebraHomOfLe_app_coe _ _ _ _ 1 (op V) x

/-- The short complex on `U` is a complex. -/
theorem kernelIdealSheafCompInclusion_comp_pushforwardMap :
    kernelIdealSheafCompInclusion B S hS i c ≫ kernelIdealSheafPushforwardMap B S hS i c = 0 := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext (fun V ↦ ?_))
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  refine ((kernelIdealSheafPushforwardMap_app_eq_zero_iff B S hS i c V.unop _).2 ?_).trans rfl
  exact (congrArg (· ∈ (kernelIdealSheaf B S hS c).obj V)
    (kernelIdealSheafCompInclusion_app_coe B S hS i c V.unop x)).mpr
    ((mem_kernelIdealSheafZPow_one_iff B S hS c V x.1).1 x.2)

/-- The short complex `Ker(c^♯) ⟶ Ker((i ≫ c)^♯) ⟶ c_*Ker(i^♯)` of `𝒪_U`-modules. -/
noncomputable abbrev kernelIdealSheafShortComplex : ShortComplex (Modules.{u, u} B S hS U.1 U.2) :=
  ShortComplex.mk (kernelIdealSheafCompInclusion B S hS i c)
    (kernelIdealSheafPushforwardMap B S hS i c)
    (kernelIdealSheafCompInclusion_comp_pushforwardMap B S hS i c)

/-- The short complex on `U` is exact, for an arbitrary morphism `c`. -/
theorem kernelIdealSheafShortComplex_exact :
    (kernelIdealSheafShortComplex B S hS i c).Exact := by
  rw [← Stacks.SheafOfModules.exact_iff_toSheaf_exact]
  apply Stacks.AbelianSheaves.exact_of_locallyLiftable
  intro V z hz
  refine ⟨⊤, (SmallEtale.topology B S hS U.1).top_mem V, fun W p _ => ?_⟩
  have hmemV := (kernelIdealSheafPushforwardMap_app_eq_zero_iff B S hS i c V z).1 hz
  have hmem : ((structureRingSheaf B S hS U).obj.map p.op).hom z.1 ∈
      (kernelIdealSheafZPow B S hS c 1).obj (op W) :=
    (mem_kernelIdealSheafZPow_one_iff B S hS c (op W) _).2
      (mem_ker_structureSharp_app_map B S hS c p.op _ hmemV)
  exact ⟨⟨_, hmem⟩, Subtype.ext ((kernelIdealSheafCompInclusion_app_coe B S hS i c W _).trans rfl)⟩

/-- The chart projections of the direct image of an inclusion of a sheaf of ideals are the
underlying sections of the chart projections. -/
theorem moduleChartProjection_modulePushforward_map_ι
    (N : (SheafOfModules.unit (structureRingSheaf B S hS Y)).Submodule) (V : SmallEtale B S hS U.1)
    (j : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS Y).op)
    (x : ((modulePushforward B S hS c).obj N.toSheafOfModules).val.obj (op V)) :
    (moduleChartProjection B S hS c V j).app (structureSetSheaf B S hS Y)
      (((modulePushforward B S hS c).map N.ι).val.app (op V) x) =
    ((moduleChartProjection B S hS c V j).app
      (moduleSetSheaf B S hS Y N.toSheafOfModules) x).1 := by
  have h := ConcreteCategory.congr_hom
    ((moduleChartProjection B S hS c V j).naturality
      ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map N.ι)) x
  exact h

/-- The map `Ker((i ≫ c)^♯) ⟶ c_*Ker(i^♯)` is surjective when `c` is a closed immersion. -/
theorem epi_kernelIdealSheafPushforwardMap (hc : IsClosedImmersion B S hS c.hom) :
    Epi (kernelIdealSheafPushforwardMap B S hS i c) := by
  refine Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _ ⟨fun {V} t => ?_⟩
  let N := kernelIdealSheafZPow B S hS i 1
  let T : ToType ((structureRingSheafDirectImage B S hS c).obj.obj (op V)) :=
    ((modulePushforward B S hS c).map N.ι).val.app (op V) t
  have hsurj : Sheaf.IsLocallySurjective (structureSharp B S hS c) :=
    isLocallySurjective_structureSharp B S hS c hc
  refine (SmallEtale.topology B S hS U.1).superset_covering ?_
    (Presheaf.imageSieve_mem (SmallEtale.topology B S hS U.1) (structureSharp B S hS c).hom T)
  rintro W m ⟨s, hs⟩
  let tW : ((modulePushforward B S hS c).obj N.toSheafOfModules).val.obj (op W) :=
    ((modulePushforward B S hS c).obj N.toSheafOfModules).val.map m.op t
  have hE1 : ∀ (j : StructuredArrow (op (chartBaseChange B S hS c W))
      (comparisonFunctor B S hS Y).op),
      chartPullbackRingHom B S hS c W j s =
        ((moduleChartProjection B S hS c W j).app
          (moduleSetSheaf B S hS Y N.toSheafOfModules) tW).1 := fun j => by
    have h1 := moduleChartProjection_app_structureSharp B S hS c W j s
    have h2 : ((modulePushforward B S hS c).map N.ι).val.app (op W) tW =
        (structureRingSheafDirectImage B S hS c).obj.map m.op T :=
      PresheafOfModules.naturality_apply ((modulePushforward B S hS c).map N.ι).val m.op t
    rw [← moduleChartProjection_modulePushforward_map_ι B S hS c N W j tW, h2]
    exact h1.symm.trans (congrArg _ hs)
  have hmem : s ∈ (kernelIdealSheaf B S hS (i ≫ c)).obj (op W) := by
    refine (mem_ker_structureSharp_iff B S hS (i ≫ c) W s).2 fun k => ?_
    have hg' : ((unop k.right).1.hom ≫ i.hom) ≫ c.hom =
        yoneda.map (chartBaseChangeMap B S hS (i ≫ c) W k) ≫ W.1.hom :=
      (Category.assoc _ _ _).trans (chartDiagramOfIndex B S hS (i ≫ c) W k).comm
    obtain ⟨ℓ, hℓsnd, hℓfst⟩ : ∃ ℓ : (unop k.right).1.left ⟶ hc.rep.pullback W.1.hom,
        ℓ ≫ hc.rep.snd W.1.hom = chartBaseChangeMap B S hS (i ≫ c) W k ∧
          yoneda.map ℓ ≫ hc.rep.fst W.1.hom = (unop k.right).1.hom ≫ i.hom :=
      ⟨_, hc.rep.lift_snd _ _ hg', hc.rep.lift_fst _ _ hg'⟩
    have hj₀ := chartBaseChangeMap_chartBaseChangeArrow B S hS c hc.rep W
    have hK : chartPullbackRingHom B S hS c W (chartBaseChangeArrow B S hS c hc.rep W) s ∈
        (kernelIdealSheaf B S hS i).obj (op ((smallBaseChange B S hS c hc.rep).obj W)) := by
      rw [hE1]
      exact (mem_kernelIdealSheafZPow_one_iff B S hS i _ _).1 (Subtype.prop _)
    have hkill := kernelIdealSheaf_le_ker_of_lift B S hS i
      ((smallBaseChange B S hS c hc.rep).obj W) _ (unop k.right).1.hom hℓfst hK
    have hkill' : (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map ℓ).op).hom
        (chartPullbackRingHom B S hS c W (chartBaseChangeArrow B S hS c hc.rep W) s) = 0 := hkill
    refine RingHom.mem_ker.2 (Eq.trans ?_ hkill')
    rw [chartPullbackRingHom, chartPullbackRingHom, hj₀, ← hℓsnd, Functor.map_comp, op_comp,
      Functor.map_comp]
    rfl
  have hmem' : s ∈ (kernelIdealSheafZPow B S hS (i ≫ c) 1).obj (op W) :=
    (mem_kernelIdealSheafZPow_one_iff B S hS (i ≫ c) _ _).2 hmem
  refine ⟨⟨s, hmem'⟩, ?_⟩
  refine moduleChartProjection_ext B S hS c W _ fun j => Subtype.ext ?_
  exact ((congrArg Subtype.val
    (moduleChartProjection_kernelIdealSheafPushforwardMap B S hS i c W j ⟨s, hmem'⟩)).trans
      rfl).trans (hE1 j)

/-- The degree-one map `c^*Ker((i ≫ c)^♯) ⟶ Ker(i^♯)` of the ambient factor is the inverse image
of `AlgebraicGeometry.Space.kernelIdealSheafPushforwardMap` followed by the counit. -/
theorem kernelIdealSheafPullbackMap_eq :
    kernelIdealSheafPullbackMap B S hS i c =
      (modulePullback B S hS c).map (kernelIdealSheafPushforwardMap B S hS i c) ≫
        (modulePullbackAdjunction B S hS c).counit.app (kerIdealOneModule B S hS i) :=
  calc kernelIdealSheafPullbackMap B S hS i c
      = ((modulePullbackAdjunction B S hS c).homEquiv _ _).symm
          (((modulePullbackAdjunction B S hS c).homEquiv _ _)
            (kernelIdealSheafPullbackMap B S hS i c)) := (Equiv.symm_apply_apply _ _).symm
    _ = ((modulePullbackAdjunction B S hS c).homEquiv _ _).symm
          (kernelIdealSheafPushforwardMap B S hS i c) := by
        rw [kernelIdealSheafPushforwardMap_eq]
    _ = _ := Adjunction.homEquiv_counit _ _ _ _

/-- The short complex `c^*Ker(c^♯) ⟶ c^*Ker((i ≫ c)^♯) ⟶ Ker(i^♯)` of `𝒪_Y`-modules. -/
noncomputable abbrev kernelIdealSheafPullbackShortComplex :
    ShortComplex (Modules.{u, u} B S hS Y.1 Y.2) :=
  ShortComplex.mk ((modulePullback B S hS c).map (kernelIdealSheafCompInclusion B S hS i c))
    (kernelIdealSheafPullbackMap B S hS i c) (by
      rw [kernelIdealSheafPullbackMap_eq, ← Functor.map_comp_assoc,
        kernelIdealSheafCompInclusion_comp_pushforwardMap, Functor.map_zero, zero_comp])

/-- The morphism from the inverse image along `c` of the short complex on `U` to the short
complex on `Y`: the identity on the first two terms and the counit on the third. -/
noncomputable abbrev kernelIdealSheafShortComplexPullbackHom :
    (kernelIdealSheafShortComplex B S hS i c).map (modulePullback B S hS c) ⟶
      kernelIdealSheafPullbackShortComplex B S hS i c where
  τ₁ := 𝟙 _
  τ₂ := 𝟙 _
  τ₃ := (modulePullbackAdjunction B S hS c).counit.app (kerIdealOneModule B S hS i)
  comm₁₂ := by simp
  comm₂₃ := (Category.id_comp _).trans (kernelIdealSheafPullbackMap_eq B S hS i c).symm

/-- The inverse image along `f` of an exact short complex of modules whose second map is
surjective is exact. -/
private theorem exact_map_modulePullback {Y' X' : AlgebraicSpaces B S hS} (f : Y' ⟶ X')
    (T : ShortComplex (Modules.{u, u} B S hS X'.1 X'.2)) (hT : T.Exact) (hg : Epi T.g) :
    (T.map (modulePullback B S hS f)).Exact := by
  have : PreservesColimitsOfSize.{0, 0} (modulePullback B S hS f) :=
    (modulePullbackAdjunction B S hS f).leftAdjoint_preservesColimits
  exact hT.map_of_epi_of_preservesCokernel _ hg inferInstance

/-- The short complex on `Y` is exact and its second map is surjective, for a closed immersion
`c`. -/
theorem kernelIdealSheafPullbackShortComplex_exact (hc : IsClosedImmersion B S hS c.hom) :
    (kernelIdealSheafPullbackShortComplex B S hS i c).Exact ∧
      Epi (kernelIdealSheafPullbackMap B S hS i c) := by
  have hq := epi_kernelIdealSheafPushforwardMap B S hS i c hc
  have h₁ : ((kernelIdealSheafShortComplex B S hS i c).map (modulePullback B S hS c)).Exact :=
    exact_map_modulePullback B S hS c _ (kernelIdealSheafShortComplex_exact B S hS i c) hq
  have hcounit :
      IsIso ((modulePullbackAdjunction B S hS c).counit.app (kerIdealOneModule B S hS i)) :=
    isIso_modulePullbackAdjunction_counit B S hS c hc _
  have : (modulePullback B S hS c).PreservesEpimorphisms :=
    preservesEpimorphisms_modulePullback B S hS c
  have : Epi ((modulePullback B S hS c).map (kernelIdealSheafPushforwardMap B S hS i c)) :=
    (modulePullback B S hS c).map_epi _
  have : Epi (kernelIdealSheafShortComplexPullbackHom B S hS i c).τ₁ := inferInstanceAs (Epi (𝟙 _))
  have : IsIso (kernelIdealSheafShortComplexPullbackHom B S hS i c).τ₂ :=
    inferInstanceAs (IsIso (𝟙 _))
  have : Mono (kernelIdealSheafShortComplexPullbackHom B S hS i c).τ₃ := IsIso.mono_of_iso _
  refine ⟨(ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    (kernelIdealSheafShortComplexPullbackHom B S hS i c)).1 h₁, ?_⟩
  have : Epi ((modulePullbackAdjunction B S hS c).counit.app (kerIdealOneModule B S hS i)) :=
    @IsIso.epi_of_iso _ _ _ _ _ hcounit
  rw [kernelIdealSheafPullbackMap_eq]
  exact epi_comp _ _

/-! ### The conormal sequence of a morphism followed by a closed immersion -/

/-- The first map of the conormal sequence, `i^*𝒞_{Y/U} ⟶ 𝒞_{Z/U}` for `i : Z ⟶ Y` and
`c : Y ⟶ U`, in the kernel-ideal form `𝒞_{Y/U} = c^*Ker(c^♯)`,
`𝒞_{Z/U} = (i ≫ c)^*Ker((i ≫ c)^♯)`: the composition comparison `i^*c^* ≅ (i ≫ c)^*` followed by
the inverse image of the inclusion `Ker(c^♯) ⊆ Ker((i ≫ c)^♯)`.  This is the canonical map of
Stacks 04CP for the square with `f = i` and `g = 𝟙`. -/
noncomputable def kernelConormalSequenceFirstMap :
    (modulePullback B S hS i).obj ((modulePullback B S hS c).obj (kerIdealOneModule B S hS c)) ⟶
      (modulePullback B S hS (i ≫ c)).obj (kerIdealOneModule B S hS (i ≫ c)) :=
  (modulePullbackCompIso B S hS i c).hom.app (kerIdealOneModule B S hS c) ≫
    (modulePullback B S hS (i ≫ c)).map (kernelIdealSheafCompInclusion B S hS i c)

/-- The second map of the conormal sequence, `𝒞_{Z/U} ⟶ 𝒞_{Z/Y}`: the composition comparison
`(i ≫ c)^* ≅ i^*c^*` followed by the inverse image along `i` of the map
`c^*Ker((i ≫ c)^♯) ⟶ Ker(i^♯)` given on sections by pullback of regular functions along `c`.
This is the degree-one component `AlgebraicGeometry.Space.conormalAlgebraAmbientPieceMap i c 1`
of the ambient factor of Stacks 09RS, with source and target spelled as inverse images of kernel
ideal sheaves. -/
noncomputable def kernelConormalSequenceSecondMap :
    (modulePullback B S hS (i ≫ c)).obj (kerIdealOneModule B S hS (i ≫ c)) ⟶
      (modulePullback B S hS i).obj (kerIdealOneModule B S hS i) :=
  (modulePullbackCompIso B S hS i c).inv.app (kerIdealOneModule B S hS (i ≫ c)) ≫
    (modulePullback B S hS i).map (kernelIdealSheafPullbackMap B S hS i c)

/-- The defining equation of the second map. -/
theorem kernelConormalSequenceSecondMap_eq :
    kernelConormalSequenceSecondMap B S hS i c =
      (modulePullbackCompIso B S hS i c).inv.app (kerIdealOneModule B S hS (i ≫ c)) ≫
        (modulePullback B S hS i).map (kernelIdealSheafPullbackMap B S hS i c) :=
  rfl

/-- The first map, read on `i^*c^*`, is the inverse image of the inclusion of kernel ideal
sheaves. -/
theorem kernelConormalSequenceFirstMap_comp_inv :
    kernelConormalSequenceFirstMap B S hS i c ≫
        (modulePullbackCompIso B S hS i c).inv.app (kerIdealOneModule B S hS (i ≫ c)) =
      (modulePullback B S hS i).map
        ((modulePullback B S hS c).map (kernelIdealSheafCompInclusion B S hS i c)) := by
  rw [kernelConormalSequenceFirstMap, Category.assoc,
    (modulePullbackCompIso B S hS i c).inv.naturality, Iso.hom_inv_id_app_assoc]
  rfl

/-- The two maps of the conormal sequence compose to zero, for arbitrary morphisms
`i : Z ⟶ Y` and `c : Y ⟶ U`. -/
theorem kernelConormalSequenceFirstMap_comp_secondMap :
    kernelConormalSequenceFirstMap B S hS i c ≫ kernelConormalSequenceSecondMap B S hS i c = 0 := by
  rw [kernelConormalSequenceSecondMap_eq, ← Category.assoc, kernelConormalSequenceFirstMap_comp_inv,
    ← Functor.map_comp, (kernelIdealSheafPullbackShortComplex B S hS i c).zero, Functor.map_zero]

/-- The conormal sequence `i^*𝒞_{Y/U} ⟶ 𝒞_{Z/U} ⟶ 𝒞_{Z/Y}` of `i : Z ⟶ Y` and `c : Y ⟶ U`, in
the kernel-ideal form. -/
noncomputable abbrev kernelConormalSequenceShortComplex :
    ShortComplex (Modules.{u, u} B S hS Z.1 Z.2) :=
  ShortComplex.mk _ _ (kernelConormalSequenceFirstMap_comp_secondMap B S hS i c)

/-- The comparison of the conormal sequence with the inverse image along `i` of the short
complex on `Y`. -/
noncomputable abbrev kernelConormalSequenceShortComplexHom :
    kernelConormalSequenceShortComplex B S hS i c ⟶
      (kernelIdealSheafPullbackShortComplex B S hS i c).map (modulePullback B S hS i) where
  τ₁ := 𝟙 _
  τ₂ := (modulePullbackCompIso B S hS i c).inv.app (kerIdealOneModule B S hS (i ≫ c))
  τ₃ := 𝟙 _
  comm₁₂ := (Category.id_comp _).trans (kernelConormalSequenceFirstMap_comp_inv B S hS i c).symm
  comm₂₃ := (Category.comp_id _).trans (kernelConormalSequenceSecondMap_eq B S hS i c)

/-- For a closed immersion `c : Y ⟶ U` and an arbitrary morphism `i : Z ⟶ Y` of algebraic spaces,
the sequence `i^*𝒞_{Y/U} ⟶ 𝒞_{Z/U} ⟶ 𝒞_{Z/Y} ⟶ 0` of kernel-ideal conormal modules is exact. -/
theorem kernelConormalSequenceShortComplex_exact (hc : IsClosedImmersion B S hS c.hom) :
    (kernelConormalSequenceShortComplex B S hS i c).Exact ∧
      Epi (kernelConormalSequenceSecondMap B S hS i c) := by
  obtain ⟨hY, hepi⟩ := kernelIdealSheafPullbackShortComplex_exact B S hS i c hc
  have : (modulePullback B S hS i).PreservesEpimorphisms :=
    preservesEpimorphisms_modulePullback B S hS i
  have h₁ : ((kernelIdealSheafPullbackShortComplex B S hS i c).map
      (modulePullback B S hS i)).Exact :=
    exact_map_modulePullback B S hS i _ hY hepi
  have : Epi ((modulePullback B S hS i).map (kernelIdealSheafPullbackMap B S hS i c)) :=
    (modulePullback B S hS i).map_epi _
  have : Epi (kernelConormalSequenceShortComplexHom B S hS i c).τ₁ := inferInstanceAs (Epi (𝟙 _))
  have : IsIso (kernelConormalSequenceShortComplexHom B S hS i c).τ₂ :=
    inferInstanceAs (IsIso ((modulePullbackCompIso B S hS i c).inv.app
      (kerIdealOneModule B S hS (i ≫ c))))
  have : Mono (kernelConormalSequenceShortComplexHom B S hS i c).τ₃ := inferInstanceAs (Mono (𝟙 _))
  refine ⟨(ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    (kernelConormalSequenceShortComplexHom B S hS i c)).2 h₁, ?_⟩
  have : Epi ((modulePullbackCompIso B S hS i c).inv.app (kerIdealOneModule B S hS (i ≫ c))) :=
    @IsIso.epi_of_iso _ _ _ _ _ (((modulePullbackCompIso B S hS i c).app _).isIso_inv)
  rw [kernelConormalSequenceSecondMap_eq]
  exact epi_comp _ _

end Pushforward

end AlgebraicGeometry.Space
