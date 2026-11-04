module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorDiagonal
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorPushforward
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorLimits

/-!
# The closed immersion of Quot along a surjection of modules

Let `f : X ⟶ B` be a morphism of algebraic spaces of finite presentation and let `φ : F ⟶ G` be
a surjection of quasi-coherent `𝒪_X`-modules. Stacks 0DP5 asserts that there is a canonical closed
immersion `Quot_{G/X/B} ⟶ Quot_{F/X/B}`.

## The construction

A quotient `G_T ⟶ Q` of `G_T` determines the quotient `F_T ⟶ G_T ⟶ Q` of `F_T`, through the
surjection `φ_T : F_T ⟶ G_T`. Quotients are recorded by their kernels, so this is
`L ↦ ker(φ_T ≫ (G_T ⟶ G_T/L))`, which is
`AlgebraicGeometry.Space.QuotSituation.quotientSubobject`. It commutes with pullback of
quotients (`AlgebraicGeometry.Space.QuotSituation.quotientPullback_quotientSubobject`), which is
how it assembles into the transformation
`AlgebraicGeometry.Space.QuotSituation.quotientInclusion`.

## The closed immersion

Let `N = ker φ`. By right exactness of pullback `N_T ⟶ F_T ⟶ G_T ⟶ 0` is exact for every `T`. So a
quotient `F_T ⟶ Q'` of `F_T` comes from a quotient of `G_T` exactly when it kills the image of
`N_T`, i.e. when `N_T ⟶ F_T ⟶ Q'` vanishes. Given a quotient over `T`, the locus of `T' ⟶ T` over
which its pullback comes from `Quot_{G/X/B}` is therefore the zero locus of `N_T ⟶ F_T ⟶ Q'`, a
closed subscheme of `T` by Stacks 083M.

The Quot presheaves take values in `Type (u + 1)`, so being a closed immersion is read through
`CategoryTheory.uliftYoneda`: it is the relative property
`AlgebraicGeometry.Space.QuotSituation.closedImmersionOver` of `CategoryTheory.uliftYoneda`.

## Main results

* `AlgebraicGeometry.Space.QuotSituation.quotientInclusion`: the transformation
  `Quot_{G/X/B} ⟶ Quot_{F/X/B}` over `B`.
* `AlgebraicGeometry.Space.QuotSituation.relative_closedImmersionOver_quotientInclusion`: the
  transformation `Quot_{G/X/B} ⟶ Quot_{F/X/B}` is representable by closed immersions.

## References

* [Stacks Project, Tag 0DP5](https://stacks.math.columbia.edu/tag/0DP5)
* [Stacks Project, Tag 083M](https://stacks.math.columbia.edu/tag/083M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

-- The `𝒪_{X_T}`-modules here have their sections in the universe `u` of the schemes. The
-- ambient-universe abelian and Grothendieck structures of `Stacks.Cohomology.SiteModules` would be
-- selected ahead of `SheafOfModules.instAbelian` and leave the module universes unsolved.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace CategoryTheory.Functor

variable {C : Type*} {D₁ : Type*} {D₂ : Type*} [Category* C] [Category* D₁] [Category* D₂]
  [Abelian D₁] [Abelian D₂] {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂}

/-- **Conjugation of a quotient induced along a map.** For a comparison `e : P₂ ≅ P₁ ⋙ L` and a
map `φ : M ⟶ N` with `P₁ φ` and `P₂ φ` epimorphisms, the conjugate of the quotient
`P₁ M ⟶ P₁ N ⟶ P₁ N / K` is the quotient `P₂ M ⟶ P₂ N ⟶ P₂ N / K'` induced by the conjugate `K'`
of `K`. -/
theorem conjSubobject_kernelSubobject_map_comp_cokernel_π [L.PreservesEpimorphisms]
    (e : P₂ ≅ P₁ ⋙ L) {M N : C} (φ : M ⟶ N) [Epi (P₁.map φ)] [Epi (P₂.map φ)]
    (K : Subobject (P₁.obj N)) :
    conjSubobject e (kernelSubobject (P₁.map φ ≫ cokernel.π K.arrow)) =
      kernelSubobject (P₂.map φ ≫ cokernel.π (conjSubobject e K).arrow) := by
  refine conjSubobject_kernelSubobject_eq e (P₁.map φ ≫ cokernel.π K.arrow)
    (P₂.map φ ≫ cokernel.π (conjSubobject e K).arrow) (conjSubobjectCokernelIso e K).symm ?_
  have hnat := e.hom.naturality φ
  have hproj := cokernel_π_comp_conjSubobjectCokernelIso_hom e K
  simp only [Functor.comp_map] at hnat
  rw [Iso.symm_hom, L.map_comp, ← Category.assoc, ← Category.assoc, ← hnat, Category.assoc,
    Category.assoc]
  congr 1
  rw [← Category.assoc, Iso.comp_inv_eq, hproj]
  rfl

/-- **Vanishing against a conjugate quotient.** For a comparison `e : P₂ ≅ P₁ ⋙ L`, a map
`ι : N ⟶ M` and a subobject `K` of `P₁ M`, the image under `L` of `P₁ N ⟶ P₁ M ⟶ P₁ M / K` vanishes
exactly when `P₂ N ⟶ P₂ M ⟶ P₂ M / K'` does, `K'` the conjugate of `K`. -/
theorem map_comp_cokernel_π_eq_zero_iff [L.PreservesEpimorphisms] [L.PreservesZeroMorphisms]
    (e : P₂ ≅ P₁ ⋙ L) {N M : C} (ι : N ⟶ M) (K : Subobject (P₁.obj M)) :
    L.map (P₁.map ι ≫ cokernel.π K.arrow) = 0 ↔
      P₂.map ι ≫ cokernel.π (conjSubobject e K).arrow = 0 := by
  have hnat := e.hom.naturality ι
  have hproj := cokernel_π_comp_conjSubobjectCokernelIso_hom e K
  simp only [Functor.comp_map] at hnat
  have key : e.hom.app N ≫ L.map (P₁.map ι ≫ cokernel.π K.arrow) =
      (P₂.map ι ≫ cokernel.π (conjSubobject e K).arrow) ≫ (conjSubobjectCokernelIso e K).hom := by
    rw [L.map_comp, ← Category.assoc, ← hnat, Category.assoc, Category.assoc, hproj]
    rfl
  constructor
  · intro h
    rw [h, comp_zero] at key
    exact (cancel_mono (conjSubobjectCokernelIso e K).hom).1 (key.symm.trans zero_comp.symm)
  · intro h
    rw [h, zero_comp] at key
    exact (cancel_epi (e.hom.app N)).1 (key.trans comp_zero.symm)

/-- A map killed by `ψ` kills the projection onto the quotient by the kernel of `ψ`. -/
theorem _root_.CategoryTheory.Limits.comp_cokernel_π_kernelSubobject_eq_zero {A N Q : D₁}
    (ψ : A ⟶ Q) (ν : N ⟶ A) (h : ν ≫ ψ = 0) :
    ν ≫ cokernel.π (kernelSubobject ψ).arrow = 0 := by
  have hf : (kernelSubobject ψ).Factors ν := (kernelSubobject_factors_iff _ _).2 h
  rw [← Subobject.factorThru_arrow _ _ hf, Category.assoc, cokernel.condition, comp_zero]

/-- If `p ≫ χ` is the projection onto the quotient by `K`, with `χ` an epimorphism, then the
quotient of the source of `p` induced by the quotient presented by `χ` is the one by `K`. -/
theorem _root_.CategoryTheory.Limits.kernelSubobject_comp_cokernel_π_kernelSubobject
    {A M : D₁} (p : A ⟶ M) (K : Subobject A) (χ : M ⟶ cokernel K.arrow) [Epi χ]
    (h : p ≫ χ = cokernel.π K.arrow) :
    kernelSubobject (p ≫ cokernel.π (kernelSubobject χ).arrow) = K := by
  rw [← kernelSubobject_comp_mono _ (Abelian.cokernelKernelSubobjectIso χ).hom]
  simp only [Category.assoc, Abelian.cokernel_π_kernelSubobject_comp, h,
    kernelSubobject_cokernel_π]

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotSituation

variable (D : QuotSituation B S hS)

/-- The Quot situation of a second quasi-coherent module `G` on the same space `X` over `B`. -/
abbrev withModule (G : Modules.{u, u} B S hS D.X.1 D.X.2) (hG : G.IsQuasicoherentOnSite) :
    QuotSituation B S hS where
  X := D.X
  Y := D.Y
  f := D.f
  F := G
  quasicoherent := hG
  finitePresentation := D.finitePresentation

variable {G : Modules.{u, u} B S hS D.X.1 D.X.2} {hG : G.IsQuasicoherentOnSite} (φ : D.F ⟶ G)

/-- The base change `φ_T : F_T ⟶ G_T` of a map of `𝒪_X`-modules to a test scheme. -/
abbrev baseChangeModuleMap (T : SchemesOver D.Y) :
    D.baseChangeModule T ⟶ (D.withModule G hG).baseChangeModule T :=
  (modulePullback B S hS (D.sourceProjection T)).map φ

variable [Epi φ]

/-- The base change `φ_T : F_T ⟶ G_T` of an epimorphism `φ : F ⟶ G` is an epimorphism. -/
instance epi_baseChangeModuleMap (T : SchemesOver D.Y) :
    Epi (D.baseChangeModuleMap (hG := hG) φ T) :=
  (modulePullback B S hS (D.sourceProjection T)).map_epi φ

/-- For an epimorphism `φ : F ⟶ G`, the composite `F_T ⟶ G_T ⟶ G_T/L` is an epimorphism. -/
instance epi_baseChangeModuleMap_comp_quotientProjection (T : SchemesOver D.Y)
    (L : Subobject ((D.withModule G hG).baseChangeModule T)) :
    Epi (D.baseChangeModuleMap φ T ≫ (D.withModule G hG).quotientProjection T L) :=
  @epi_comp _ _ _ _ _ _ (D.epi_baseChangeModuleMap (hG := hG) φ T) _
    ((D.withModule G hG).epi_quotientProjection T L)

/-- The kernel of the quotient `F_T ⟶ G_T ⟶ G_T/L` of `F_T` induced by a quotient of `G_T`. -/
def quotientSubobject (T : SchemesOver D.Y)
    (L : Subobject ((D.withModule G hG).baseChangeModule T)) :
    Subobject (D.baseChangeModule T) :=
  kernelSubobject (D.baseChangeModuleMap φ T ≫ (D.withModule G hG).quotientProjection T L)

/-- The quotient of `F_T` induced by a quotient of `G_T` is that quotient of `G_T`. -/
def quotientSubobjectIso (T : SchemesOver D.Y)
    (L : Subobject ((D.withModule G hG).baseChangeModule T)) :
    D.quotientModule T (D.quotientSubobject φ T L) ≅ (D.withModule G hG).quotientModule T L :=
  Abelian.cokernelKernelSubobjectIso
    (D.baseChangeModuleMap φ T ≫ (D.withModule G hG).quotientProjection T L)

/-- A member of `Quot_{G/X/B}(T)` induces a member of `Quot_{F/X/B}(T)`. -/
theorem quotientSubobject_mem {T : SchemesOver D.Y}
    {L : Subobject ((D.withModule G hG).baseChangeModule T)}
    (hL : L ∈ (D.withModule G hG).properlySupportedQuotients T) :
    D.quotientSubobject φ T L ∈ D.properlySupportedQuotients T :=
  (D.mem_properlySupportedQuotients_iff T _).2
    (IsQuotModule.of_iso (D.quotientSubobjectIso φ T L).symm
      (((D.withModule G hG).mem_properlySupportedQuotients_iff T L).1 hL))

/-- **The induced quotient commutes with pullback of quotients.** -/
theorem quotientPullback_quotientSubobject {T' T : SchemesOver D.Y} (g : T' ⟶ T)
    (L : Subobject ((D.withModule G hG).baseChangeModule T)) :
    D.quotientPullback g (D.quotientSubobject φ T L) =
      D.quotientSubobject φ T' ((D.withModule G hG).quotientPullback g L) :=
  have := D.epi_baseChangeModuleMap (hG := hG) φ T
  have := D.epi_baseChangeModuleMap (hG := hG) φ T'
  Functor.conjSubobject_kernelSubobject_map_comp_cokernel_π (D.baseChangeComparison g) φ L

/-- **The transformation `Quot_{G/X/B} ⟶ Quot_{F/X/B}`** induced by a surjection `φ : F ⟶ G`, on
the test schemes over `B`: a quotient `G_T ⟶ Q` goes to the quotient `F_T ⟶ G_T ⟶ Q`. -/
def quotientInclusion : (D.withModule G hG).quotFunctor ⟶ D.quotFunctor where
  app T := ↾fun L => ⟨D.quotientSubobject φ T.unop L.1, D.quotientSubobject_mem φ L.2⟩
  naturality _ _ m := ConcreteCategory.hom_ext _ _ fun L =>
    Subtype.ext (D.quotientPullback_quotientSubobject φ m.unop L.1).symm

/-- **The induced quotient determines the quotient of `G_T`**, `φ_T` being an epimorphism. -/
theorem quotientSubobject_injective (T : SchemesOver D.Y) :
    Function.Injective (D.quotientSubobject (hG := hG) φ T) := by
  intro L L' h
  obtain ⟨e, he⟩ := Abelian.exists_iso_of_kernelSubobject_eq _ _ h
  have he' : (D.withModule G hG).quotientProjection T L ≫ e.hom =
      (D.withModule G hG).quotientProjection T L' :=
    (cancel_epi (D.baseChangeModuleMap φ T)).1 (by rw [← Category.assoc]; exact he)
  rw [← kernelSubobject_cokernel_π L, ← kernelSubobject_cokernel_π L']
  show kernelSubobject ((D.withModule G hG).quotientProjection T L) =
    kernelSubobject ((D.withModule G hG).quotientProjection T L')
  rw [← he', kernelSubobject_comp_mono]

/-! ### The image locus -/

/-- For an epimorphism `φ : F ⟶ G`, the sequence `0 ⟶ ker φ ⟶ F ⟶ G ⟶ 0` is short exact. -/
theorem shortExact_kernel :
    (ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ)).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel φ))
    (by dsimp; infer_instance) (by dsimp; infer_instance)

/-- The kernel of a surjection of quasi-coherent modules is quasi-coherent (Stacks 03M1). -/
theorem isQuasicoherentOnSite_kernel_surjection (hG : G.IsQuasicoherentOnSite) :
    (kernel φ).IsQuasicoherentOnSite := by
  have : (ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ)).X₂.IsQuasicoherentOnSite :=
    D.quasicoherent
  have : (ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ)).X₃.IsQuasicoherentOnSite := hG
  exact isQuasicoherent_left_of_shortExact' _ (D.shortExact_kernel φ)

/-- Pullback of modules along a morphism of algebraic spaces preserves zero morphisms. -/
private instance modulePullback_preservesZeroMorphisms {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) : (modulePullback B S hS f).PreservesZeroMorphisms :=
  (modulePullbackSystem B S hS).preservesZeroMorphisms _

omit [Epi φ] in
/-- The base change of `N ⟶ F ⟶ G` vanishes. -/
theorem map_kernel_ι_comp_baseChangeModuleMap (T : SchemesOver D.Y) :
    (modulePullback B S hS (D.sourceProjection T)).map (kernel.ι φ) ≫
      (modulePullback B S hS (D.sourceProjection T)).map φ = 0 := by
  rw [← Functor.map_comp, kernel.condition, Functor.map_zero]

/-- **Right exactness of pullback**: `φ_T` is a cokernel of `N_T ⟶ F_T`. -/
def baseChangeModuleMapIsColimit (T : SchemesOver D.Y) :
    IsColimit (CokernelCofork.ofπ ((modulePullback B S hS (D.sourceProjection T)).map φ)
      (D.map_kernel_ι_comp_baseChangeModuleMap φ T) :
        Cofork ((modulePullback B S hS (D.sourceProjection T)).map (kernel.ι φ)) 0) :=
  have := preservesFiniteColimits_spaceModulePullback (D.sourceProjection T)
  have : (modulePullback B S hS (D.sourceProjection T)).PreservesZeroMorphisms :=
    (modulePullbackSystem B S hS).preservesZeroMorphisms _
  isColimitCoforkMapOfIsColimit' (modulePullback B S hS (D.sourceProjection T)) (kernel.condition φ)
    (Abelian.epiIsCokernelOfKernel (KernelFork.ofι (kernel.ι φ) (kernel.condition φ))
      (kernelIsKernel φ))

/-- **A quotient of `F_T` comes from `G_T` exactly when it kills the image of `N_T`.** -/
theorem exists_quotientSubobject_eq_iff {T : SchemesOver D.Y} {K : Subobject (D.baseChangeModule T)}
    (hK : K ∈ D.properlySupportedQuotients T) :
    (∃ L : Subobject ((D.withModule G hG).baseChangeModule T),
        L ∈ (D.withModule G hG).properlySupportedQuotients T ∧ D.quotientSubobject φ T L = K) ↔
      (modulePullback B S hS (D.sourceProjection T)).map (kernel.ι φ) ≫
        D.quotientProjection T K = 0 := by
  constructor
  · rintro ⟨L, -, rfl⟩
    have hν : (modulePullback B S hS (D.sourceProjection T)).map (kernel.ι φ) ≫
        (D.baseChangeModuleMap φ T ≫ (D.withModule G hG).quotientProjection T L) = 0 := by
      rw [← Category.assoc, D.map_kernel_ι_comp_baseChangeModuleMap φ T, zero_comp]
    exact comp_cokernel_π_kernelSubobject_eq_zero _ _ hν
  · intro h
    let χ : (D.withModule G hG).baseChangeModule T ⟶ D.quotientModule T K :=
      (D.baseChangeModuleMapIsColimit φ T).desc (CokernelCofork.ofπ _ h)
    have hχ : D.baseChangeModuleMap φ T ≫ χ = D.quotientProjection T K :=
      (D.baseChangeModuleMapIsColimit φ T).fac (CokernelCofork.ofπ _ h) WalkingParallelPair.one
    have : Epi χ := epi_of_epi_fac hχ
    refine ⟨kernelSubobject χ, ?_, ?_⟩
    · exact ((D.withModule G hG).mem_properlySupportedQuotients_iff T _).2
        (IsQuotModule.of_iso (Abelian.cokernelKernelSubobjectIso χ).symm
          ((D.mem_properlySupportedQuotients_iff T K).1 hK))
    · exact kernelSubobject_comp_cokernel_π_kernelSubobject _ K χ hχ

omit [Epi φ] in
/-- **The vanishing of `N_T ⟶ F_T ⟶ F_T/K` after base change.** For `t : T' ⟶ T`, the pullback of
`N_T ⟶ F_T ⟶ F_T/K` along `X_{T'} ⟶ X_T` vanishes exactly when `N_{T'} ⟶ F_{T'}` kills the
pulled-back quotient. -/
theorem modulePullback_relativeMap_eq_zero_iff {T' T : SchemesOver D.Y} (g : T' ⟶ T)
    (K : Subobject (D.baseChangeModule T)) :
    (modulePullback B S hS (D.relativeMap g)).map
        ((modulePullback B S hS (D.sourceProjection T)).map (kernel.ι φ) ≫
          D.quotientProjection T K) = 0 ↔
      (modulePullback B S hS (D.sourceProjection T')).map (kernel.ι φ) ≫
        D.quotientProjection T' (D.quotientPullback g K) = 0 :=
  Functor.map_comp_cokernel_π_eq_zero_iff (D.baseChangeComparison g) (kernel.ι φ) K

/-- The value of `Quot_{G/X/B} ⟶ Quot_{F/X/B}` at a test scheme. -/
theorem quotientInclusion_app (T : SchemesOver D.Y)
    (L : (D.withModule G hG).quotFunctor.obj (Opposite.op T)) :
    (D.quotientInclusion φ).app (Opposite.op T) L =
      ⟨D.quotientSubobject φ T L.1, D.quotientSubobject_mem φ L.2⟩ :=
  rfl

omit [Epi φ] in
/-- The restriction maps of `Quot_{F/X/B}`, as structures. -/
private theorem quotFunctor_map_mk {T' T : SchemesOver D.Y} (t : T' ⟶ T)
    (K : Subobject (D.baseChangeModule T)) (hK : K ∈ D.properlySupportedQuotients T) :
    D.quotFunctor.map t.op ⟨K, hK⟩ =
      ⟨D.quotientPullback t K, D.quotientPullback_mem_properlySupportedQuotients t K hK⟩ :=
  rfl

/-- The closed immersions of test schemes over `B`: morphisms of test schemes whose underlying
morphism of schemes is a closed immersion. -/
abbrev closedImmersionOver : MorphismProperty (SchemesOver D.Y) :=
  (MorphismProperty.inverseImage (@AlgebraicGeometry.IsClosedImmersion.{u})
    (BigFppfOver.toScheme B S hS)).inverseImage
      (CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y)

/-- The closed immersions of test schemes over `B` respect isomorphisms. -/
instance : D.closedImmersionOver.RespectsIso :=
  have : (MorphismProperty.inverseImage (@AlgebraicGeometry.IsClosedImmersion.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  MorphismProperty.RespectsIso.inverseImage _ _

/-- **The image locus of `Quot_{G/X/B} ⟶ Quot_{F/X/B}`.** For a point `K` of `Quot_{F/X/B}` over a
test scheme `a`, the morphisms `t : c ⟶ a` of test schemes along which the pullback of `K` comes
from `Quot_{G/X/B}` are those factoring through a fixed closed immersion. -/
theorem exists_imageLocus_quotientInclusion (a : SchemesOver D.Y)
    (y : D.quotFunctor.obj (Opposite.op a)) :
    ∃ (b : SchemesOver D.Y) (s : b ⟶ a), Mono s ∧ D.closedImmersionOver s ∧
      ∀ (c : SchemesOver D.Y) (t : c ⟶ a),
        (∃ x : (D.withModule G hG).quotFunctor.obj (Opposite.op c),
            (D.quotientInclusion φ).app (Opposite.op c) x = D.quotFunctor.map t.op y) ↔
          ∃ r : c ⟶ b, r ≫ s = t := by
  obtain ⟨K, hK⟩ := y
  have hN := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
    (D.sourceProjection a) (kernel φ) (D.isQuasicoherentOnSite_kernel_surjection φ hG)
  obtain ⟨Z, hZ, -, hZloc⟩ := D.exists_isClosedSubspace_modulePullback_eq_zero_iff hK hN
    ((modulePullback B S hS (D.sourceProjection a)).map (kernel.ι φ) ≫ D.quotientProjection a K)
  obtain ⟨V, s₀, hs₀, hV⟩ := exists_forall_factorsThrough_iff_of_presheaf
    (MorphismProperty.inverseImage (@AlgebraicGeometry.IsClosedImmersion.{u})
      (BigFppfOver.toScheme B S hS)) Z (presheaf_isClosedImmersion_of_isClosedSubspace Z hZ)
  have hmono : Mono s₀ := mono_of_isClosedImmersion_toScheme_map s₀ hs₀
  refine ⟨CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map s₀ ≫ a.hom),
    CostructuredArrow.homMk s₀ rfl, ⟨fun r r' h => CostructuredArrow.hom_ext _ _
      (hmono.right_cancellation _ _ (congrArg CommaMorphism.left h))⟩, hs₀, fun c t => ?_⟩
  have hfac : (∃ r : c ⟶ CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map s₀ ≫ a.hom),
      r ≫ CostructuredArrow.homMk s₀ rfl = t) ↔ ∃ r₀ : c.left ⟶ V, r₀ ≫ s₀ = t.left := by
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨r.left, rfl⟩
    · rintro ⟨r₀, hr₀⟩
      refine ⟨CostructuredArrow.homMk r₀ ?_, CostructuredArrow.hom_ext _ _ hr₀⟩
      show (schemeSpaceFunctor B S hS).map r₀ ≫ (schemeSpaceFunctor B S hS).map s₀ ≫ a.hom =
        c.hom
      rw [← Category.assoc, ← Functor.map_comp, hr₀]
      exact CostructuredArrow.w t
  rw [hfac, hV, ← hZloc, D.modulePullback_relativeMap_eq_zero_iff φ,
    ← D.exists_quotientSubobject_eq_iff (hG := hG) φ
      (D.quotientPullback_mem_properlySupportedQuotients t K hK)]
  constructor
  · rintro ⟨⟨L, hL⟩, hx⟩
    have hx' := ((D.quotientInclusion_app (hG := hG) φ c ⟨L, hL⟩).symm.trans hx).trans
      (D.quotFunctor_map_mk t K hK)
    exact ⟨L, hL, congrArg Subtype.val hx'⟩
  · rintro ⟨L, hL, hLK⟩
    exact ⟨⟨L, hL⟩, (D.quotientInclusion_app (hG := hG) φ c ⟨L, hL⟩).trans
      ((Subtype.ext hLK).trans (D.quotFunctor_map_mk t K hK).symm)⟩

/-- Let `φ : F ⟶ G` be a surjection of quasi-coherent `𝒪_X`-modules. The canonical transformation
`Quot_{G/X/B} ⟶ Quot_{F/X/B}` of functors on the test schemes over `B`, sending a quotient
`G_T ⟶ Q` to the quotient `F_T ⟶ G_T ⟶ Q`, is a closed immersion: it is representable by closed
immersions of test schemes.

The Quot functors take values in `Type (u + 1)`, so representability is read through
`CategoryTheory.uliftYoneda`. -/
@[stacks 0DP5]
theorem relative_closedImmersionOver_quotientInclusion :
    D.closedImmersionOver.relative uliftYoneda.{u + 1} (D.quotientInclusion (hG := hG) φ) := by
  refine MorphismProperty.relative_of_injective_of_imageLoci _ _ ?_
    (D.exists_imageLocus_quotientInclusion φ)
  rintro ⟨T⟩ ⟨L, hL⟩ ⟨L', hL'⟩ h
  have h' := ((D.quotientInclusion_app (hG := hG) φ T ⟨L, hL⟩).symm.trans h).trans
    (D.quotientInclusion_app (hG := hG) φ T ⟨L', hL'⟩)
  exact Subtype.ext (D.quotientSubobject_injective φ T (congrArg Subtype.val h'))

end QuotSituation

end AlgebraicGeometry.Space

end
