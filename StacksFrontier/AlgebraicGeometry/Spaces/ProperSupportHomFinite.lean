module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperExtFiniteOverAffineObject
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentSchemeTheoreticSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ModuleSupportProperDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardBaseScalars
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPushforwardCoherentProperSupport
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.CategoryTheory.Sites.Modules.GlobalSmulFunctoriality
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact

/-!
# Morphisms into a coherent module with proper support form a finite module

Let `V` be an object of the big fppf site of `S` whose scheme is affine and locally Noetherian,
let `f : X ⟶ V` be a morphism of algebraic spaces locally of finite type, and let `M`, `N` be
coherent `𝒪_X`-modules, the support of `N` being proper over `V` (Stacks 0CZD). Then
`Hom_{𝒪_X}(M, N)` is a finite `Γ(V, 𝒪_V)`-module, the functions on `V` acting through `f`.

This is the finiteness used for axiom [3] in Stacks 0CZW, where the source cites Stacks 08AR
(finiteness of the cohomology of coherent sheaves on proper algebraic spaces over a field). The
proof reduces to the proper case along the scheme-theoretic support. Let `i : Z ⟶ X` be the
scheme-theoretic support of `N` (Stacks 07U0) and `G` the coherent `𝒪_Z`-module with
`i_*G ≅ N` (Stacks 07UG). Then `Z` is proper over `V` (Stacks 0CZI), `i^*M` is coherent, and
`Hom_X(M, N) = Hom_X(M, i_*G) = Hom_Z(i^*M, G)`, which embeds into
`Hom_{D(𝒪_Z)}(i^*M, G)`. That group is finite by Stacks 0D0T over the affine object `V`
(`AlgebraicGeometry.Space.moduleFinite_hom_shift_of_isProper_toAffineObject`). Each
identification is `Γ(V, 𝒪_V)`-linear because `i_*` and hence its left adjoint `i^*` commute with
multiplication by the functions pulled back from `V`.

## Main results

* `AlgebraicGeometry.Space.modulePullback_map_globalSmul_pullbackToGlobalFunctions`: the inverse
  image of modules commutes with multiplication by pulled-back functions.
* `AlgebraicGeometry.Space.moduleFinite_hom_of_hasProperSupport_toAffineObject`: the finiteness
  above.

## References

* [Stacks Project, Tag 08AR](https://stacks.math.columbia.edu/tag/08AR)
* [Stacks Project, Tag 0D0T](https://stacks.math.columbia.edu/tag/0D0T)
* [Stacks Project, Tag 07U0](https://stacks.math.columbia.edu/tag/07U0)
* [Stacks Project, Tag 07UG](https://stacks.math.columbia.edu/tag/07UG)
* [Stacks Project, Tag 0CZI](https://stacks.math.columbia.edu/tag/0CZI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Cohomology.SiteModules

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The inverse image of modules commutes with multiplication by pulled-back functions.** For
`f : X ⟶ Y`, `h : Y ⟶ T` with `T` an object of the site, an `𝒪_Y`-module `M` and a function `x`
on `T`, the inverse image of multiplication by `h^♯ x` on `M` is multiplication by
`(f ≫ h)^♯ x` on `f^*M`. This is the left adjoint form of
`AlgebraicGeometry.Space.modulePushforward_map_globalSmul_pullbackToGlobalFunctions`. -/
theorem modulePullback_map_globalSmul_pullbackToGlobalFunctions {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) {T : BigFppfOver B S hS} (h : Y ⟶ schemeSpace T)
    (M : Modules.{u, u} B S hS Y.1 Y.2) (x : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) :
    (modulePullback B S hS f).map
        (globalSmul
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))
          (pullbackToGlobalFunctions B S hS Y T h x) M) =
      globalSmul ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
        (pullbackToGlobalFunctions B S hS X T (f ≫ h) x) ((modulePullback B S hS f).obj M) :=
  Stacks.SheafOfModules.map_globalSmul_of_adjunction (modulePullbackAdjunction B S hS f) _ _
    (fun N => modulePushforward_map_globalSmul_pullbackToGlobalFunctions B S hS f h N x) M

/-- **The inverse image along a morphism over an object of the site is linear** over the
functions of that object, acting on both sides through the pulled-back functions. -/
theorem modulePullback_linear_objectRingHom (V : BigFppfOver B S hS)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (h : Y ⟶ schemeSpace V) :
    letI := Stacks.SheafOfModules.linearOver
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)
      (objectRingHom V h)
    letI := Stacks.SheafOfModules.linearOver
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
      (objectRingHom V (f ≫ h))
    (modulePullback B S hS f).Linear Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
  Stacks.SheafOfModules.linear_of_map_globalSmul _ _ _
    (fun a M => modulePullback_map_globalSmul_pullbackToGlobalFunctions f h M a)

/-- An object placed in degree zero is cohomologically bounded above. -/
theorem _root_.DerivedCategoryB.isBoundedAbove_singleFunctor_obj {A : Type*} [Category A]
    [Abelian A] [HasDerivedCategory A] (M : A) :
    DerivedCategoryB.IsBoundedAbove ((DerivedCategory.singleFunctor A 0).obj M) :=
  ⟨0, fun _ hn => DerivedCategory.isZero_of_isLE _ 0 _ hn⟩

/-- **Morphisms into a coherent module with proper support form a finite module.** Let `V` be
an object of the site whose scheme is affine and locally Noetherian, `f : X ⟶ V` a morphism of
algebraic spaces locally of finite type, and `M`, `N` coherent `𝒪_X`-modules with the support of
`N` proper over `V`. Then `Hom_{𝒪_X}(M, N)` is a finite `Γ(V, 𝒪_V)`-module, the functions on `V`
acting through `f`. -/
theorem moduleFinite_hom_of_hasProperSupport_toAffineObject (V : BigFppfOver B S hS)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)] {X : AlgebraicSpaces B S hS}
    (f : X ⟶ schemeSpace V) (hf : IsLocallyOfFiniteType B S hS f.hom)
    (M N : Modules.{u, u} B S hS X.1 X.2) (hM : IsCoherent B S hS X.1 X.2 M)
    (hN : IsCoherent B S hS X.1 X.2 N)
    (hsupp : HasProperSupport B S hS X.2 (schemeSpace V).2 f.hom hf
      ((SheafOfModules.toSheaf _).obj N)) :
    letI := Stacks.SheafOfModules.linearOver
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
      (objectRingHom V f)
    Module.Finite Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) (M ⟶ N) := by
  have : IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
    have := hV
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  have hVN : HasEtaleLocalProperty B S hS (yoneda.obj V)
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
    hasEtaleLocalProperty_of_representable B S hS _ _ V (Iso.refl _) inferInstance
  have hXN : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS X.2 (schemeSpace V).2 f.hom hf hVN
  have hNft : SheafOfModules.IsFiniteTypeOnSite N :=
    isFiniteTypeOnSite_of_isCoherentOnSite B S hS X N
  -- the scheme-theoretic support `i : Z ⟶ X` of `N` and the module `G` on it with `i_*G ≅ N`
  let Z := coherentSchemeTheoreticSupport B S hS X N
  let i := closedSubspaceInclusion B S hS X Z
  have hex := exists_module_on_schemeTheoreticSupport B S hS X N hN.toIsQuasicoherentOnSite
    (Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteTypeOnSite N hNft)
  let G : Modules.{u, u} B S hS (closedSubspaceToSpace B S hS X Z).1
      (closedSubspaceToSpace B S hS X Z).2 := hex.choose_spec.choose
  have hGqc : G.IsQuasicoherentOnSite := hex.choose_spec.choose_spec.1
  let e : (modulePushforward B S hS i).obj G ≅ N := hex.choose_spec.choose_spec.2.some
  have hG : IsCoherent B S hS (closedSubspaceToSpace B S hS X Z).1
      (closedSubspaceToSpace B S hS X Z).2 G :=
    isCoherent_module_on_coherentSchemeTheoreticSupport B S hS X hXN N G hGqc e
  -- `Z` is proper over `V`
  let g : closedSubspaceToSpace B S hS X Z ⟶ schemeSpace V := i ≫ f
  have hg : IsProper B S hS g.hom :=
    (isProper_schemeTheoreticSupport_iff_isProperOver B S hS X (schemeSpace V) f.hom hf N
      hN.toIsQuasicoherentOnSite hNft hsupp.1).2 hsupp.2
  have hZN : HasEtaleLocalProperty B S hS (closedSubspaceToSpace B S hS X Z).1
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS (closedSubspaceToSpace B S hS X Z).2
      (schemeSpace V).2 g.hom hg.2.1.1 hVN
  have : Fact (HasEtaleLocalProperty B S hS (closedSubspaceToSpace B S hS X Z).1
      (fun T : Scheme.{u} => IsLocallyNoetherian T)) := ⟨hZN⟩
  have hiM : IsCoherent B S hS (closedSubspaceToSpace B S hS X Z).1
      (closedSubspaceToSpace B S hS X Z).2 ((modulePullback B S hS i).obj M) :=
    isCoherent_modulePullback B S hS i M hM
  -- the linear structures
  let R := Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
  let LX := Stacks.SheafOfModules.linearOver
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
    (objectRingHom V f)
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS (closedSubspaceToSpace B S hS X Z).1
    (closedSubspaceToSpace B S hS X Z).2)
  let LZ := Stacks.SheafOfModules.linearOver
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
      (closedSubspaceToSpace B S hS X Z).1 (closedSubspaceToSpace B S hS X Z).2).O)
    (objectRingHom V g)
  have := modulePushforward_additive B S hS i
  have : (modulePullback B S hS i).Additive :=
    Adjunction.left_adjoint_additive (modulePullbackAdjunction B S hS i)
  have : (modulePullback B S hS i).Linear R := modulePullback_linear_objectRingHom V i f
  -- Stacks 0D0T on `Z`
  have hW := isWeakSerre_isCoherent B S hS (closedSubspaceToSpace B S hS X Z).1
    (closedSubspaceToSpace B S hS X Z).2
  let D₁ := (DerivedCategory.singleFunctor _ 0).obj ((modulePullback B S hS i).obj M)
  let D₂ := (DerivedCategory.singleFunctor _ 0).obj G
  have hfin : Module.Finite R (D₁ ⟶ D₂⟦(0 : ℤ)⟧) :=
    moduleFinite_hom_shift_of_isProper_toAffineObject B S hS V hV g hg D₁ D₂
      ⟨DerivedCategoryB.isBoundedAbove_singleFunctor_obj _,
        (DerivedCategoryB.derivedCategoryBPlus_singleFunctor_obj _ hW _ hiM).2⟩
      (DerivedCategoryB.derivedCategoryBPlus_singleFunctor_obj _ hW _ hG) 0
  -- the embedding `Hom_X(M, N) ⟶ Hom_{D(𝒪_Z)}(i^*M, G[0])`
  let adj := modulePullbackAdjunction B S hS i
  let Φ : (M ⟶ N) →ₗ[R] (D₁ ⟶ D₂⟦(0 : ℤ)⟧) :=
    (Linear.homCongr R (Iso.refl D₁)
        ((shiftFunctorZero (DerivedCategory _) ℤ).symm.app D₂)).toLinearMap ∘ₗ
      (DerivedCategory.singleFunctor _ 0).mapLinearMap R ∘ₗ
      Linear.rightComp R _ (adj.counit.app G) ∘ₗ
      (modulePullback B S hS i).mapLinearMap R ∘ₗ
      (Linear.homCongr R (Iso.refl M) e.symm).toLinearMap
  have h₂ : Function.Injective ((DerivedCategory.singleFunctor _ 0).mapLinearMap R :
      (((modulePullback B S hS i).obj M) ⟶ G) →ₗ[R] (D₁ ⟶ D₂)) :=
    fun a b hab => (DerivedCategory.singleFunctor _ 0).map_injective hab
  have h₃ : Function.Injective (Linear.rightComp R _ (adj.counit.app G) ∘ₗ
      (modulePullback B S hS i).mapLinearMap R :
        (M ⟶ (modulePushforward B S hS i).obj G) →ₗ[R] _) := fun a b hab =>
    (adj.homEquiv _ _).symm.injective
      (by rwa [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit])
  exact Module.Finite.of_injective Φ ((Linear.homCongr R (Iso.refl D₁)
      ((shiftFunctorZero (DerivedCategory _) ℤ).symm.app D₂)).injective.comp
    (h₂.comp (h₃.comp (Linear.homCongr R (Iso.refl M) e.symm).injective)))

end AlgebraicGeometry.Space

end
