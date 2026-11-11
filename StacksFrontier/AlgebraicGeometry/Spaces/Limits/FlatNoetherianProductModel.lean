module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ModuleNoetherianModel
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource

/-!
# Noetherian models of a flat space of finite presentation with a module of proper support

Let `X` be an algebraic space flat and of finite presentation over `Spec A` and `F` a module of
finite presentation on `X` whose support is proper over `Spec A`. Writing `Spec A = lim Spec A_λ`
over the finitely generated subrings `A_λ ⊆ A`, the pair `(X, F)` is the base change of a pair
`(X_λ, F_λ)` over some `Spec A_λ`, with `X_λ` flat and of finite presentation over `Spec A_λ`,
and `F_λ` of finite presentation with support proper over `Spec A_λ`.

This is the variant of `AlgebraicGeometry.Space.exists_noetherianProductModel` in which the
flatness is asked of the space rather than of the module: flatness of `X_λ` comes with the stage
model of `X` (`AlgebraicGeometry.Space.exists_stageModel`) and survives base change (Stacks 03MO),
and the module is descended by Stacks 07V7 and 08K2 alone.

## Main results

* `AlgebraicGeometry.Space.exists_modulePullback_productSpaceConeMap_iso_of_hasProperSupport`:
  Stacks 07V7 and 08K2 for the base changes `h_V ⨯ X₀` along a directed system of affine
  schemes whose limit is in the site.
* `AlgebraicGeometry.Space.exists_flatNoetherianProductModel`: the Noetherian model, as a
  cartesian square on the site over `Spec A₀`.

## References

* [Stacks Project, Tag 07V7](https://stacks.math.columbia.edu/tag/07V7)
* [Stacks Project, Tag 08K2](https://stacks.math.columbia.edu/tag/08K2)
* [Stacks Project, Tag 03MO](https://stacks.math.columbia.edu/tag/03MO)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

section ProductDescent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (hZ : B.Contains (⊤_ Scheme.{u})) {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)]
  [Nonempty J] (T : Jᵒᵖ ⥤ BigFppfOver B S hS)
  [∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (T.obj i))]
  {c : Cone T} (hc : IsLimit c) (hcS : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
  (X₀ : AlgebraicSpaces B S hS) {f₀ : X₀ ⟶ schemeSpace (Over.mk (𝟙 (B.obj hS)))}
  (hf₀ : IsFinitePresentation B S hS f₀.hom)

include hZ hc hcS hf₀ in
/-- **Stacks 07V7 and 08K2 together, for the base changes `X_V = h_V ⨯ X₀` along a directed
inverse system `T` of affine schemes with limit `c.pt` in the site.** Let `X₀` be of finite
presentation over `S` and `G` a module of finite presentation on `X_{c.pt}` with support proper
over `c.pt`. Then `G` is the inverse image of a module `N` on some `X_{T j}` which is of finite
presentation with support proper over `T j`. -/
theorem exists_modulePullback_productSpaceConeMap_iso_of_hasProperSupport
    (G : Modules.{u, u} B S hS (productSpace X₀ c.pt).1 (productSpace X₀ c.pt).2)
    (hG : G.IsFinitePresentation)
    (hsupp : HasProperSupport B S hS (productSpace X₀ c.pt).2 (schemeSpace c.pt).2
      (productSpaceFst X₀ c.pt).hom (isFiniteType_of_isFinitePresentation B S hS
        (isFinitePresentation_productSpaceFst hf₀ c.pt)).1 ((SheafOfModules.toSheaf _).obj G)) :
    ∃ (j : J) (N : Modules.{u, u} B S hS (productSpace X₀ (T.obj (op j))).1
        (productSpace X₀ (T.obj (op j))).2),
      N.IsFinitePresentation ∧ N.IsQuasicoherentOnSite ∧ N.IsFinitePresentationOnSite ∧
      HasProperSupport B S hS (productSpace X₀ (T.obj (op j))).2 (schemeSpace (T.obj (op j))).2
        (productSpaceFst X₀ (T.obj (op j))).hom (isFiniteType_of_isFinitePresentation B S hS
          (isFinitePresentation_productSpaceFst hf₀ (T.obj (op j)))).1
        ((SheafOfModules.toSheaf _).obj N) ∧
      Nonempty ((modulePullback B S hS (productSpaceConeMap X₀ T c (op j))).obj N ≅ G) := by
  have hfp (V : BigFppfOver B S hS) := isFinitePresentation_productSpaceFst hf₀ V
  have hlft (V : BigFppfOver B S hS) := (isFiniteType_of_isFinitePresentation B S hS (hfp V)).1
  have hqc (j : Jᵒᵖ) := isQuasiCompactSpace_productSpace hf₀ (T.obj j)
  have hqs (j : Jᵒᵖ) := isAbsolutelyQuasiSeparated_productSpace hZ hf₀ (T.obj j)
  -- Stacks 07V7: a model `N` of `G` over some stage
  obtain ⟨j₁, -, N, hNq, hNfp, ⟨ι⟩⟩ := exists_modulePullback_productSpaceConeMap_iso X₀ c hcS
    (op (Classical.arbitrary J)) hZ (hqc _) (hqs _) G
    (isQuasicoherentOnSite_of_isFinitePresentation G hG)
    (isFinitePresentationOnSite_of_isFinitePresentation' G hG)
  have hNfp' : N.IsFinitePresentation :=
    SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite' N hNfp
  -- Stacks 08K2: proper support over a later stage
  obtain ⟨j₂, h₁₂, hlft₂, hP₂⟩ := exists_hasProperSupport_productSpaceMap hZ T hc hcS X₀ j₁.unop
    (hqc _) (hqs _) (hlft _) N hNq (isFiniteTypeOnSite_of_isFinitePresentation' N hNfp')
    (hlft c.pt) (hasProperSupport_of_iso (schemeSpace c.pt).2 _ (hlft c.pt) ι.symm hsupp)
  let N₂ := (modulePullback B S hS (productSpaceMap X₀ (T.map (homOfLE h₁₂).op))).obj N
  have hN₂fp : N₂.IsFinitePresentation := isFinitePresentation_modulePullback _ N hNfp'
  have hcw : productSpaceMap X₀ (V := c.pt) (c.π.app (op j₂)) ≫
      productSpaceMap X₀ (T.map (homOfLE h₁₂).op) =
        productSpaceMap X₀ (V := c.pt) (c.π.app (op j₁.unop)) := by
    rw [← productSpaceMap_comp, c.w]
  refine ⟨j₂, N₂, hN₂fp, isQuasicoherentOnSite_of_isFinitePresentation N₂ hN₂fp,
    isFinitePresentationOnSite_of_isFinitePresentation' N₂ hN₂fp, ?_, ⟨?_⟩⟩
  · exact hP₂
  · exact (modulePullbackCompIso B S hS _ _).app N ≪≫
      eqToIso (congrArg (fun φ => (modulePullback B S hS φ).obj N) hcw) ≪≫ ι

end ProductDescent

section ModulePullback

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y X' Y' : AlgebraicSpaces B S hS} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- In a cartesian square, the pullback of a module of finite presentation with support proper
over `Y` is of finite presentation with support proper over `Y'`. -/
theorem modulePullback_finitePresentation_hasProperSupport (sq : IsPullback g' f' f g)
    (hft : IsLocallyOfFiniteType B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hFfp : F.IsFinitePresentation)
    (hFsupp : HasProperSupport B S hS X.2 Y.2 f.hom hft ((SheafOfModules.toSheaf _).obj F)) :
    ((modulePullback B S hS g').obj F).IsFinitePresentation ∧
      HasProperSupport B S hS X'.2 Y'.2 f'.hom
        ((isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback sq hft)
        ((SheafOfModules.toSheaf _).obj ((modulePullback B S hS g').obj F)) := by
  have hqc := isQuasicoherentOnSite_of_isFinitePresentation F hFfp
  have hfin := isFiniteTypeOnSite_of_isFinitePresentation F hFfp
  exact ⟨isFinitePresentation_modulePullback g' F hFfp,
    isClosed_supportOfSheaf_modulePullback B S hS g' F hfin,
    isProperOver_supportOfSheaf_modulePullback B S hS sq hft F hqc hfin hFsupp.2⟩

end ModulePullback

section Model

variable (B : BigFppfSite.{u}) {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}
  {X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}

include B in
/-- **Noetherian approximation of a flat space of finite presentation with a module of finite
presentation and proper support.** Let `X` be an algebraic space flat and of finite presentation
over `Spec A` and `F` an `𝒪_X`-module of finite presentation with support proper over `Spec A`.
Then there are a ring `A₀ ⊆ A` of finite type over `ℤ`, an affine Noetherian scheme `Y₀` over
`Spec A₀` with a morphism `y : Spec A ⟶ Y₀` over `Spec A₀`, an algebraic space `X₀` flat and of
finite presentation over `Y₀` and an `𝒪_{X₀}`-module `F₀` of finite presentation with support
proper over `Y₀`, such that on the site over `Spec A₀` the lower-shriek extension `Λ X` of `X` is
the base change `X₀ ×_{Y₀} Spec A` along a morphism `a : Λ X ⟶ X₀` and the module of `Λ X`
attached to `F` is `a^* F₀`. -/
theorem exists_flatNoetherianProductModel (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
    (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA))))
    (hfp : IsFinitePresentation B (Spec (.of A)) hA f) (hfl : IsFlat B (Spec (.of A)) hA f)
    (F : Modules.{u, u} B (Spec (.of A)) hA X hX) (hF : F.IsFinitePresentation)
    (hsupp : HasProperSupport B (Spec (.of A)) hA hX
      (isAlgebraicSpace_yoneda B (Spec (.of A)) hA (Over.mk (𝟙 (B.obj hA)))) f
      (isFiniteType_of_isFinitePresentation B _ hA hfp).1 ((SheafOfModules.toSheaf _).obj F)) :
    ∃ (A₀ : Type u) (_ : CommRing A₀) (_ : Algebra A₀ A) (_ : Algebra.FiniteType ℤ A₀)
      (hA₀ : B.Contains (Spec (.of A₀))) (g : B.obj hA ⟶ B.obj hA₀)
      (_ : B.inclusion.map g = Spec.map (CommRingCat.ofHom (algebraMap A₀ A)))
      (Y₀ : BigFppfOver B (Spec (.of A₀)) hA₀) (y : Over.mk g ⟶ Y₀)
      (X₀ : AlgebraicSpaces B (Spec (.of A₀)) hA₀) (f₀ : X₀ ⟶ schemeSpace Y₀)
      (hf₀ : IsFinitePresentation B (Spec (.of A₀)) hA₀ f₀.hom)
      (F₀ : Modules.{u, u} B (Spec (.of A₀)) hA₀ X₀.1 X₀.2)
      (a : relocalizeSpace B hA hA₀ g ⟨X, hX⟩ ⟶ X₀),
      IsAffine ((BigFppfOver.toScheme B _ hA₀).obj Y₀) ∧
      IsNoetherian B (Spec (.of A₀)) hA₀ (BigFppfSite.contains_terminal B) (schemeSpace Y₀).1 ∧
      IsFlat B (Spec (.of A₀)) hA₀ f₀.hom ∧
      F₀.IsFinitePresentation ∧ F₀.IsQuasicoherentOnSite ∧ F₀.IsFinitePresentationOnSite ∧
      HasProperSupport B (Spec (.of A₀)) hA₀ X₀.2 (schemeSpace Y₀).2 f₀.hom
        (isFiniteType_of_isFinitePresentation B _ hA₀ hf₀).1 ((SheafOfModules.toSheaf _).obj F₀) ∧
      IsPullback a (ObjectProperty.homMk (OverShriek.viewStructureMap g X) :
          relocalizeSpace B hA hA₀ g ⟨X, hX⟩ ⟶ schemeSpace (Over.mk g)) f₀ (schemeSpaceMap y) ∧
      Nonempty ((relocalizeModulesEquivalence B hA hA₀ g X hX).functor.obj F ≅
        (modulePullback B (Spec (.of A₀)) hA₀ a).obj F₀) := by
  classical
  obtain ⟨i, X₀, hX₀, f₀, hfp₀, -, hfl₀, hiso⟩ := exists_stageModel B hX f hfp
  let h₀ := contains_specAdjoinFinsetDiagram_obj B i
  let g : B.obj hA ⟶ B.obj h₀ := ObjectProperty.homMk ((specAdjoinFinsetCone A).π.app i)
  obtain ⟨e⟩ := hiso g rfl
  -- the system of stages above `i`, over the stage `i`
  have : Nonempty (Set.Ici i.unop) := ⟨⟨i.unop, Set.mem_Ici.mpr le_rfl⟩⟩
  have := directed_tail i.unop
  let T := specAdjoinTail B A i.unop
  let cT := specAdjoinTailCone B A hA i.unop
  let X₀s : AlgebraicSpaces B _ h₀ := ⟨X₀, hX₀⟩
  -- `Λ X` is the base change of `X₀` to `Spec A`
  let ψ : relocalizeSpace B hA h₀ g ⟨X, hX⟩ ≅ productSpace X₀s cT.pt :=
    ObjectProperty.isoMk _ ((OverShriek.relocalizePresheafFunctor g).mapIso e ≪≫
      OverShriek.relocalizeRestrictIsoProduct g X₀)
  have hψ : (ψ.hom ≫ productSpaceFst X₀s cT.pt).hom = OverShriek.viewStructureMap g X := by
    change ((OverShriek.relocalizePresheafFunctor g).map e.hom ≫
      (OverShriek.relocalizeRestrictIsoProduct g X₀).hom) ≫ prod.fst = _
    rw [Category.assoc, OverShriek.relocalizeRestrictIsoProduct_hom_fst,
      OverShriek.relocalize_map_viewStructureMap]
  -- the module of `Λ X` attached to `F`, read on the base change
  let Ys : AlgebraicSpaces B _ hA := schemeSpace (Over.mk (𝟙 (B.obj hA)))
  let fs : (⟨X, hX⟩ : AlgebraicSpaces B _ hA) ⟶ Ys := ObjectProperty.homMk f
  let frel := relocalizeHom B hA h₀ g fs
  have hlft := (isFiniteType_of_isFinitePresentation B _ hA hfp).1
  let θ : schemeSpace cT.pt ≅ relocalizeSpace B hA h₀ g Ys :=
    (asIso (relocalizeBaseHom B hA h₀ g)).symm
  have h1 : frel ≫ θ.inv = ψ.hom ≫ productSpaceFst X₀s cT.pt :=
    ObjectProperty.hom_ext _ ((relocalizeHom_comp_relocalizeBaseHom B hA h₀ g hX fs).trans hψ.symm)
  have sq : IsPullback ψ.inv (productSpaceFst X₀s cT.pt) frel θ.hom := IsPullback.of_horiz_isIso
    ⟨(Iso.inv_comp_eq ψ).2 (((Iso.comp_inv_eq θ).1 h1).trans (Category.assoc _ _ _))⟩
  -- the module on the base change: finite presentation and proper support
  obtain ⟨hGfp, hGsupp⟩ := modulePullback_finitePresentation_hasProperSupport sq
    ((isLocallyOfFiniteType_relocalize_iff B _ hA _ h₀ g f).2 hlft)
    ((relocalizeModulesEquivalence B hA h₀ g X hX).functor.obj F)
    (isFinitePresentation_relocalizeModulesEquivalence_functor B hA h₀ g X hX F hF)
    ((hasProperSupport_relocalizeModulesEquivalence_functor_iff B hA h₀ g hX Ys.2 f hlft F).2 hsupp)
  -- Stacks 07V7 and 08K2 along the system
  obtain ⟨j, N, hNfp, hNq, hNos, hNsupp, ⟨ι⟩⟩ :=
    exists_modulePullback_productSpaceConeMap_iso_of_hasProperSupport B.contains_terminal T
      (isLimit_specAdjoinTailCone B A hA i.unop) (isLimit_toScheme_specAdjoinTailCone B A hA i.unop)
      X₀s (f₀ := ObjectProperty.homMk f₀) hfp₀ _ hGfp hGsupp
  -- Stacks 03MO: the model is flat
  have := isFlat_isStableUnderBaseChange B _ h₀
  have hflj : IsFlat B _ h₀ (productSpaceFst X₀s (T.obj (op j))).hom :=
    MorphismProperty.of_isPullback (P := fun ⦃F G : AlgebraicSpaces B _ h₀⦄ (φ : F ⟶ G) =>
      IsFlat B _ h₀ φ.hom) (isPullback_productSpaceSnd_productSpaceFst X₀s (T.obj (op j))
        (ObjectProperty.homMk f₀)) (hfl₀ hfl)
  exact ⟨Algebra.adjoin ℤ (i.unop : Set A), inferInstance, inferInstance,
    finiteType_adjoinFinset_int A i.unop, h₀, g, rfl, _, cT.π.app (op j), _,
    productSpaceFst X₀s (T.obj (op j)), isFinitePresentation_productSpaceFst hfp₀ _, N,
    ψ.hom ≫ productSpaceConeMap X₀s T cT (op j), isAffine_specAdjoinFinsetDiagram_obj A (op j.val),
    isNoetherian_schemeSpace B.contains_terminal (T.obj (op j))
      (hV := isNoetherian_specAdjoinTail_obj B A i.unop (op j)), hflj, hNfp, hNq, hNos,
    hNsupp, isPullback_comp_productSpaceMap_of_iso X₀s ψ (cT.π.app (op j))
      (ObjectProperty.hom_ext _ hψ), ⟨modulePullbackIsoOfIso ψ _ ι⟩⟩

end Model

end AlgebraicGeometry.Space
