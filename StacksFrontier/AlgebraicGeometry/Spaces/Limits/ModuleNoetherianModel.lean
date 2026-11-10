module

public import StacksFrontier.AlgebraicGeometry.Limits.SmallDominantIndex
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorPresheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.NoetherianStageModel
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ProductFlatDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ProductModuleObjects
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ProductProperSupportDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeChartReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeModulesFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeSlice
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteUniverses

/-!
# Noetherian models of modules of finite presentation, flat with proper support

Let `X` be an algebraic space of finite presentation over `Spec A` and `F` a module of finite
presentation on `X`, flat over `Spec A` and with support proper over `Spec A`. Writing
`Spec A = lim Spec A_λ` over the finitely generated subrings `A_λ ⊆ A`, the pair `(X, F)` is the
base change of a pair `(X_λ, F_λ)` over some `Spec A_λ` with the same properties. This is the
reduction to the Noetherian case in the proof of Stacks 0A1P.

## Main results

* `AlgebraicGeometry.Space.exists_modulePullback_productSpaceConeMap_iso_of_isFlatOver`:
  Stacks 07V7, 70.6.12 and 08K2 for the base changes `h_V ⨯ X₀` along a directed system of affine
  schemes whose limit is in the site.
* `AlgebraicGeometry.Space.exists_noetherianProductModel`: the Noetherian model, as a cartesian
  square on the site over `Spec A₀`.

## Implementation notes

The model lives on the site over the stage `Spec A₀` given by
`AlgebraicGeometry.Space.exists_stageModel`, to which `X` is carried by the lower-shriek extension
`Λ`: there `Λ X` is the base change `h_{Spec A} ⨯ X₀`, the module of `Λ X` attached to `F` is
transported along this identification, and the descent results along the system of the stages
`Spec A_λ ⟶ Spec A₀` apply. No bound on the size of the index set enters.

## References

* [Stacks Project, Tag 07V7](https://stacks.math.columbia.edu/tag/07V7)
* [Stacks Project, Tag 08K2](https://stacks.math.columbia.edu/tag/08K2)
* [Stacks Project, Tag 0A1P](https://stacks.math.columbia.edu/tag/0A1P)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### The Noetherian approximation of `Spec A` as a system over a stage -/

section System

variable (B : BigFppfSite.{u}) (A : Type u) [CommRing A] (hA : B.Contains (Spec (.of A)))
  (i : Finset A)

/-- The spectra of the finitely generated subalgebras of `A`, as objects of the site. -/
def specAdjoinFinsetSiteDiagram : (Finset A)ᵒᵖ ⥤ B.Schemes :=
  ObjectProperty.lift _ (specAdjoinFinsetDiagram A) (contains_specAdjoinFinsetDiagram_obj B)

/-- `Spec A` as a cone over `specAdjoinFinsetSiteDiagram`. -/
def specAdjoinFinsetSiteCone : Cone (specAdjoinFinsetSiteDiagram B A) where
  pt := B.obj hA
  π :=
    { app j := ObjectProperty.homMk ((specAdjoinFinsetCone A).π.app j)
      naturality _ _ a := ObjectProperty.hom_ext _ ((specAdjoinFinsetCone A).π.naturality a) }

/-- `Spec A` is the limit of the spectra of the finitely generated subalgebras in the site. -/
def isLimit_specAdjoinFinsetSiteCone : IsLimit (specAdjoinFinsetSiteCone B A hA) :=
  isLimitOfReflects B.inclusion (isLimit_specAdjoinFinsetCone A)

/-- The tail above `i` of the Noetherian approximation, as a system over the stage `Spec ℤ[i]`. -/
def specAdjoinTail :
    (Set.Ici i)ᵒᵖ ⥤ BigFppfOver B _ (contains_specAdjoinFinsetDiagram_obj B (op i)) :=
  tailToOver i ⋙ Over.post (specAdjoinFinsetSiteDiagram B A)

/-- `Spec A` as a cone over the tail. -/
def specAdjoinTailCone : Cone (specAdjoinTail B A i) :=
  ((Over.conePost (specAdjoinFinsetSiteDiagram B A) (op i)).obj
    (specAdjoinFinsetSiteCone B A hA)).whisker (tailToOver i)

/-- Every scheme in the tail above `i` is affine. -/
instance (j : (Set.Ici i)ᵒᵖ) : IsAffine ((BigFppfOver.toScheme B _ _).obj
    ((specAdjoinTail B A i).obj j)) :=
  isAffine_specAdjoinFinsetDiagram_obj A (op j.unop.val)

/-- Every scheme in the tail above `i` is Noetherian. -/
instance isNoetherian_specAdjoinTail_obj (j : (Set.Ici i)ᵒᵖ) :
    _root_.AlgebraicGeometry.IsNoetherian
      ((BigFppfOver.toScheme B _ _).obj ((specAdjoinTail B A i).obj j)) :=
  inferInstanceAs
    (_root_.AlgebraicGeometry.IsNoetherian ((specAdjoinFinsetDiagram A).obj (op j.unop.val)))

/-- The structure morphism of the cone point of `specAdjoinTailCone` is the projection
`Spec A ⟶ Spec ℤ[i]`. -/
theorem specAdjoinTailCone_pt_hom : (specAdjoinTailCone B A hA i).pt.hom =
    ObjectProperty.homMk ((specAdjoinFinsetCone A).π.app (op i)) := rfl

/-- The tail cone is a limit in the site. -/
def isLimit_specAdjoinTailCone : IsLimit (specAdjoinTailCone B A hA i) :=
  haveI := initial_tailToOver i
  (Functor.Initial.isLimitWhiskerEquiv (tailToOver i) _).symm
    (Over.isLimitConePost (op i) (isLimit_specAdjoinFinsetSiteCone B A hA))

/-- The underlying schemes of the tail cone form a limit. -/
def isLimit_toScheme_specAdjoinTailCone :
    IsLimit ((BigFppfOver.toScheme B _ _).mapCone (specAdjoinTailCone B A hA i)) :=
  haveI := initial_tailToOver i
  (Functor.Initial.isLimitWhiskerEquiv (tailToOver i ⋙ Over.forget _) _).symm
    (isLimit_specAdjoinFinsetCone A)

end System

/-! ### Base changes of a space of finite presentation over the base -/

section ProductSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (X₀ : AlgebraicSpaces B S hS)

/-- The morphism of a scheme over `S` to the final object `S` of the site. -/
abbrev toBaseHom (V : BigFppfOver B S hS) : V ⟶ Over.mk (𝟙 (B.obj hS)) :=
  Over.homMk V.hom (Category.comp_id _)

/-- **The base change `h_V ⨯ X₀` is the fibre product of `X₀` and `h_V` over the base.** -/
theorem isPullback_productSpaceSnd_productSpaceFst (V : BigFppfOver B S hS)
    (f₀ : X₀ ⟶ schemeSpace (Over.mk (𝟙 (B.obj hS)))) :
    IsPullback (productSpaceSnd X₀ V) (productSpaceFst X₀ V) f₀ (schemeSpaceMap (toBaseHom V)) := by
  let t := isTerminal_yoneda_obj_base B S hS
  have h : IsPullback (prod.snd : yoneda.obj V ⨯ X₀.1 ⟶ X₀.1) prod.fst f₀.hom
      (yoneda.map (toBaseHom V)) := by
    rw [t.hom_ext f₀.hom (t.from _), t.hom_ext (yoneda.map (toBaseHom V)) (t.from _)]
    exact (IsPullback.of_is_product' (prodIsProd (yoneda.obj V) X₀.1) t).flip
  exact IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ h.w) h

/-- **The base change along a morphism of schemes is cartesian**, in algebraic spaces. -/
theorem isPullback_productSpaceMap_schemeSpaceMap {V V' : BigFppfOver B S hS} (k : V ⟶ V') :
    IsPullback (productSpaceMap X₀ k) (productSpaceFst X₀ V) (productSpaceFst X₀ V')
      (schemeSpaceMap k) :=
  IsPullback.of_map (ObjectProperty.ι _)
    (ObjectProperty.hom_ext _ (isPullback_productSpaceMap X₀ k).w) (isPullback_productSpaceMap X₀ k)

/-- The base change square along a morphism of schemes, precomposed with an isomorphism onto the
base change, is cartesian. -/
theorem isPullback_comp_productSpaceMap_of_iso {M : AlgebraicSpaces B S hS}
    {V V' : BigFppfOver B S hS} (ψ : M ≅ productSpace X₀ V) (k : V ⟶ V')
    {b : M ⟶ schemeSpace V} (hb : ψ.hom ≫ productSpaceFst X₀ V = b) :
    IsPullback (ψ.hom ≫ productSpaceMap X₀ k) b (productSpaceFst X₀ V') (schemeSpaceMap k) := by
  subst hb
  have sq : IsPullback ψ.hom (ψ.hom ≫ productSpaceFst X₀ V) (productSpaceFst X₀ V) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨(Category.comp_id _).symm⟩
  have := sq.paste_horiz (isPullback_productSpaceMap_schemeSpaceMap X₀ k)
  rwa [Category.id_comp] at this

/-- An affine Noetherian scheme is a Noetherian algebraic space. -/
theorem isNoetherian_schemeSpace (hZ : B.Contains (⊤_ Scheme.{u})) (V : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [hV : _root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj V)] :
    IsNoetherian B S hS hZ (schemeSpace V).1 :=
  ⟨isQuasiCompactSpace_yoneda_of_isAffine B S hS V inferInstance,
    isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S hS _ hZ
      ⟨_, inferInstance, ⟨Functor.RepresentableBy.yoneda _⟩⟩,
    (exists_atlas_iff_of_representable B S hS _ _ V (Iso.refl _)).2
      (inferInstanceAs
        (_root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)))⟩

variable {X₀} {f₀ : X₀ ⟶ schemeSpace (Over.mk (𝟙 (B.obj hS)))}

/-- The base change of a space of finite presentation over the base is of finite presentation
over the scheme. -/
theorem isFinitePresentation_productSpaceFst (hf₀ : IsFinitePresentation B S hS f₀.hom)
    (V : BigFppfOver B S hS) : IsFinitePresentation B S hS (productSpaceFst X₀ V).hom :=
  MorphismProperty.of_isPullback (P := fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) =>
    IsFinitePresentation B S hS f.hom) (isPullback_productSpaceSnd_productSpaceFst X₀ V f₀) hf₀

/-- The base change of a space of finite presentation over the base to an affine scheme is
quasi-compact. -/
theorem isQuasiCompactSpace_productSpace (hf₀ : IsFinitePresentation B S hS f₀.hom)
    (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] :
    IsQuasiCompactSpace B S hS (productSpace X₀ V).1 :=
  isQuasiCompactSpace_source_of_isQuasiCompact B S hS (schemeSpace V).2
    (isQuasiCompactSpace_yoneda_of_isAffine B S hS V inferInstance)
    (isFinitePresentation_productSpaceFst hf₀ V).2.1

/-- The base change of a space of finite presentation over the base to an affine scheme is
quasi-separated. -/
theorem isAbsolutelyQuasiSeparated_productSpace (hZ : B.Contains (⊤_ Scheme.{u}))
    (hf₀ : IsFinitePresentation B S hS f₀.hom) (V : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] :
    IsAbsolutelyQuasiSeparated B S hS hZ (productSpace X₀ V).1 :=
  isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ (productSpace X₀ V).2
    (isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S hS _ hZ
      ⟨_, inferInstance, ⟨Functor.RepresentableBy.yoneda _⟩⟩)
    (isFinitePresentation_productSpaceFst hf₀ V).2.2

end ProductSpace

/-! ### Descent of a module along a limit of affine base changes -/

section ProductDescent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A module of finite presentation is of finite presentation on the site. -/
theorem isFinitePresentationOnSite_of_isFinitePresentation' {X : AlgebraicSpaces B S hS}
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsFinitePresentation) :
    F.IsFinitePresentationOnSite :=
  have : SheafOfModules.IsFinitePresentation
      (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O) F := hF
  Stacks.Sheaves.FinitePresentation.isFinitePresentationOnSite_of_isFinitePresentation
    (X := smallEtaleRingedTopos B S hS X) F

/-- A module of finite presentation is of finite type on the site. -/
theorem isFiniteTypeOnSite_of_isFinitePresentation' {X : AlgebraicSpaces B S hS}
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsFinitePresentation) :
    SheafOfModules.IsFiniteTypeOnSite F :=
  have := isFinitePresentationOnSite_of_isFinitePresentation' F hF
  SheafOfModules.isFiniteTypeOnSite_of_isFinitePresentationOnSite F

/-- The inverse image of a module of finite presentation is of finite presentation. -/
theorem isFinitePresentation_modulePullback {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS Y.1 Y.2) (hF : F.IsFinitePresentation) :
    ((modulePullback B S hS f).obj F).IsFinitePresentation :=
  SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite' _
    (isFinitePresentationOnSite_modulePullback B S hS f F
      (isFinitePresentationOnSite_of_isFinitePresentation' F hF))

/-- A module `E` whose inverse image along `ψ⁻¹` is the inverse image of `N` along `φ` is the
inverse image of `N` along `ψ ≫ φ`. -/
def modulePullbackIsoOfIso {M P Q : AlgebraicSpaces B S hS} (ψ : M ≅ P) (φ : P ⟶ Q)
    {E : Modules.{u, u} B S hS M.1 M.2} {N : Modules.{u, u} B S hS Q.1 Q.2}
    (ι : (modulePullback B S hS φ).obj N ≅ (modulePullback B S hS ψ.inv).obj E) :
    E ≅ (modulePullback B S hS (ψ.hom ≫ φ)).obj N :=
  ((modulePullbackIdIso B S hS M).app E).symm ≪≫
    eqToIso (congrArg (fun f => (modulePullback B S hS f).obj E) ψ.hom_inv_id.symm) ≪≫
    ((modulePullbackCompIso B S hS ψ.hom ψ.inv).app E).symm ≪≫
    (modulePullback B S hS ψ.hom).mapIso ι.symm ≪≫ (modulePullbackCompIso B S hS ψ.hom φ).app N

/-- Inverse images along `f` and `g` compose to the inverse image along `h = f ≫ g`, which is
identified with `G` by `ι`. -/
private def modulePullbackPullbackIsoOfComp {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    {h : X ⟶ Z} (hfg : f ≫ g = h) {N : Modules.{u, u} B S hS Z.1 Z.2}
    {G : Modules.{u, u} B S hS X.1 X.2} (ι : (modulePullback B S hS h).obj N ≅ G) :
    (modulePullback B S hS f).obj ((modulePullback B S hS g).obj N) ≅ G :=
  (modulePullbackCompIso B S hS f g).app N ≪≫
    eqToIso (congrArg (fun φ => (modulePullback B S hS φ).obj N) hfg) ≪≫ ι

variable (hZ : B.Contains (⊤_ Scheme.{u})) {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)]
  [Nonempty J] (T : Jᵒᵖ ⥤ BigFppfOver B S hS)
  [∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (T.obj i))]
  {c : Cone T} (hc : IsLimit c) (hcS : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
  (X₀ : AlgebraicSpaces B S hS) {f₀ : X₀ ⟶ schemeSpace (Over.mk (𝟙 (B.obj hS)))}
  (hf₀ : IsFinitePresentation B S hS f₀.hom)

include hZ hc hcS hf₀ in
/-- **Stacks 07V7, 70.6.12 and 08K2 together, for the base changes `X_V = h_V ⨯ X₀` along a
directed inverse system `T` of affine schemes with limit `c.pt` in the site.** Let `X₀` be of
finite presentation over `S` and `G` a module of finite presentation on `X_{c.pt}`, flat over
`c.pt` and with support proper over `c.pt`. Then `G` is the inverse image of a module `N` on some
`X_{T j}` which is of finite presentation, flat over `T j` and with support proper over `T j`. -/
theorem exists_modulePullback_productSpaceConeMap_iso_of_isFlatOver
    (G : Modules.{u, u} B S hS (productSpace X₀ c.pt).1 (productSpace X₀ c.pt).2)
    (hG : G.IsFinitePresentation)
    (hflat : IsFlatOver B S hS (productSpace X₀ c.pt).2 (productSpaceFst X₀ c.pt).hom G)
    (hsupp : HasProperSupport B S hS (productSpace X₀ c.pt).2 (schemeSpace c.pt).2
      (productSpaceFst X₀ c.pt).hom (isFiniteType_of_isFinitePresentation B S hS
        (isFinitePresentation_productSpaceFst hf₀ c.pt)).1 ((SheafOfModules.toSheaf _).obj G)) :
    ∃ (j : J) (N : Modules.{u, u} B S hS (productSpace X₀ (T.obj (op j))).1
        (productSpace X₀ (T.obj (op j))).2),
      N.IsFinitePresentation ∧ N.IsQuasicoherentOnSite ∧ N.IsFinitePresentationOnSite ∧
      IsFlatOver B S hS (productSpace X₀ (T.obj (op j))).2
        (productSpaceFst X₀ (T.obj (op j))).hom N ∧
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
  have hc {j k : Jᵒᵖ} (e : j ⟶ k) : productSpaceMap X₀ (V := c.pt) (c.π.app j) ≫
      productSpaceMap X₀ (T.map e) = productSpaceMap X₀ (V := c.pt) (c.π.app k) := by
    rw [← productSpaceMap_comp, c.w]
  let ι₂ := modulePullbackPullbackIsoOfComp _ _ (hc (homOfLE h₁₂).op) ι
  -- Stacks 70.6.12: flatness over a later stage
  obtain ⟨j₃, e₃, hflat₃⟩ := eventually_isFlatOver_productSpaceFst X₀ T c hcS (op j₂) (hqc _)
    (hfp _).1 N₂ (isQuasicoherentOnSite_of_isFinitePresentation N₂ hN₂fp)
    (isFinitePresentationOnSite_of_isFinitePresentation' N₂ hN₂fp)
    (IsFlatOver.of_iso B S hS _ ι₂.symm hflat)
  let N₃ := (modulePullback B S hS (productSpaceMap X₀ (T.map e₃))).obj N₂
  have hN₃fp : N₃.IsFinitePresentation := isFinitePresentation_modulePullback _ N₂ hN₂fp
  exact ⟨j₃.unop, N₃, hN₃fp, isQuasicoherentOnSite_of_isFinitePresentation N₃ hN₃fp,
    isFinitePresentationOnSite_of_isFinitePresentation' N₃ hN₃fp, hflat₃,
    ⟨isClosed_supportOfSheaf_modulePullback B S hS _ N₂
      (isFiniteTypeOnSite_of_isFinitePresentation' N₂ hN₂fp),
      isProperOver_supportOfSheaf_modulePullback B S hS
        (isPullback_productSpaceMap_schemeSpaceMap X₀ (T.map e₃)) (hlft _) N₂
        (isQuasicoherentOnSite_of_isFinitePresentation N₂ hN₂fp)
        (isFiniteTypeOnSite_of_isFinitePresentation' N₂ hN₂fp) hP₂.2⟩,
    ⟨modulePullbackPullbackIsoOfComp _ _ (hc e₃) ι₂⟩⟩

end ProductDescent

/-! ### The Noetherian model of a module -/

section Model

variable (B : BigFppfSite.{u}) {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}
  {X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}

include B in
/-- **Noetherian approximation of a module of finite presentation, flat with proper support**
(the input of Stacks 0A1P). Let `X` be an algebraic space of finite presentation over `Spec A`
and `F` an `𝒪_X`-module of finite presentation, flat over `Spec A`, with support proper over
`Spec A`. Then there are a ring `A₀ ⊆ A` of finite type over `ℤ`, an affine Noetherian scheme
`Y₀` over `Spec A₀` with a morphism `y : Spec A ⟶ Y₀` over `Spec A₀`, an algebraic space `X₀` of
finite presentation over `Y₀` and an `𝒪_{X₀}`-module `F₀` of finite presentation, flat over `Y₀`
and with support proper over `Y₀`, such that on the site over `Spec A₀` the lower-shriek
extension `Λ X` of `X` is the base change `X₀ ×_{Y₀} Spec A` along a morphism `a : Λ X ⟶ X₀` and
the module of `Λ X` attached to `F` is `a^* F₀`.

Everything takes place over the one base `Spec A₀`, not over `Spec A`: with `X`, `Y = Spec A`,
`X₀`, `Y₀` all over the same base `S`, the statement would be false. For `R` non-Noetherian,
`S = Y = X = Spec R` and `F = 𝒪_X`, the morphisms `Y ⟶ Y₀ ⟶ S` would exhibit `R` as a retract of
the Noetherian ring of `Y₀`, so `R` would be Noetherian. -/
theorem exists_noetherianProductModel (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
    (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA))))
    (hfp : IsFinitePresentation B (Spec (.of A)) hA f)
    (F : Modules.{u, u} B (Spec (.of A)) hA X hX) (hF : F.IsFinitePresentation)
    (hflat : IsFlatOver B (Spec (.of A)) hA hX f F)
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
      _root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B _ hA₀).obj Y₀) ∧
      IsNoetherian B (Spec (.of A₀)) hA₀ (BigFppfSite.contains_terminal B) (schemeSpace Y₀).1 ∧
      F₀.IsFinitePresentation ∧ F₀.IsQuasicoherentOnSite ∧ F₀.IsFinitePresentationOnSite ∧
      IsFlatOver B (Spec (.of A₀)) hA₀ X₀.2 f₀.hom F₀ ∧
      HasProperSupport B (Spec (.of A₀)) hA₀ X₀.2 (schemeSpace Y₀).2 f₀.hom
        (isFiniteType_of_isFinitePresentation B _ hA₀ hf₀).1 ((SheafOfModules.toSheaf _).obj F₀) ∧
      IsPullback a (ObjectProperty.homMk (OverShriek.viewStructureMap g X) :
          relocalizeSpace B hA hA₀ g ⟨X, hX⟩ ⟶ schemeSpace (Over.mk g)) f₀ (schemeSpaceMap y) ∧
      Nonempty ((relocalizeModulesEquivalence B hA hA₀ g X hX).functor.obj F ≅
        (modulePullback B (Spec (.of A₀)) hA₀ a).obj F₀) := by
  classical
  obtain ⟨i, X₀, hX₀, f₀, hfp₀, -, -, hiso⟩ := exists_stageModel B hX f hfp
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
  obtain ⟨hGfp, hGflat, hGsupp⟩ := modulePullback_coefficient_conditions sq
    ((isLocallyOfFiniteType_relocalize_iff B _ hA _ h₀ g f).2 hlft)
    ((relocalizeModulesEquivalence B hA h₀ g X hX).functor.obj F)
    (isFinitePresentation_relocalizeModulesEquivalence_functor B hA h₀ g X hX F hF)
    (isFlatOver_relocalizeModulesEquivalence_functor B hA h₀ g hX Ys.2 f F hflat)
    ((hasProperSupport_relocalizeModulesEquivalence_functor_iff B hA h₀ g hX Ys.2 f hlft F).2 hsupp)
  -- Stacks 07V7, 70.6.12 and 08K2 along the system
  obtain ⟨j, N, hNfp, hNq, hNos, hNflat, hNsupp, ⟨ι⟩⟩ :=
    exists_modulePullback_productSpaceConeMap_iso_of_isFlatOver B.contains_terminal T
      (isLimit_specAdjoinTailCone B A hA i.unop) (isLimit_toScheme_specAdjoinTailCone B A hA i.unop)
      X₀s (f₀ := ObjectProperty.homMk f₀) hfp₀ _ hGfp hGflat hGsupp
  exact ⟨Algebra.adjoin ℤ (i.unop : Set A), inferInstance, inferInstance,
    finiteType_adjoinFinset_int A i.unop, h₀, g, rfl, _, cT.π.app (op j), _,
    productSpaceFst X₀s (T.obj (op j)), isFinitePresentation_productSpaceFst hfp₀ _, N,
    ψ.hom ≫ productSpaceConeMap X₀s T cT (op j), isAffine_specAdjoinFinsetDiagram_obj A (op j.val),
    isNoetherian_specAdjoinTail_obj B A i.unop (op j), isNoetherian_schemeSpace B.contains_terminal
      (T.obj (op j)) (hV := isNoetherian_specAdjoinTail_obj B A i.unop (op j)), hNfp, hNq, hNos,
    hNflat, hNsupp, isPullback_comp_productSpaceMap_of_iso X₀s ψ (cT.π.app (op j))
      (ObjectProperty.hom_ext _ hψ), ⟨modulePullbackIsoOfIso ψ _ ι⟩⟩

end Model

end AlgebraicGeometry.Space
