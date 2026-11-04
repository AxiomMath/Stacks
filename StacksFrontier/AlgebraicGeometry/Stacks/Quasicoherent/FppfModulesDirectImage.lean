module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftEssentialImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedQuasicoherentPullback
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfModulesEnoughInjectives
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageFppfWeakSerre
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StackModuleRule

/-!
# The direct image of modules on algebraic stacks at module universe `u`

Let `f : 𝒳 ⟶ 𝒴` be a `1`-morphism of algebraic stacks over `S` and `τ : SiteKind` a topology. The
direct image `f_*` on modules on the `τ`-sites, `Stacks.RelativeCech.moduleDirectImage` (and
`AlgebraicGeometry.Stack.moduleSheafPushforward` for the fppf sites), lives at the module universe
`u + 1`, while the inverse image `f^*` and the modules `Mod(𝒪_𝒳)` live at the module universe `u`
of the schemes. This file constructs the direct image at `u`: a functor right adjoint to the
inverse image at `u`, whose universe lift is the direct image at `u + 1` of the lift.

## Main definitions

* `AlgebraicGeometry.Stack.stackModuleULift`: the universe lift
  `Mod_u(𝒳_τ, 𝒪_𝒳) ⥤ Mod_{u+1}(𝒳_τ, 𝒪_𝒳)`.
* `AlgebraicGeometry.Stack.stackModuleDirectImage`: the direct image
  `f_* : Mod(𝒳_τ, 𝒪_𝒳) ⥤ Mod(𝒴_τ, 𝒪_𝒴)` at module universe `u`.
* `AlgebraicGeometry.Stack.stackModuleHigherDirectImage`: its right derived functors `Rⁱf_*`.
* `AlgebraicGeometry.Stack.stackModuleDirectImageData`: the direct image as an
  `AlgebraicGeometry.Stack.StackModuleDirectImage`, for every topology `τ`.
* `AlgebraicGeometry.Stack.fppfModulesULift`, `AlgebraicGeometry.Stack.fppfModulesPushforward`
  and `AlgebraicGeometry.Stack.fppfModulesHigherDirectImage`: the same three for `τ = fppf`, in
  the spelling of `AlgebraicGeometry.Stack.fppfModules`.

## Main results

* `AlgebraicGeometry.Stack.stackModuleInverseDirectImageAdjunction`: on the `τ`-sites at module
  universe `u`, `f^* ⊣ f_*` with `f^*` the inverse image `Stacks.RelativeCech.moduleInverseImage`.
* `AlgebraicGeometry.Stack.stackModuleDirectImageULiftIso` and
  `AlgebraicGeometry.Stack.stackModuleInverseImageULiftIso`: the lifts of `f_*` and `f^*` at `u`
  are `f_*` and `f^*` at `u + 1` of the lift.
* `AlgebraicGeometry.Stack.fppfModulesPullbackPushforwardAdjunction`: on the fppf sites at module
  universe `u`, `f^* ⊣ f_*`.
* `AlgebraicGeometry.Stack.fppfModulesPushforwardULiftIso`: the lift of `f_*` at `u` is `f_*` at
  `u + 1` of the lift.
* `AlgebraicGeometry.Stack.fppfModulesPullbackULiftIso`: the inverse image commutes with the
  lift.
* `AlgebraicGeometry.Stack.isWeakSerreClass_essImage_fppfModulesULift`: the modules at `u + 1`
  coming from `u` form a weak Serre class.

## References

* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w t

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The universe lift `Mod_u(𝒪_𝒳) ⥤ Mod_{u+1}(𝒪_𝒳)` of modules on the fppf site of an algebraic
stack: the module sections are lifted along `ULift`, the structure sheaf is unchanged. -/
abbrev fppfModulesULift (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    fppfModules B S hS 𝒳 ⥤ AlgebraicStacks.fppfModules B S hS 𝒳 :=
  Stacks.SheafOfModules.moduleULift.{u + 1, u} _

/-- The universe lift of modules on an algebraic stack is fully faithful. -/
def fppfModulesULiftFullyFaithful (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    (fppfModulesULift B S hS 𝒳).FullyFaithful :=
  Stacks.SheafOfModules.moduleULiftFullyFaithful _

/-- The universe lift of modules on an algebraic stack is full. -/
instance (𝒳 : AlgebraicStacks.{u, w} B S hS) : (fppfModulesULift B S hS 𝒳).Full :=
  (fppfModulesULiftFullyFaithful B S hS 𝒳).full

/-- The universe lift of modules on an algebraic stack is faithful. -/
instance (𝒳 : AlgebraicStacks.{u, w} B S hS) : (fppfModulesULift B S hS 𝒳).Faithful :=
  (fppfModulesULiftFullyFaithful B S hS 𝒳).faithful

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
section SiteKind

variable (τ : SiteKind)

/-- The universe lift `Mod_u(𝒳_τ, 𝒪_𝒳) ⥤ Mod_{u+1}(𝒳_τ, 𝒪_𝒳)` of modules on the `τ`-site of an
algebraic stack. -/
abbrev stackModuleULift (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    SheafOfModules.{u} (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids τ) ⥤
      SheafOfModules.{u + 1} (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids τ) :=
  Stacks.SheafOfModules.moduleULift.{u + 1, u} _

/-- The inverse image of modules on the `τ`-sites commutes with the universe lift. -/
def stackModuleInverseImageULiftIso :
    Stacks.RelativeCech.moduleInverseImage.{u, u + 1, u + 1, u, u, u} B S hS 𝒳.val.val.p
        𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
        (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
        τ ⋙ stackModuleULift B S hS τ 𝒳 ≅
      stackModuleULift B S hS τ 𝒴 ⋙
        Stacks.RelativeCech.moduleInverseImage.{u, u + 1, u + 1, u, u, u + 1} B S hS 𝒳.val.val.p
          𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
          (CatFiberedInGroupoids.homFunctor f.hom)
          (CatFiberedInGroupoids.homFunctor_comp_p f.hom) τ :=
  NatIso.ofComponents (fun _ ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (fun _ _ _ ↦ rfl))) (fun _ ↦ rfl)

/-- The direct image of modules on the `τ`-sites at module universe `u + 1`. -/
abbrev stackModuleDirectImageSucc :
    SheafOfModules.{u + 1} (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids τ) ⥤
      SheafOfModules.{u + 1} (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒴.val.val.p
        𝒴.val.isFiberedInGroupoids τ) :=
  Stacks.RelativeCech.moduleDirectImage.{u, u + 1, u + 1, u, u, u} B S hS 𝒳.val.val.p
    𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor_comp_p f.hom) τ

/-- The direct image at module universe `u + 1` of the universe lift of a module at `u` has
`u`-small sections. -/
theorem small_stackModuleDirectImageSucc_obj
    (M : SheafOfModules.{u} (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids τ)) (y : 𝒴.val.val.objᵒᵖ) :
    Small.{u} (((stackModuleDirectImageSucc B S hS f τ).obj
      ((stackModuleULift B S hS τ 𝒳).obj M)).val.obj y) := by
  have : ∀ X, Small.{u} (((stackModuleULift B S hS τ 𝒳).obj M).val.obj X) := fun X ↦
    small_ulift (M.val.obj X)
  have hF := (𝒴.val.isFiberedInGroupoids.isFibredOneMorphism
    (CatFiberedInGroupoids.homFunctor_comp_p f.hom))
  let : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  let : 𝒴.val.val.p.IsFibered := 𝒴.val.isFiberedInGroupoids.isFibered
  let := (hF.isContinuous_and_isCocontinuous_inheritedTopology
    (BigFppfOver.baseOverTopology B S hS τ)).1
  let := (hF.isContinuous_and_isCocontinuous_inheritedTopology
    (BigFppfOver.baseOverTopology B S hS τ)).2
  exact SheafOfModules.small_directImageOfEq_obj _ _ _ _ _ _ y

/-- The universe lift of modules on the `τ`-site of an algebraic stack is fully faithful. -/
def stackModuleULiftFullyFaithful (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    (stackModuleULift B S hS τ 𝒳).FullyFaithful :=
  Stacks.SheafOfModules.moduleULiftFullyFaithful _

/-- The universe lift of modules on the `τ`-site of an algebraic stack is full. -/
instance (𝒳 : AlgebraicStacks.{u, w} B S hS) : (stackModuleULift B S hS τ 𝒳).Full :=
  (stackModuleULiftFullyFaithful B S hS τ 𝒳).full

/-- The universe lift of modules on the `τ`-site of an algebraic stack is faithful. -/
instance (𝒳 : AlgebraicStacks.{u, w} B S hS) : (stackModuleULift B S hS τ 𝒳).Faithful :=
  (stackModuleULiftFullyFaithful B S hS τ 𝒳).faithful

/-- **The direct image of modules on the `τ`-sites along a `1`-morphism of algebraic stacks, at
module universe `u`**: the direct image at `u + 1` of the universe lift, which has `u`-small
sections, factored through the lift. -/
def stackModuleDirectImage :
    SheafOfModules.{u} (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids τ) ⥤
      SheafOfModules.{u} (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒴.val.val.p
        𝒴.val.isFiberedInGroupoids τ) :=
  Functor.essImage.liftFunctor
    (stackModuleULift B S hS τ 𝒳 ⋙ stackModuleDirectImageSucc B S hS f τ)
    (stackModuleULift B S hS τ 𝒴) (fun M ↦ (Stacks.SheafOfModules.moduleULift_essImage_iff _ _).2
      (small_stackModuleDirectImageSucc_obj B S hS f τ M))

/-- The universe lift of the direct image at `u` is the direct image at `u + 1` of the lift. -/
def stackModuleDirectImageULiftIso :
    stackModuleDirectImage B S hS f τ ⋙ stackModuleULift B S hS τ 𝒴 ≅
      stackModuleULift B S hS τ 𝒳 ⋙ stackModuleDirectImageSucc B S hS f τ :=
  Functor.essImage.liftFunctorCompIso _ _ _

/-- On the `τ`-sites at module universe `u`, the inverse image
`Stacks.RelativeCech.moduleInverseImage` is left adjoint to the direct image. -/
def stackModuleInverseDirectImageAdjunction :
    Stacks.RelativeCech.moduleInverseImage.{u, u + 1, u + 1, u, u, u} B S hS 𝒳.val.val.p
        𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
        (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
        τ ⊣ stackModuleDirectImage B S hS f τ :=
  (Stacks.RelativeCech.moduleInverseDirectImageAdjunction.{u, u + 1, u + 1, u, u, u} B S hS
    𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
    τ).restrictFullyFaithful
    (stackModuleULiftFullyFaithful B S hS τ 𝒴) (stackModuleULiftFullyFaithful B S hS τ 𝒳)
    (stackModuleInverseImageULiftIso B S hS f τ).symm
    (stackModuleDirectImageULiftIso B S hS f τ).symm

/-- The direct image of modules on the `τ`-sites at module universe `u` is additive. -/
instance stackModuleDirectImage_additive : (stackModuleDirectImage B S hS f τ).Additive :=
  have := Stacks.RelativeCech.moduleInverseImage_additive.{u, u + 1, u + 1, u, u, u} B S hS
    𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor_comp_p f.hom) τ
  (stackModuleInverseDirectImageAdjunction B S hS f τ).right_adjoint_additive

/-- **The higher direct images `Rⁱf_*` of modules on the `τ`-sites along a `1`-morphism of
algebraic stacks, at module universe `u`**: the right derived functors of
`AlgebraicGeometry.Stack.stackModuleDirectImage`. -/
def stackModuleHigherDirectImage (i : ℕ) :
    SheafOfModules.{u} (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids τ) ⥤
      SheafOfModules.{u} (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒴.val.val.p
        𝒴.val.isFiberedInGroupoids τ) :=
  letI := hasSheafify_associatedTopology_siteKind B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ
  letI := FibredSite.wEqualsLocallyBijective_associatedTopology B S hS 𝒳.val.val.p τ
  letI := hasSheafify_associatedTopology_siteKind B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids τ
  letI := FibredSite.wEqualsLocallyBijective_associatedTopology B S hS 𝒴.val.val.p τ
  letI := enoughInjectives_moduleRingSheaf B S hS 𝒳 τ
  (stackModuleDirectImage B S hS f τ).rightDerived i

/-- **The direct image of modules on the `τ`-sites of algebraic stacks**, as an
`AlgebraicGeometry.Stack.StackModuleDirectImage`: the direct image
`AlgebraicGeometry.Stack.stackModuleDirectImage` at the universe of the schemes, right adjoint to
the inverse image, with the enough injectives of every `Mod(𝒳_τ, 𝒪_𝒳)`. -/
noncomputable def stackModuleDirectImageData : StackModuleDirectImage.{u, w} B S hS τ where
  pushforward f := stackModuleDirectImage B S hS f τ
  adjunction f := stackModuleInverseDirectImageAdjunction B S hS f τ
  enoughInjectives 𝒳 := enoughInjectives_moduleRingSheaf B S hS 𝒳 τ

/-- The higher direct images of `AlgebraicGeometry.Stack.stackModuleDirectImageData` are
`AlgebraicGeometry.Stack.stackModuleHigherDirectImage`. -/
theorem stackModuleDirectImageData_higherDirectImage (i : ℕ) :
    (stackModuleDirectImageData B S hS τ).higherDirectImage f i =
      stackModuleHigherDirectImage B S hS f τ i := rfl

end SiteKind


/-- The inverse image of modules on the fppf sites commutes with the universe lift. -/
def fppfModulesPullbackULiftIso :
    fppfModulesPullback B S hS f ⋙ fppfModulesULift B S hS 𝒳 ≅
      fppfModulesULift B S hS 𝒴 ⋙ AlgebraicStacks.fppfModulePullback B S hS f :=
  NatIso.ofComponents (fun _ ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (fun _ _ _ ↦ rfl))) (fun _ ↦ rfl)

/-- The direct image `AlgebraicGeometry.Stack.moduleSheafPushforward` of modules on the fppf
sites along a `1`-morphism of algebraic stacks, at module universe `u + 1`. -/
abbrev fppfModulesPushforwardSucc :
    AlgebraicStacks.fppfModules B S hS 𝒳 ⥤ AlgebraicStacks.fppfModules B S hS 𝒴 :=
  moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
    𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor f.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p f.hom) B.topology le_rfl

/-- The direct image at module universe `u + 1` of the universe lift of a module at `u` on the
fppf sites has `u`-small sections. -/
theorem small_fppfModulesPushforwardSucc_obj (M : fppfModules B S hS 𝒳)
    (y : 𝒴.val.val.objᵒᵖ) :
    Small.{u} (((fppfModulesPushforwardSucc B S hS f).obj
      ((fppfModulesULift B S hS 𝒳).obj M)).val.obj y) := by
  let F := CatFiberedInGroupoids.homFunctor f.hom
  let W := moduleFunctoriality.{u, u + 1, u, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
    𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids F
    (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
  let N := (fppfModulesULift B S hS 𝒳).obj M
  let D₀ := StructuredArrow.proj y F.op ⋙ M.val.presheaf
  have : HasLimit D₀ := hasLimitsOfShape_of_essentiallySmall _ _ |>.has_limit D₀
  let e : ((PresheafOfModules.toPresheaf _).obj (W.pushforward.obj N.val)).obj y ≅
      AddCommGrpCat.uliftFunctor.{u + 1}.obj (limit D₀) :=
    (W.pushforward_iso.app N.val).app y ≪≫ F.op.ranObjObjIsoLimit _ y ≪≫
      (preservesLimitIso AddCommGrpCat.uliftFunctor.{u + 1} D₀).symm
  have : Small.{u} (AddCommGrpCat.uliftFunctor.{u + 1}.obj (limit D₀)) :=
    small_ulift ((limit D₀ : AddCommGrpCat.{u}) : Type u)
  exact small_of_injective (f := e.addCommGroupIsoToAddEquiv)
    e.addCommGroupIsoToAddEquiv.injective

/-- **The direct image of modules along a `1`-morphism of algebraic stacks at module universe
`u`**, on the fppf sites: `AlgebraicGeometry.Stack.stackModuleDirectImage` at `τ = fppf`. -/
abbrev fppfModulesPushforward : fppfModules B S hS 𝒳 ⥤ fppfModules B S hS 𝒴 :=
  stackModuleDirectImage B S hS f .fppf

/-- The inverse image `Stacks.RelativeCech.moduleInverseImage` on the fppf sites, at any module
universe, is `AlgebraicGeometry.Stack.modulePullback`. -/
theorem moduleInverseImage_fppf_eq_modulePullback :
    Stacks.RelativeCech.moduleInverseImage.{u, u + 1, u + 1, u, u, t} B S hS 𝒳.val.val.p
        𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
        (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
        .fppf =
      modulePullback.{u, u + 1, u, t, u + 1, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
        𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
        (CatFiberedInGroupoids.homFunctor f.hom)
        (CatFiberedInGroupoids.homFunctor_comp_p f.hom) B.topology le_rfl := by
  unfold Stacks.RelativeCech.moduleInverseImage modulePullback
  congr 1
  ext1
  simp only [ringStructureSheafCoreHom]
  exact eqToHom_map (sheafToPresheaf _ _) _

/-- The inverse image `Stacks.RelativeCech.moduleInverseImage` on the fppf sites is
`AlgebraicGeometry.Stack.modulePullback`, as a natural isomorphism. -/
def moduleInverseImageFppfIsoModulePullback :
    Stacks.RelativeCech.moduleInverseImage.{u, u + 1, u + 1, u, u, t} B S hS 𝒳.val.val.p
        𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
        (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
        .fppf ≅
      modulePullback.{u, u + 1, u, t, u + 1, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
        𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
        (CatFiberedInGroupoids.homFunctor f.hom)
        (CatFiberedInGroupoids.homFunctor_comp_p f.hom) B.topology le_rfl :=
  eqToIso (moduleInverseImage_fppf_eq_modulePullback.{u, w, t} B S hS f)

/-- On the fppf sites at module universe `u`, the inverse image is left adjoint to the direct
image. -/
def fppfModulesPullbackPushforwardAdjunction :
    fppfModulesPullback B S hS f ⊣ fppfModulesPushforward B S hS f :=
  (stackModuleInverseDirectImageAdjunction B S hS f .fppf).ofNatIsoLeft
    (moduleInverseImageFppfIsoModulePullback.{u, w, u} B S hS f)

/-- The direct image at module universe `u + 1` of
`Stacks.RelativeCech.moduleDirectImage` on the fppf sites is the one of
`AlgebraicGeometry.Stack.moduleSheafPushforward`. -/
def stackModuleDirectImageSuccFppfIso :
    stackModuleDirectImageSucc B S hS f .fppf ≅ fppfModulesPushforwardSucc B S hS f :=
  ((Stacks.RelativeCech.moduleInverseDirectImageAdjunction.{u, u + 1, u + 1, u, u, u} B S hS
    𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
    .fppf).ofNatIsoLeft
      (moduleInverseImageFppfIsoModulePullback.{u, w, u + 1} B S hS f)).rightAdjointUniq
    (moduleSheafAdjunction.{u, u + 1, u, u, u + 1, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
      𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor f.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p f.hom) B.topology le_rfl)

/-- The universe lift of the direct image at `u` is the direct image at `u + 1` of the lift. -/
def fppfModulesPushforwardULiftIso :
    fppfModulesPushforward B S hS f ⋙ fppfModulesULift B S hS 𝒴 ≅
      fppfModulesULift B S hS 𝒳 ⋙ fppfModulesPushforwardSucc B S hS f :=
  stackModuleDirectImageULiftIso B S hS f .fppf ≪≫
    Functor.isoWhiskerLeft _ (stackModuleDirectImageSuccFppfIso B S hS f)

/-- The direct image of modules on the fppf sites at module universe `u` is additive. -/
instance fppfModulesPushforward_additive : (fppfModulesPushforward B S hS f).Additive :=
  (fppfModulesPullbackPushforwardAdjunction B S hS f).right_adjoint_additive

/-- **The higher direct images `Rⁱf_*` of modules along a `1`-morphism of algebraic stacks at
module universe `u`**, on the fppf sites: `AlgebraicGeometry.Stack.stackModuleHigherDirectImage`
at `τ = fppf`. -/
abbrev fppfModulesHigherDirectImage (i : ℕ) :
    SheafOfModules.{u} (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids .fppf) ⥤
      SheafOfModules.{u} (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒴.val.val.p
        𝒴.val.isFiberedInGroupoids .fppf) :=
  stackModuleHigherDirectImage B S hS f .fppf i

attribute [local instance] AlgebraicStacks.hasSheafify_fppfAssociatedTopology
  AlgebraicStacks.wEqualsLocallyBijective_fppfAssociatedTopology
  FlatFppf.hasSheafify_fppf_addCommGrpCat FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat in
/-- **The modules at universe `u + 1` on an algebraic stack which come from universe `u` form a
weak Serre class**: the essential image of `AlgebraicGeometry.Stack.fppfModulesULift` is closed
under kernels, cokernels and extensions. -/
theorem isWeakSerreClass_essImage_fppfModulesULift (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    (fppfModulesULift B S hS 𝒳).essImage.IsWeakSerreClass :=
  Stacks.SheafOfModules.isWeakSerreClass_essImage_moduleULift _


end AlgebraicGeometry.Stack
