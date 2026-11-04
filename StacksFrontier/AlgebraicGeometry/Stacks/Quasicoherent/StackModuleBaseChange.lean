module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfModulesBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StackModuleRuleAffineTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Equalizers

/-!
# Stacks 075H for the direct images of modules on the sites of algebraic stacks

For a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks, a 1-morphism `g : V ⟶ 𝒴` out of the algebraic
stack of a scheme and the canonical 2-fibre product, the higher direct images of modules on the
`τ`-sites at module universe `u` satisfy `g⁻¹ Rⁱf_* ℱ ≅ Rⁱf'_* (g')⁻¹ ℱ`, for every direct image
in the sense of `AlgebraicGeometry.Stack.StackModuleDirectImage`.

Every such direct image is right adjoint to the inverse image, hence isomorphic to the canonical
direct image along the cocontinuous functor underlying the 1-morphism
(`StackModuleDirectImage.pushforwardIsoModuleDirectImage`), for which Stacks 075H is
`AlgebraicGeometry.Stack.moduleHigherDirectImageBaseChangeIso`. Its injectivity input holds here:
`g` is faithful because a scheme is fibred in sets over the base, hence so is `g'`
(`CategoryTheory.TwoFibreProductOver.faithful_fst_of_faithful`), and the 2-fibre product is an
algebraic stack, so it has equalizers (Stacks 06WY (3)) and is essentially small.

## Main results

* `AlgebraicGeometry.Stack.StackModuleDirectImage.higherDirectImageBaseChangeIso`.
* `AlgebraicGeometry.Stack.StackModuleDirectImage.hasSmoothBaseChange` and
  `AlgebraicGeometry.Stack.hasSmoothBaseChange_stackModuleDirectImageData`: the predicate
  `AlgebraicGeometry.Stack.StackModuleRule.HasSmoothBaseChange` consumed by Stacks 076Z, 0770.

## References

* [Stacks Project, Tag 075H](https://stacks.math.columbia.edu/tag/075H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u t

namespace CategoryTheory.TwoFibreProductOver

variable {𝒞 : Type*} [Category 𝒞] {𝒳 𝒴 𝒮 : Type*} [Category 𝒳] [Category 𝒴] [Category 𝒮]
  {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒮 : 𝒮 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒮} {G : 𝒴 ⥤ 𝒮}

/-- The first projection of a 2-fibre product is faithful as soon as the second leg `G` is:
a morphism of the 2-fibre product is determined by its first component, the comparison
isomorphism then pinning down the image under `G` of the second. -/
theorem faithful_fst_of_faithful [G.Faithful] : (fst p𝒳 p𝒴 p𝒮 F G).Faithful where
  map_injective {P Q} u v h := by
    change u.a = v.a at h
    refine Hom.ext' h (G.map_injective ((cancel_epi P.iso.hom).1 ?_))
    rw [← u.w, ← v.w, h]

end CategoryTheory.TwoFibreProductOver

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A 1-morphism out of the algebraic stack of a scheme is faithful: its source is fibred in sets,
the structure functor `Over.forget V` being faithful. -/
theorem faithful_homFunctor_schemeStack {V : BigFppfOver B S hS} {𝒴 : AlgebraicStacks.{u, t} B S hS}
    (g : schemeStack.{u, t} B S hS V ⟶ 𝒴) : (CatFiberedInGroupoids.homFunctor g.hom).Faithful :=
  have : (CatFiberedInGroupoids.homFunctor g.hom ⋙ 𝒴.val.val.p).Faithful := by
    rw [CatFiberedInGroupoids.homFunctor_comp_p g.hom]
    exact inferInstanceAs (Over.forget V).Faithful
  Functor.Faithful.of_comp _ 𝒴.val.val.p

variable {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴) (τ : SiteKind)

/-- The inverse image of modules on the `τ`-sites is the inverse image of Stacks 06WE at the
topology `B.baseTopology τ`. -/
theorem stackModuleInverseImage_eq_modulePullback :
    stackModuleInverseImage B S hS τ f =
      modulePullback.{u, u + 1, u, u, u + 1, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
        𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
        (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
        (B.baseTopology τ) (B.baseTopology_le_topology τ) := by
  unfold stackModuleInverseImage Stacks.RelativeCech.moduleInverseImage
  rw [modulePullback_eq_pushforward_ringStructureSheafCoreHom]

/-- Any direct image of modules on the `τ`-sites in the sense of
`AlgebraicGeometry.Stack.StackModuleDirectImage` is the canonical direct image: both are right
adjoint to the inverse image. -/
def StackModuleDirectImage.pushforwardIsoModuleDirectImage
    (D : StackModuleDirectImage.{u, t} B S hS τ) :
    D.pushforward f ≅
      moduleDirectImage.{u, u + 1, u, u + 1, u, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
        𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
        (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
        (B.baseTopology τ) (B.baseTopology_le_topology τ) :=
  ((D.adjunction f).ofNatIsoLeft
    (eqToIso (stackModuleInverseImage_eq_modulePullback B S hS f τ))).rightAdjointUniq
    (moduleDirectImageAdjunction.{u, u + 1, u, u + 1, u, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
      𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
      (B.baseTopology τ) (B.baseTopology_le_topology τ))

/-- **Stacks 075H for sheaves of modules on the `τ`-sites of algebraic stacks**, along a
1-morphism `g` out of the algebraic stack of a scheme, for every direct image `D`:
`g⁻¹ Rⁱf_* ℱ ≅ Rⁱf'_* (g')⁻¹ ℱ` for the canonical 2-fibre product. -/
def StackModuleDirectImage.higherDirectImageBaseChangeIso
    (D : StackModuleDirectImage.{u, t} B S hS τ) {V : BigFppfOver B S hS}
    (g : schemeStack.{u, t} B S hS V ⟶ 𝒴) (i : ℕ) (F : StackModules B S hS τ 𝒳) :
    (stackModuleInverseImage B S hS τ g).obj ((D.higherDirectImage f i).obj F) ≅
      (D.higherDirectImage (twoFibreProductSquareAlgebraicStacks B S hS f g).snd i).obj
        ((stackModuleInverseImage B S hS τ
          (twoFibreProductSquareAlgebraicStacks B S hS f g).fst).obj F) := by
  let P := twoFibreProductSquareAlgebraicStacks B S hS f g
  have hsndc := isCocontinuous_homFunctor B S hS P.snd (B.baseTopology τ)
  have hRf : ∀ G : 𝒳.val.val.objᵒᵖ ⥤ RingCat.{u},
      (CatFiberedInGroupoids.homFunctor f.hom).op.HasPointwiseRightKanExtension G :=
    hasPointwiseRightKanExtension_homFunctor_of_hasLimitsOfSize B S hS f RingCat.{u}
  have hAf : ∀ G : 𝒳.val.val.objᵒᵖ ⥤ AddCommGrpCat.{u},
      (CatFiberedInGroupoids.homFunctor f.hom).op.HasPointwiseRightKanExtension G :=
    hasPointwiseRightKanExtension_homFunctor_of_hasLimitsOfSize B S hS f AddCommGrpCat.{u}
  have hRs : ∀ G : (TwoFibreProductOver 𝒳.val.val.p (schemeStack.{u, t} B S hS V).val.val.p
      𝒴.val.val.p (CatFiberedInGroupoids.homFunctor f.hom)
      (CatFiberedInGroupoids.homFunctor g.hom))ᵒᵖ ⥤ RingCat.{u},
      (TwoFibreProductOver.snd 𝒳.val.val.p (schemeStack.{u, t} B S hS V).val.val.p
      𝒴.val.val.p (CatFiberedInGroupoids.homFunctor f.hom)
      (CatFiberedInGroupoids.homFunctor g.hom)).op.HasPointwiseRightKanExtension G :=
    hasPointwiseRightKanExtension_homFunctor_of_hasLimitsOfSize B S hS P.snd RingCat.{u}
  have hAs : ∀ G : (TwoFibreProductOver 𝒳.val.val.p (schemeStack.{u, t} B S hS V).val.val.p
      𝒴.val.val.p (CatFiberedInGroupoids.homFunctor f.hom)
      (CatFiberedInGroupoids.homFunctor g.hom))ᵒᵖ ⥤ AddCommGrpCat.{u},
      (TwoFibreProductOver.snd 𝒳.val.val.p (schemeStack.{u, t} B S hS V).val.val.p
      𝒴.val.val.p (CatFiberedInGroupoids.homFunctor f.hom)
      (CatFiberedInGroupoids.homFunctor g.hom)).op.HasPointwiseRightKanExtension G :=
    hasPointwiseRightKanExtension_homFunctor_of_hasLimitsOfSize B S hS P.snd AddCommGrpCat.{u}
  have := D.additive_pushforward P.snd
  have := D.additive_pushforward f
  have hsndc' : (TwoFibreProductOver.snd 𝒳.val.val.p (schemeStack.{u, t} B S hS V).val.val.p
      𝒴.val.val.p (CatFiberedInGroupoids.homFunctor f.hom)
      (CatFiberedInGroupoids.homFunctor g.hom)).IsCocontinuous
      (associatedTopology B S hS P.pt.val.val.p (B.baseTopology τ))
      (associatedTopology B S hS (schemeStack.{u, t} B S hS V).val.val.p (B.baseTopology τ)) :=
    hsndc
  have sh : ∀ 𝒵 : AlgebraicStacks.{u, t} B S hS,
      HasSheafify (associatedTopology B S hS 𝒵.val.val.p (B.baseTopology τ)) AddCommGrpCat.{u} :=
    fun 𝒵 => hasSheafify_stackModules B S hS τ 𝒵
  have wl : ∀ 𝒵 : AlgebraicStacks.{u, t} B S hS,
      (associatedTopology B S hS 𝒵.val.val.p (B.baseTopology τ)).WEqualsLocallyBijective
        AddCommGrpCat.{u} :=
    fun 𝒵 => wEqualsLocallyBijective_stackModules B S hS τ 𝒵
  have := sh 𝒳
  have := sh 𝒴
  have := sh (schemeStack.{u, t} B S hS V)
  have := sh P.pt
  have := wl 𝒳
  have := wl 𝒴
  have := wl (schemeStack.{u, t} B S hS V)
  have := wl P.pt
  have := D.enoughInjectives 𝒳
  have := D.enoughInjectives P.pt
  have : HasInjectiveResolutions (SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (B.baseTopology τ) (B.baseTopology_le_topology τ))) :=
    inferInstance
  have hip : HasInjectiveResolutions (SheafOfModules.{u} (ringStructureSheafCore B S hS
      P.pt.val.val.p P.pt.val.isFiberedInGroupoids (B.baseTopology τ)
      (B.baseTopology_le_topology τ))) :=
    inferInstance
  have : HasSheafify (associatedTopology B S hS (TwoFibreProductOver.structureFunctor 𝒳.val.val.p
        (schemeStack.{u, t} B S hS V).val.val.p 𝒴.val.val.p
        (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor g.hom))
      (B.baseTopology τ)) AddCommGrpCat.{u} := sh P.pt
  have : (associatedTopology B S hS (TwoFibreProductOver.structureFunctor 𝒳.val.val.p
        (schemeStack.{u, t} B S hS V).val.val.p 𝒴.val.val.p
        (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor g.hom))
      (B.baseTopology τ)).WEqualsLocallyBijective AddCommGrpCat.{u} := wl P.pt
  have : HasInjectiveResolutions (SheafOfModules.{u} (ringStructureSheafCore B S hS
      (TwoFibreProductOver.structureFunctor 𝒳.val.val.p
        (schemeStack.{u, t} B S hS V).val.val.p 𝒴.val.val.p
        (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor g.hom))
        P.pt.val.isFiberedInGroupoids (B.baseTopology τ)
      (B.baseTopology_le_topology τ))) := hip
  have : (TwoFibreProductOver.snd 𝒳.val.val.p (schemeStack.{u, t} B S hS V).val.val.p
      𝒴.val.val.p (CatFiberedInGroupoids.homFunctor f.hom)
      (CatFiberedInGroupoids.homFunctor g.hom)).IsCocontinuous
      (associatedTopology B S hS (TwoFibreProductOver.structureFunctor 𝒳.val.val.p
        (schemeStack.{u, t} B S hS V).val.val.p 𝒴.val.val.p
        (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor g.hom))
        (B.baseTopology τ))
      (associatedTopology B S hS (schemeStack.{u, t} B S hS V).val.val.p (B.baseTopology τ)) :=
    hsndc
  have hfaith : (TwoFibreProductOver.fst 𝒳.val.val.p (schemeStack.{u, t} B S hS V).val.val.p
      𝒴.val.val.p (CatFiberedInGroupoids.homFunctor f.hom)
      (CatFiberedInGroupoids.homFunctor g.hom)).Faithful :=
    have := faithful_homFunctor_schemeStack B S hS g
    TwoFibreProductOver.faithful_fst_of_faithful
  have hfaith' : (CatFiberedInGroupoids.homFunctor P.fst.hom).Faithful := hfaith
  have hEq : HasEqualizers P.pt.val.val.obj := inferInstance
  have hES : EssentiallySmall.{u} P.pt.val.val.obj := inferInstance
  have hinj := preservesInjectiveObjects_modulePullback.{u, u + 1, u, u + 1, u} B S hS
    P.pt.val.val.p 𝒳.val.val.p P.pt.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor P.fst.hom) (CatFiberedInGroupoids.homFunctor_comp_p P.fst.hom)
    (B.baseTopology τ) (B.baseTopology_le_topology τ)
  have : (modulePullback.{u, u + 1, u, u, u + 1, u} B S hS
      (TwoFibreProductOver.structureFunctor 𝒳.val.val.p
        (schemeStack.{u, t} B S hS V).val.val.p 𝒴.val.val.p
        (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor g.hom))
      𝒳.val.val.p P.pt.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
      (TwoFibreProductOver.fst 𝒳.val.val.p (schemeStack.{u, t} B S hS V).val.val.p
        𝒴.val.val.p (CatFiberedInGroupoids.homFunctor f.hom)
        (CatFiberedInGroupoids.homFunctor g.hom))
      (CatFiberedInGroupoids.homFunctor_comp_p P.fst.hom)
      (B.baseTopology τ) (B.baseTopology_le_topology τ)).PreservesInjectiveObjects := hinj
  have eF := StackModuleDirectImage.pushforwardIsoModuleDirectImage B S hS f τ D
  have eS := StackModuleDirectImage.pushforwardIsoModuleDirectImage B S hS P.snd τ D
  have bc := moduleHigherDirectImageBaseChangeIso.{u, u, u + 1, u, u + 1, u, u + 1, u} B S hS
    𝒳.val.val.p
    (schemeStack.{u, t} B S hS V).val.val.p 𝒴.val.val.p (CatFiberedInGroupoids.homFunctor f.hom)
    (CatFiberedInGroupoids.homFunctor g.hom) (B.baseTopology τ) (B.baseTopology_le_topology τ)
    𝒳.val.isFiberedInGroupoids (schemeStack.{u, t} B S hS V).val.isFiberedInGroupoids
    𝒴.val.isFiberedInGroupoids (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p g.hom)
    (TwoFibreProductOver.structureFunctor 𝒳.val.val.p
        (schemeStack.{u, t} B S hS V).val.val.p 𝒴.val.val.p
        (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor g.hom))
        P.pt.val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor_comp_p P.fst.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p P.snd.hom) i
  rw [stackModuleInverseImage_eq_modulePullback, stackModuleInverseImage_eq_modulePullback]
  unfold StackModuleDirectImage.higherDirectImage
  exact (modulePullback B S hS _ _ _ _ _ _ _ _).mapIso
      ((Functor.rightDerivedIsoOfNatIso eF i).app F) ≪≫ bc.app F ≪≫
    (Functor.rightDerivedIsoOfNatIso eS i).symm.app _

/-- **Stacks 075H along 1-morphisms out of schemes, for every direct image**: every direct image
`D` of modules on the `τ`-sites satisfies the base change identification of
`AlgebraicGeometry.Stack.StackModuleRule.HasSmoothBaseChange`. Smoothness is not used: the
identification holds along every 1-morphism out of the algebraic stack of a scheme. -/
theorem StackModuleDirectImage.hasSmoothBaseChange (D : StackModuleDirectImage.{u, t} B S hS τ) :
    StackModuleRule.HasSmoothBaseChange D :=
  fun f g _ i F => ⟨StackModuleDirectImage.higherDirectImageBaseChangeIso B S hS f τ D g i F⟩

/-- **Stacks 075H for the direct image `stackModuleDirectImageData`** of modules on the `τ`-sites
at module universe `u`, along smooth 1-morphisms out of schemes. -/
theorem hasSmoothBaseChange_stackModuleDirectImageData :
    StackModuleRule.HasSmoothBaseChange (stackModuleDirectImageData.{u, t} B S hS τ) :=
  StackModuleDirectImage.hasSmoothBaseChange B S hS τ _

end AlgebraicGeometry.Stack
