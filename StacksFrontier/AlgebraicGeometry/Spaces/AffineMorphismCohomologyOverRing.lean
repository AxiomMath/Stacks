module

public import StacksFrontier.AlgebraicGeometry.Quot.TwistedEulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishingUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforwardExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleCohomologyUniverseLift
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.GlobalSections
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology along an affine morphism of algebraic spaces, as modules over a ring

Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, and let `𝓕` be a quasi-coherent `𝒪_X`-module. Stacks 0D2U asserts that

`Hⁱ(X, 𝓕) = Hⁱ(Y, f_*𝓕)`

for every `i`. The library has this as abelian groups,
`AlgebraicGeometry.Space.cohomologyIsoOfIsAffineHom`, in the universe of the structure sheaf. This
file proves it as modules: given a ring `A` and ring maps `A ⟶ Γ(Y, 𝒪_Y)` and
`A ⟶ Γ(X, 𝒪_X)` compatible with `f`, the two sides are isomorphic as `A`-modules; and it proves
it in the universe of the Euler characteristic of Stacks 0DN1, for the universe lift of `𝓕`.
For `A` the field of definition of a proper algebraic space this is what makes the Euler
characteristics of `𝓕` on `X` and of `f_*𝓕` on `Y` agree.

The comparison of global sections is restriction along the base change of étale charts
`V ↦ V ×_Y X`, a morphism of small étale sites (Stacks 03G2 (4)), along which global sections of
sheaves are unchanged (`CategoryTheory.Functor.bijective_sectionsPrecomp_of_isMorphismOfSites`);
in that form its compatibility with the `A`-module structures is a sectionwise identity. The
higher degrees are the Leray collapse
(`Stacks.RightDerivedComp.objIsoOfAcyclicImage`) with the vanishing of the higher direct images
of Stacks 073H and the acyclicity of the direct image of an injective module of Stacks 072Z as
inputs, both proved unconditionally.

## Main definitions

* `AlgebraicGeometry.Space.GlobalSectionRingHomsCompatible`: the compatibility of ring maps
  `A ⟶ Γ(Y, 𝒪_Y)` and `A ⟶ Γ(X, 𝒪_X)` with `f`.
* `AlgebraicGeometry.Space.cohomologyOverRingIsoOfIsAffineHom`: Stacks 0D2U as an isomorphism of
  `A`-modules, in the universe of the structure sheaf.
* `AlgebraicGeometry.Space.cohomologyUliftOverRingIsoOfIsAffineHom`: the same in the universe of
  the Euler characteristic.
* `AlgebraicGeometry.Space.cohomologyUliftIsoOfIsAffineHom`: **Stacks 0D2U**, in the universe of
  the Euler characteristic.

## Main results

* `AlgebraicGeometry.Space.globalSectionRingHomsCompatible_globalSectionsRingHom`: the ring maps
  `Γ(V, 𝒪_V) ⟶ Γ(-, 𝒪)` induced by morphisms `φ : Y ⟶ V` and `f ≫ φ : X ⟶ V` to a scheme are
  compatible with `f`.
* `AlgebraicGeometry.Space.eulerCharacteristicAlong_modulePushforward_of_isAffineHom`: the Euler
  characteristic over a field is unchanged by the direct image along an affine morphism.

## Implementation notes

The cohomology in the universe of the structure sheaf is related to that in the universe of the
Euler characteristic by `Stacks.Cohomology.SiteModules.rightDerivedGlobalSectionsUliftIso`: the
universe lift of sheaves of modules preserves injective objects.

## References

* [Stacks Project, Tag 0D2U](https://stacks.math.columbia.edu/tag/0D2U)
* [Stacks Project, Tag 073H](https://stacks.math.columbia.edu/tag/073H)
* [Stacks Project, Tag 072Z](https://stacks.math.columbia.edu/tag/072Z)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] AlgebraicGeometry.Space.additive_smallBaseChangeModulePushforward
  AlgebraicGeometry.Space.additive_smallBaseChangeModulePushforward_modules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- Ring maps `A ⟶ Γ(Y, 𝒪_Y)` and `A ⟶ Γ(X, 𝒪_X)` are **compatible with** a representable
morphism `f : X ⟶ Y` when, on every étale chart `V` of `Y`, the second evaluated at the base
change `V ×_Y X` is the pullback of the first evaluated at `V`. -/
def GlobalSectionRingHomsCompatible (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
    {A : Type*} [CommRing A]
    (ψY : A →+* GlobalSectionRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)))
    (ψX : A →+* GlobalSectionRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) :
    Prop :=
  ∀ (a : A) (V : SmallEtale B S hS Y.1),
    (ψX a).1 (op ((smallBaseChange B S hS f hf).obj V)) =
      (smallBaseChangeSharp B S hS f hf).hom.app (op V) ((ψY a).1 (op V))

/-- The chart morphism to a scheme `V` that `f ≫ φ` induces on the base change `W ×_Y X` of an
étale chart `W` of `Y` is the cartesian projection `W ×_Y X ⟶ W` followed by the chart morphism
that `φ` induces on `W`. -/
theorem chartToScheme_smallBaseChange_obj (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
    {V : BigFppfOver B S hS} (φ : Y.1 ⟶ yoneda.obj V) (W : SmallEtale B S hS Y.1) :
    chartToScheme B S hS X.1 (f.hom ≫ φ) ((smallBaseChange B S hS f hf).obj W) =
      hf.snd W.1.hom ≫ chartToScheme B S hS Y.1 φ W := by
  apply Yoneda.fullyFaithful.map_injective
  rw [chartToScheme, Functor.FullyFaithful.map_preimage]
  refine Eq.trans ?_ (yoneda.map_comp (hf.snd W.1.hom) (chartToScheme B S hS Y.1 φ W)).symm
  rw [chartToScheme, Functor.FullyFaithful.map_preimage, ← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ φ) (hf.w W.1.hom)

/-- **The ring maps on global functions induced by morphisms `φ : Y ⟶ V` and `f ≫ φ : X ⟶ V` to
a scheme are compatible with `f`**, after precomposition with any ring map into `Γ(V, 𝒪_V)`. -/
theorem globalSectionRingHomsCompatible_globalSectionsRingHom (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) {V : BigFppfOver B S hS}
    (φ : Y.1 ⟶ yoneda.obj V) {A : Type*} [CommRing A]
    (α : A →+* Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj V))) :
    GlobalSectionRingHomsCompatible B S hS f hf
      ((globalSectionsRingHom B S hS Y.1 Y.2 φ).comp α)
      ((globalSectionsRingHom B S hS X.1 X.2 (f.hom ≫ φ)).comp α) := by
  intro a W
  show (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (chartToScheme B S hS X.1 (f.hom ≫ φ)
      ((smallBaseChange B S hS f hf).obj W))).op).hom (α a) =
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (hf.snd W.1.hom)).op).hom
      ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        (chartToScheme B S hS Y.1 φ W)).op).hom (α a))
  rw [chartToScheme_smallBaseChange_obj]
  exact congrArg (fun k => k.hom (α a))
    ((congrArg Scheme.Γ.map (congrArg Quiver.Hom.op ((BigFppfOver.toScheme B S hS).map_comp
      (hf.snd W.1.hom) (chartToScheme B S hS Y.1 φ W)))).trans (Scheme.Γ.map_comp _ _))

variable (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom) {A : Type u} [CommRing A]
    (ψY : A →+* GlobalSectionRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)))
    (ψX : A →+* GlobalSectionRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)))

/-- Restriction of global sections along the base change of étale charts,
`Γ(X, 𝓕) ⟶ Γ(Y, f_*𝓕)`, as a map of `A`-modules. -/
def globalSectionsSmallBaseChangeLinearMap (h : GlobalSectionRingHomsCompatible B S hS f hf ψY ψX)
    (G : Modules.{u, u} B S hS X.1 X.2) :
    ((globalSectionsFunctor.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) ⋙
      ModuleCat.restrictScalars ψX).obj G) →ₗ[A]
    ((smallBaseChangeModulePushforward.{u, u} B S hS f hf ⋙
      globalSectionsFunctor.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)) ⋙
      ModuleCat.restrictScalars ψY).obj G) where
  toFun s := (⟨fun V => (s : G.sections).1 ((smallBaseChange B S hS f hf).op.obj V),
    fun g => (s : G.sections).2 ((smallBaseChange B S hS f hf).op.map g)⟩ :
      ((smallBaseChangeModulePushforward.{u, u} B S hS f hf).obj G).sections)
  map_add' _ _ := rfl
  map_smul' a s := Subtype.ext (funext fun V =>
    congrArg (fun r => r • (show G.val.obj ((smallBaseChange B S hS f hf).op.obj V) from
      (s : G.sections).1 ((smallBaseChange B S hS f hf).op.obj V))) (h a V.unop))

/-- The restriction map `Γ(X, 𝓕) ⟶ Γ(Y, f_*𝓕)` along the base change of étale charts is
bijective. -/
theorem bijective_globalSectionsSmallBaseChangeLinearMap
    (h : GlobalSectionRingHomsCompatible B S hS f hf ψY ψX) (G : Modules.{u, u} B S hS X.1 X.2) :
    Function.Bijective (globalSectionsSmallBaseChangeLinearMap B S hS f hf ψY ψX h G) := by
  have := smallBaseChange_isMorphismOfSites B S hS f hf
  have hb := Functor.bijective_sectionsPrecomp_of_isMorphismOfSites_ulift.{u + 1, u}
    (J := SmallEtale.topology B S hS Y.1) (smallBaseChange B S hS f hf)
    ((sheafCompose (SmallEtale.topology B S hS X.1) (forget AddCommGrpCat.{u})).obj
      ((SheafOfModules.toSheaf _).obj G))
  refine ⟨fun s t hst => Subtype.ext (congrArg Subtype.val
    (hb.1 (Subtype.ext (congrArg Subtype.val hst) :
      Functor.sectionsPrecomp _ ⟨(s : G.sections).1, (s : G.sections).2⟩ =
        Functor.sectionsPrecomp _ ⟨(t : G.sections).1, (t : G.sections).2⟩))), fun t => ?_⟩
  obtain ⟨s, hs⟩ := hb.2 ⟨(t : ((smallBaseChangeModulePushforward.{u, u} B S hS f hf).obj
    G).sections).1, (t : ((smallBaseChangeModulePushforward.{u, u} B S hS f hf).obj G).sections).2⟩
  exact ⟨(⟨s.1, s.2⟩ : G.sections), Subtype.ext (congrArg Subtype.val hs)⟩

/-- **Global sections are unchanged by the direct image along a representable morphism, as
`A`-modules.** For `f : X ⟶ Y` representable and ring maps `A ⟶ Γ(Y, 𝒪_Y)`, `A ⟶ Γ(X, 𝒪_X)`
compatible with `f`, restriction of sections along the base change of étale charts identifies
`Γ(X, 𝓕)` with `Γ(Y, f_*𝓕)` as `A`-modules, naturally in `𝓕`; here `f_*` is the direct image
`AlgebraicGeometry.Space.smallBaseChangeModulePushforward` along chart base change. -/
def globalSectionsSmallBaseChangeIso (h : GlobalSectionRingHomsCompatible B S hS f hf ψY ψX) :
    globalSectionsFunctor.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) ⋙
        ModuleCat.restrictScalars ψX ≅
      (smallBaseChangeModulePushforward.{u, u} B S hS f hf :
          Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2) ⋙
        globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)) ⋙
        ModuleCat.restrictScalars ψY :=
  NatIso.ofComponents
    (fun G => LinearEquiv.toModuleIso (LinearEquiv.ofBijective _
      (bijective_globalSectionsSmallBaseChangeLinearMap B S hS f hf ψY ψX h G)))
    (fun _ => rfl)

/-- Restriction of scalars along a ring map is exact. -/
theorem preservesFiniteLimits_and_colimits_restrictScalars {R R' : Type*} [Ring R] [Ring R']
    (φ : R →+* R') :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{u + 1} φ) ∧
      PreservesFiniteColimits (ModuleCat.restrictScalars.{u + 1} φ) :=
  ((Functor.exact_tfae (ModuleCat.restrictScalars.{u + 1} φ)).out 2 4).mp
    fun T hT => (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (T.map (ModuleCat.restrictScalars.{u + 1} φ))).2
        ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).1 hT)

/-- `AlgebraicGeometry.Space.globalSectionsSmallBaseChangeIso` for the direct image of Stacks
03LU, through its identification `AlgebraicGeometry.Space.modulePushforwardChartIso` with the
direct image along chart base change. -/
def globalSectionsModulePushforwardLinearIso
    (h : GlobalSectionRingHomsCompatible B S hS f hf ψY ψX) :
    globalSectionsFunctor.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) ⋙
        ModuleCat.restrictScalars ψX ≅
      modulePushforward B S hS f ⋙
        globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)) ⋙
        ModuleCat.restrictScalars ψY :=
  globalSectionsSmallBaseChangeIso B S hS f hf ψY ψX h ≪≫
    Functor.isoWhiskerRight (modulePushforwardChartIso B S hS f hf).symm _

/-- **Stacks 0D2U as an isomorphism of `A`-modules**, in the universe of the structure sheaf.
Let `f : X ⟶ Y` be an affine morphism of algebraic spaces, `𝓕` a quasi-coherent `𝒪_X`-module and
`A ⟶ Γ(Y, 𝒪_Y)`, `A ⟶ Γ(X, 𝒪_X)` ring maps compatible with `f`. Then
`Hⁱ(X, 𝓕) ≅ Hⁱ(Y, f_*𝓕)` as `A`-modules, for every `i`. -/
def cohomologyOverRingIsoOfIsAffineHom (haff : IsAffineHom B S hS f.hom)
    (h : GlobalSectionRingHomsCompatible B S hS f hf ψY ψX)
    (G : Modules.{u, u} B S hS X.1 X.2) (hG : G.IsQuasicoherentOnSite) (q : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    have := hasInjectiveResolutions_modules B S hS Y.1 Y.2
    (ModuleCat.restrictScalars ψX).obj
        (((globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O))).rightDerived q).obj G) ≅
      (ModuleCat.restrictScalars ψY).obj
        (((globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS Y.1 Y.2).O))).rightDerived q).obj
          ((modulePushforward B S hS f).obj G)) := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := hasInjectiveResolutions_modules B S hS Y.1 Y.2
  have := enoughInjectives_modules B S hS Y.1 Y.2
  let ΓX := globalSectionsFunctor.{u + 1, u, u, u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
  let ΓY := globalSectionsFunctor.{u + 1, u, u, u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))
  let P := modulePushforward B S hS f
  have := modulePushforward_additive B S hS f
  have hX := preservesFiniteLimits_and_colimits_restrictScalars.{u} ψX
  have hY := preservesFiniteLimits_and_colimits_restrictScalars.{u} ψY
  have := hX.1
  have := hX.2
  have := hY.1
  have := hY.2
  have : (ModuleCat.restrictScalars.{u + 1} ψX).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  have : (ModuleCat.restrictScalars.{u + 1} ψY).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  have := preservesFiniteLimits_globalSectionsFunctor_structureRingSheaf B S hS Y.1 Y.2
  have hA : ∀ n, 0 < n → IsZero ((P.rightDerived n).obj G) := fun n hn =>
    isZero_rightDerived_modulePushforward_isAffineHom B S hS f haff G hG n hn
  have hGT : ∀ Z : Modules.{u, u} B S hS X.1 X.2, Injective Z →
      Stacks.RightDerivedComp.acyclic (ΓY ⋙ ModuleCat.restrictScalars ψY) (P.obj Z) := by
    intro Z hZ n hn
    exact ((ModuleCat.restrictScalars ψY).map_isZero
      (acyclic_globalSectionsFunctor_modulePushforward_of_injective B S hS f Z n hn)).of_iso
        ((Functor.rightDerivedCompIso ΓY (ModuleCat.restrictScalars ψY) n).app (P.obj Z))
  exact ((Functor.rightDerivedCompIso ΓX (ModuleCat.restrictScalars ψX) q).app G).symm ≪≫
    (Functor.rightDerivedIsoOfNatIso
      (globalSectionsModulePushforwardLinearIso B S hS f hf ψY ψX h) q).app G ≪≫
    Stacks.RightDerivedComp.objIsoOfAcyclicImage P (ΓY ⋙ ModuleCat.restrictScalars ψY) hA hGT q ≪≫
    (Functor.rightDerivedCompIso ΓY (ModuleCat.restrictScalars ψY) q).app (P.obj G)

/-- Restriction of scalars commutes with raising the universe of a module. -/
def restrictScalarsUliftIso.{w', v} {R R' : Type*} [Ring R] [Ring R'] (φ : R →+* R')
    (M : ModuleCat.{v} R') :
    (ModuleCat.restrictScalars.{max v w'} φ).obj ((ModuleCat.uliftFunctor.{w'} R').obj M) ≅
      (ModuleCat.uliftFunctor.{w'} R).obj ((ModuleCat.restrictScalars.{v} φ).obj M) :=
  Iso.refl _

/-- The cohomology of an `𝒪_X`-module with sections in the universe of the structure sheaf, in
the universe of the Euler characteristic, is the universe lift of its cohomology, as modules over
any ring mapping to `Γ(X, 𝒪_X)`. -/
def cohomologyUliftOverRingIso.{w} (Z : AlgebraicSpaces B S hS)
    (ψ : A →+* GlobalSectionRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)))
    (G : Modules.{u, u} B S hS Z.1 Z.2) (q : ℕ) :
    have := hasInjectiveResolutions_modules B S hS Z.1 Z.2
    (ModuleCat.restrictScalars ψ).obj
        ((globalModuleCohomology.{u + 1, u, u, w}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)) q).obj
          (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, max (u + 1) w} G)) ≅
      (ModuleCat.uliftFunctor.{max (u + 1) w} A).obj
        ((ModuleCat.restrictScalars ψ).obj
          (((globalSectionsFunctor.{u + 1, u, u, u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS Z.1 Z.2).O))).rightDerived q).obj G)) := by
  have := hasInjectiveResolutions_modules B S hS Z.1 Z.2
  have := hasSeparator_modules B S hS Z.1 Z.2
  have := site_hasSheafify_addCommGrp.{u + 1, u, w}
    (J := (smallEtaleRingedSite B S hS Z.1 Z.2).J)
  have := site_wEqualsLocallyBijective_addCommGrp.{u + 1, u, w}
    (J := (smallEtaleRingedSite B S hS Z.1 Z.2).J)
  have := moduleSheavesEnoughInjectives.{u + 1, u, u, w}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)
  exact (ModuleCat.restrictScalars ψ).mapIso
      ((rightDerivedGlobalSectionsUliftIso.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)
          q).app G).symm ≪≫
    restrictScalarsUliftIso.{max (u + 1) w} ψ _

/-- Stacks 0D2U, as an isomorphism of `A`-modules in the universe of the Euler
characteristic. Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over `S`, `𝓕` a
quasi-coherent `𝒪_X`-module with sections in the universe of the structure sheaf, and
`A ⟶ Γ(Y, 𝒪_Y)`, `A ⟶ Γ(X, 𝒪_X)` ring maps compatible with `f`. Then
`Hⁱ(X, 𝓕) ≅ Hⁱ(Y, f_*𝓕)` as `A`-modules for every `i`, the cohomology being that of the
universe lifts of the two modules to the universe of the small étale sites, in which
`AlgebraicGeometry.Space.eulerCharacteristic` (Stacks 0DN1) is taken. -/
def cohomologyUliftOverRingIsoOfIsAffineHom.{w} (haff : IsAffineHom B S hS f.hom)
    (h : GlobalSectionRingHomsCompatible B S hS f hf ψY ψX)
    (G : Modules.{u, u} B S hS X.1 X.2) (hG : G.IsQuasicoherentOnSite) (q : ℕ) :
    (ModuleCat.restrictScalars ψX).obj
        ((globalModuleCohomology.{u + 1, u, u, w}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) q).obj
          (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, max (u + 1) w} G)) ≅
      (ModuleCat.restrictScalars ψY).obj
        ((globalModuleCohomology.{u + 1, u, u, w}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)) q).obj
          (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, max (u + 1) w}
            ((modulePushforward B S hS f).obj G))) :=
  cohomologyUliftOverRingIso.{u, w} B S hS X ψX G q ≪≫
    (ModuleCat.uliftFunctor.{max (u + 1) w} A).mapIso
      (cohomologyOverRingIsoOfIsAffineHom B S hS f hf ψY ψX haff h G hG q) ≪≫
    (cohomologyUliftOverRingIso.{u, w} B S hS Y ψY ((modulePushforward B S hS f).obj G) q).symm

/-- Any two ring maps out of `ULift ℤ` are compatible with every representable morphism: ring
maps out of `ℤ` are unique. -/
theorem globalSectionRingHomsCompatible_ulift_int
    (ψY : ULift.{u} ℤ →+* GlobalSectionRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)))
    (ψX : ULift.{u} ℤ →+* GlobalSectionRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) :
    GlobalSectionRingHomsCompatible B S hS f hf ψY ψX := fun a W =>
  RingHom.congr_fun (RingHom.ext_int
    (((globalSectionEval _ (op ((smallBaseChange B S hS f hf).obj W))).comp ψX).comp
      (ULift.ringEquiv.{0, u} (R := ℤ)).symm.toRingHom)
    ((((smallBaseChangeSharp B S hS f hf).hom.app (op W)).hom.comp
      ((globalSectionEval _ (op W)).comp ψY)).comp
        (ULift.ringEquiv.{0, u} (R := ℤ)).symm.toRingHom)) a.down

/-- **Stacks 0D2U.** Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over `S` and `𝓕`
a quasi-coherent `𝒪_X`-module. Then `Hⁱ(X, 𝓕) = Hⁱ(Y, f_*𝓕)` for every `i ≥ 0`.

The cohomology is that of the universe lifts of the two modules to the universe of the small
étale sites, the universe in which `AlgebraicGeometry.Space.eulerCharacteristic` (Stacks 0DN1)
is taken; the isomorphism is one of abelian groups, and of `A`-modules for any ring maps to the
global functions compatible with `f`
(`AlgebraicGeometry.Space.cohomologyUliftOverRingIsoOfIsAffineHom`). -/
@[stacks 0D2U]
def cohomologyUliftIsoOfIsAffineHom.{w} (haff : IsAffineHom B S hS f.hom)
    (G : Modules.{u, u} B S hS X.1 X.2) (hG : G.IsQuasicoherentOnSite) (q : ℕ) :
    (forget₂ _ AddCommGrpCat.{max (u + 1) w}).obj
        ((globalModuleCohomology.{u + 1, u, u, w}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) q).obj
          (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, max (u + 1) w} G)) ≅
      (forget₂ _ AddCommGrpCat.{max (u + 1) w}).obj
        ((globalModuleCohomology.{u + 1, u, u, w}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)) q).obj
          (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, max (u + 1) w}
            ((modulePushforward B S hS f).obj G))) :=
  (forget₂ (ModuleCat (ULift.{u} ℤ)) AddCommGrpCat.{max (u + 1) w}).mapIso
    (cohomologyUliftOverRingIsoOfIsAffineHom.{u, w} B S hS f
      (relativelyRepresentable_of_isAffineHom B S hS f haff)
      ((Int.castRingHom _).comp ULift.ringEquiv.toRingHom)
      ((Int.castRingHom _).comp ULift.ringEquiv.toRingHom) haff
      (globalSectionRingHomsCompatible_ulift_int B S hS f _ _ _) G hG q)

/-- **The Euler characteristic is unchanged by the direct image along an affine morphism.** For
an affine `f : X ⟶ Y`, a quasi-coherent `𝒪_X`-module `𝓕`, a field `k` and ring maps
`k ⟶ Γ(Y, 𝒪_Y)`, `k ⟶ Γ(X, 𝒪_X)` compatible with `f`, the Euler characteristics of `𝓕` on `X`
and of `f_*𝓕` on `Y` agree. -/
theorem eulerCharacteristicAlong_modulePushforward_of_isAffineHom (k : Type u) [Field k]
    (ψY : k →+* GlobalSectionRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)))
    (ψX : k →+* GlobalSectionRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)))
    (haff : IsAffineHom B S hS f.hom) (h : GlobalSectionRingHomsCompatible B S hS f hf ψY ψX)
    (G : Modules.{u, u} B S hS X.1 X.2) (hG : G.IsQuasicoherentOnSite) :
    eulerCharacteristicAlong B S hS X.1 X.2 k ψX G =
      eulerCharacteristicAlong B S hS Y.1 Y.2 k ψY ((modulePushforward B S hS f).obj G) := by
  unfold eulerCharacteristicAlong
  refine finsum_congr fun q => ?_
  congr 2
  exact (cohomologyUliftOverRingIsoOfIsAffineHom.{u, u + 1} B S hS f hf ψY ψX haff h G hG
    q).toLinearEquiv.finrank_eq

end AlgebraicGeometry.Space

end
