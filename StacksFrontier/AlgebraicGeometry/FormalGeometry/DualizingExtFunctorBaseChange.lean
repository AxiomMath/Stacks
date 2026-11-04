module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.LocalCohomologyMatlisDualModel
public import StacksFrontier.Homology.Tor.BaseChangeTensorIso
public import StacksFrontier.RingTheory.Dualizing.ExtBaseChangeCompletedAway
public import StacksFrontier.RingTheory.Dualizing.RelativeComposition
public import StacksFrontier.RingTheory.Dualizing.RelativeUniquenessInternalHomCompare

/-!
# Flat base change for the Ext functor into a fixed object, functorially

Let `A → S` be a flat map of Noetherian rings and let `ω` be an object of `D(A)`. This file
builds the comparison
`S ⊗_A H^{-i}(RHom_A(X, ω)) ⟶ H^{-i}(RHom_S(S ⊗_A X, ω ⊗ᴸ_A S))`
as a morphism of functors on `(ModuleCat A)ᵒᵖ`, and shows it is an isomorphism at every finite
`A`-module. Everything is assembled from comparisons that already exist and are already
natural; nothing new about flat base change is proved here.

## Main definitions

* `Stacks.Algebraization.dualizingExtFunctorBaseChange` — the comparison, as a morphism of
  functors `(ModuleCat A)ᵒᵖ ⥤ ModuleCat S`.
* `Stacks.Algebraization.dualizingExtSystemBaseChangeNatIso` — the consequence the source of
  [Stacks, Tag 0EHK] needs: for an inverse system of *finite* `A`-modules the comparison is an
  isomorphism of systems, so the system may be base changed as a system.
* `Stacks.Algebraization.dualizingExtFunctorLocalizationBaseChange` and
  `Stacks.Algebraization.dualizingExtSystemLocalizationNatIso` — the two above at
  `A → Localization T`, where flatness is automatic.
* `Stacks.Algebraization.dualizingExtFunctorAdicCompletionBaseChange` and
  `Stacks.Algebraization.dualizingExtSystemAdicCompletionNatIso` — the two above at `A → A^∧`,
  where flatness is again automatic. Together with the localization case these are the two base
  changes the route of [Stacks, Tag 0EHK] makes, `A → A_f → (A_f)^∧`.

## Main results

* `Stacks.Algebraization.isIso_dualizingExtFunctorBaseChange_app` — the component at a finite
  module is an isomorphism.

## Implementation notes

`Stacks.Algebraization.dualizingExtFunctor` is written with the same-universe tensor--Hom
adjunction `StacksDraft.DerivedHom.derivedHomAdjunction`, whereas every available flat
base-change statement — `Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange` and the
per-object equivalences built on it — is written with the universe-polymorphic
`StacksDraft.DerivedHom.derivedHomAdjunctionOverRing`. The two are *not* definitionally equal,
but this mismatch does not make the Ext comparison natural only for the other model: the two
models are compared by
`Dualizing.modelHomNatIsoDerivedHomAdjunctionOverRing`, which is an isomorphism of *bifunctors*
on `D(A)ᵒᵖ × D(A)` and so may be whiskered into either slot. Freezing its second slot is
`Dualizing.derivedHomIntoFunctorNatIso` below, and that is the whole content of the model step.

The comparison is a natural transformation and not a natural isomorphism, and this is not a
defect of the assembly. Its invertibility comes from
`Dualizing.isIso_derivedHomBaseChange_single`, which needs the source module to be finite; at an
infinite module the map is not expected to be invertible. Naturality holds on all of
`(ModuleCat A)ᵒᵖ` regardless, which is exactly what makes
`Stacks.Algebraization.dualizingExtSystemBaseChangeNatIso` available: naturality is inherited
from the whole category, invertibility is checked index by index.

What this subsumes. `Dualizing.extBaseChangeLinearEquiv` is the content of
`Stacks.Algebraization.isIso_dualizingExtFunctorBaseChange_app` at a single module, with `Ext`
in place of `H^{-i}(RHom)` and with the base change written as a tensor product rather than as
extension of scalars; `Dualizing.localizedExtLinearEquiv` is the same statement with `S` a
localization, where flatness is automatic. Neither is rederived from the statement here: both live in other files, and `Dualizing.localizedExtLinearEquiv` additionally has a `private` clone at
`StacksFrontier.RingTheory.Dualizing.UpperShriek.CompleteIntersectionLocal`.
`Dualizing.extAdicSystemCompletionAddEquiv` is *not* subsumed: it composes flat base change with
a completion comparison, and only its flat half appears here.

## References

* [Stacks Project, Tag 0EHK](https://stacks.math.columbia.edu/tag/0EHK)
* [Stacks Project, Tag 0A6A](https://stacks.math.columbia.edu/tag/0A6A), the invertibility input.
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63), the adjunction.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite StacksDraft.DerivedHom

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

/-! ### The model step, and the two flat comparisons made natural -/

variable {A S : Type u} [CommRing A] [CommRing S] [Algebra A S]

/-- **The two spellings of `RHom_A(-, ω)` agree as functors.**
`Dualizing.derivedHomIntoFunctor` uses the same-universe adjunction
`StacksDraft.DerivedHom.derivedHomAdjunction` and
`Dualizing.dualizingDerivedHomFunctor` uses the universe-polymorphic
`StacksDraft.DerivedHom.derivedHomAdjunctionOverRing`; both freeze the second slot of their
bifunctor at `ω`, so this is `Dualizing.modelHomNatIsoDerivedHomAdjunctionOverRing` whiskered
into the first slot. It is the step that lets a flat base-change statement proved for the
second spelling be read as a statement about the first. -/
def derivedHomIntoFunctorNatIso (ω : DerivedCategory (ModuleCat.{u} A)) :
    derivedHomIntoFunctor ω ≅ dualizingDerivedHomFunctor.{u, u} A ω :=
  Functor.isoWhiskerLeft _ (modelHomNatIsoDerivedHomAdjunctionOverRing A)

/-- **Flat derived extension of scalars of a module in degree zero, naturally in the module.**
`Dualizing.totalDerivedExtensionScalarsSingleIsoOfFlat` is the component of this at one module;
both are the chosen derived functor's agreement with the degreewise one followed by the
degreewise one's compatibility with the degree-zero embedding, and that agreement
(`Dualizing.totalDerivedExtensionScalarsIsoOfFlat`) is already an isomorphism of functors. -/
def totalDerivedExtensionScalarsSingleNatIsoOfFlat (hf : (algebraMap A S).Flat) :
    DerivedCategory.singleFunctor (ModuleCat.{u} A) 0 ⋙
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (algebraMap A S)).functor ≅
      ModuleCat.extendScalars.{u, u, u} (algebraMap A S) ⋙
        DerivedCategory.singleFunctor (ModuleCat.{u} S) 0 :=
  letI := (preservesFiniteLimits_extendScalars_of_flat (algebraMap A S) hf).1
  letI := (preservesFiniteLimits_extendScalars_of_flat (algebraMap A S) hf).2
  Functor.isoWhiskerLeft _ (totalDerivedExtensionScalarsIsoOfFlat (algebraMap A S) hf) ≪≫
    (ModuleCat.extendScalars.{u, u, u} (algebraMap A S)).mapDerivedCategorySingleFunctor 0

section AbstractLeftDerived

/-- The chosen total derived extension of scalars agrees with any other left derived functor of
the degreewise one, as an isomorphism of functors. This is
`CategoryTheory.Functor.leftDerivedUnique` at the chosen construction, named because both
comparisons below are transported along it. -/
def leftDerivedExtensionScalarsIso
    (F : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} S))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A S)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))] :
    F ≅ (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A S)).functor :=
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (algebraMap A S)
  let cmpD : DerivedCategory.Q ⋙ D.functor ⟶
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A S)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q := D.comparison
  let : D.functor.IsLeftDerivedFunctor cmpD
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) := D.isLeftDerived
  Functor.leftDerivedUnique D.functor F comparison cmpD
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))

/-- **A left derived extension of scalars along a flat map carries a module in degree zero to
its base change in degree zero, naturally in the module.** -/
def leftDerivedExtensionScalarsSingleNatIso
    (F : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} S))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A S)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))]
    (hf : (algebraMap A S).Flat) :
    DerivedCategory.singleFunctor (ModuleCat.{u} A) 0 ⋙ F ≅
      ModuleCat.extendScalars.{u, u, u} (algebraMap A S) ⋙
        DerivedCategory.singleFunctor (ModuleCat.{u} S) 0 :=
  Functor.isoWhiskerLeft _ (leftDerivedExtensionScalarsIso F comparison) ≪≫
    totalDerivedExtensionScalarsSingleNatIsoOfFlat hf

/-- **A left derived extension of scalars along a flat map commutes with cohomology, naturally
in the derived object.** This is
`CochainComplex.DerivedTensor.derivedExtensionScalarsHomologyIso` transported to an arbitrary
left derived functor of the degreewise extension. -/
def leftDerivedExtensionScalarsHomologyNatIso
    (F : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} S))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A S)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))]
    (hf : (algebraMap A S).Flat) (i : ℤ) :
    F ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} S) i ≅
      DerivedCategory.homologyFunctor (ModuleCat.{u} A) i ⋙
        ModuleCat.extendScalars.{u, u, u} (algebraMap A S) :=
  Functor.isoWhiskerRight (leftDerivedExtensionScalarsIso F comparison) _ ≪≫
    CochainComplex.DerivedTensor.derivedExtensionScalarsHomologyIso.{u, u, u}
      (algebraMap A S) hf i

/-- **Flat base change of derived Hom into a fixed object, as a morphism of functors.**
`Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChangeNatTrans` is the same morphism of
bifunctors on `D(A)ᵒᵖ × D(A)`; here the second slot is frozen at `ω`, the component being the
base-change map at `(X, ω)` and the naturality square being
`Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange_naturality` with the identity of `ω`
in the covariant variable. -/
def dualizingDerivedHomFunctorBaseChange
    (F : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} S))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A S)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))]
    (ω : DerivedCategory (ModuleCat.{u} A)) :
    dualizingDerivedHomFunctor.{u, u} A ω ⋙ F ⟶
      F.op ⋙ dualizingDerivedHomFunctor.{u, u} S (F.obj ω) where
  app X := Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{u, u, u}
    (algebraMap A S) F comparison X.unop ω
  naturality X Y g := by
    have h := Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange_naturality.{u, u, u}
      (algebraMap A S) F comparison g.unop (𝟙 ω)
    rw [CategoryTheory.Functor.map_id] at h
    exact h

end AbstractLeftDerived

end Dualizing

namespace Stacks.Algebraization

variable {A S : Type u} [CommRing A] [CommRing S] [Algebra A S]
  (F : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} S))
  (comparison : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{u, u, u} (algebraMap A S)).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [F.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))]

/-- **The isomorphisms preceding the base-change step.** The model step
`Dualizing.derivedHomIntoFunctorNatIso`, which rewrites `Dualizing.derivedHomIntoFunctor` as
`Dualizing.dualizingDerivedHomFunctor`, followed by
`Dualizing.leftDerivedExtensionScalarsHomologyNatIso`, which moves the base change past
`H^{-i}` and is where flatness of `A → S` is used.

This is named, rather than inlined into
`Stacks.Algebraization.dualizingExtFunctorBaseChange`, so that the composite's source is
recorded as `Stacks.Algebraization.dualizingExtFunctor` itself. Inlined, the source is only
*definitionally* that functor, and the invertibility proof cannot take the composite apart
without unfolding a definition the statement does not mention. -/
def dualizingExtFunctorBaseChangeSourceIso (hf : (algebraMap A S).Flat)
    (ω : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    dualizingExtFunctor ω i ⋙ ModuleCat.extendScalars.{u, u, u} (algebraMap A S) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).op ⋙
        (Dualizing.dualizingDerivedHomFunctor.{u, u} A ω ⋙ F) ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} S) (-i) :=
  Functor.isoWhiskerLeft (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).op
      (Functor.isoWhiskerRight (Dualizing.derivedHomIntoFunctorNatIso ω)
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-i) ⋙
          ModuleCat.extendScalars.{u, u, u} (algebraMap A S))) ≪≫
    Functor.isoWhiskerLeft
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).op ⋙
        Dualizing.dualizingDerivedHomFunctor.{u, u} A ω)
      (Dualizing.leftDerivedExtensionScalarsHomologyNatIso F comparison hf (-i)).symm

/-- **The isomorphisms following the base-change step.**
`Dualizing.leftDerivedExtensionScalarsSingleNatIso`, which identifies the derived base change of
a module in degree zero with its base change in degree zero, followed by the model step of
`Dualizing.derivedHomIntoFunctorNatIso` run backwards over `S`. Named for the same reason as
`Stacks.Algebraization.dualizingExtFunctorBaseChangeSourceIso`. -/
def dualizingExtFunctorBaseChangeTargetIso (hf : (algebraMap A S).Flat)
    (ω : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).op ⋙
        (F.op ⋙ Dualizing.dualizingDerivedHomFunctor.{u, u} S (F.obj ω)) ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} S) (-i) ≅
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A S)).op ⋙
        dualizingExtFunctor (F.obj ω) i :=
  Functor.isoWhiskerRight
      (NatIso.op (Dualizing.leftDerivedExtensionScalarsSingleNatIso F comparison hf)).symm
      (Dualizing.dualizingDerivedHomFunctor.{u, u} S (F.obj ω) ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} S) (-i)) ≪≫
    Functor.isoWhiskerLeft (ModuleCat.extendScalars.{u, u, u} (algebraMap A S)).op
      (Functor.isoWhiskerLeft (DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).op
        (Functor.isoWhiskerRight (Dualizing.derivedHomIntoFunctorNatIso (F.obj ω)).symm
          (DerivedCategory.homologyFunctor (ModuleCat.{u} S) (-i))))

/-- **Flat base change for `Stacks.Algebraization.dualizingExtFunctor`, functorially.** For a
flat map `A → S` the base change of `X ↦ H^{-i}(RHom_A(X, ω))` maps to
`X ↦ H^{-i}(RHom_S(S ⊗_A X, ω ⊗ᴸ_A S))` as functors on `(ModuleCat A)ᵒᵖ`.

Four comparisons compose, and each is already natural in the derived object:

* the model step `Dualizing.derivedHomIntoFunctorNatIso`, which rewrites
  `Dualizing.derivedHomIntoFunctor` as `Dualizing.dualizingDerivedHomFunctor`;
* `Dualizing.leftDerivedExtensionScalarsHomologyNatIso`, flatness of `A → S`, used to move the
  base change past `H^{-i}`;
* `Dualizing.dualizingDerivedHomFunctorBaseChange`, the only step that is not an isomorphism;
* `Dualizing.leftDerivedExtensionScalarsSingleNatIso`, which identifies the derived base change
  of a module in degree zero with its base change in degree zero.

Its components are isomorphisms at finite modules
(`Stacks.Algebraization.isIso_dualizingExtFunctorBaseChange_app`) and not in general. -/
def dualizingExtFunctorBaseChange (hf : (algebraMap A S).Flat)
    (ω : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    dualizingExtFunctor ω i ⋙ ModuleCat.extendScalars.{u, u, u} (algebraMap A S) ⟶
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A S)).op ⋙
        dualizingExtFunctor (F.obj ω) i :=
  (dualizingExtFunctorBaseChangeSourceIso F comparison hf ω i).hom ≫
    Functor.whiskerLeft (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).op
      (Functor.whiskerRight (Dualizing.dualizingDerivedHomFunctorBaseChange F comparison ω)
        (DerivedCategory.homologyFunctor (ModuleCat.{u} S) (-i))) ≫
    (dualizingExtFunctorBaseChangeTargetIso F comparison hf ω i).hom

/-- **The comparison is an isomorphism at a finite module.** Four of the five comparisons
composing `Stacks.Algebraization.dualizingExtFunctorBaseChange` are isomorphisms outright, and
the fifth is `Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange` at
`(M[0], ω)`, invertible by `Dualizing.isIso_derivedHomBaseChange_single`: the third disjunct of
[Stacks, Tag 0A6A], with `M[0]` pseudo-coherent because `M` is a finite module over a Noetherian
ring and `ω` bounded below.

Finiteness of `M` is used only here. It is why
`Stacks.Algebraization.dualizingExtFunctorBaseChange` is stated as a morphism of functors and
not as an isomorphism of functors: at an infinite module the comparison is not expected to be
invertible, while naturality holds on all of `(ModuleCat A)ᵒᵖ`. -/
theorem isIso_dualizingExtFunctorBaseChange_app [IsNoetherianRing A]
    (hf : (algebraMap A S).Flat) (ω : DerivedCategory (ModuleCat.{u} A))
    (hωge : ∃ b : ℤ, ω.IsGE b) (i : ℤ) (M : ModuleCat.{u} A) (hM : Module.Finite A M) :
    IsIso ((dualizingExtFunctorBaseChange F comparison hf ω i).app (op M)) := by
  have := hM
  have hbc : IsIso (Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{u, u, u}
      (algebraMap A S) F comparison
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ω) :=
    Dualizing.isIso_derivedHomBaseChange_single F comparison
      (RingHom.flat_algebraMap_iff.mp hf) M ω hωge
  simp only [dualizingExtFunctorBaseChange, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Dualizing.dualizingDerivedHomFunctorBaseChange,
    Functor.op_obj, unop_op]
  exact IsIso.comp_isIso' inferInstance
    (IsIso.comp_isIso' (@Functor.map_isIso _ _ _ _ _ _ _ _ hbc) inferInstance)

/-- **An inverse system of finite modules may be base changed as a system.** This is the form
the source of [Stacks, Tag 0EHK] needs and the reason the comparison above is built at functor
level: `Stacks.Algebraization.dualizingExtSystem` is
`Stacks.Algebraization.dualizingExtFunctor` restricted along the system
(`Stacks.Algebraization.dualizingExtSystem_eq`), so restricting the comparison along the system
gives a morphism of systems whose naturality is inherited from the whole of `(ModuleCat A)ᵒᵖ`,
and each component is an isomorphism because each term of the system is finite.

The per-object equivalences `Dualizing.extBaseChangeLinearEquiv` and
`Dualizing.localizedExtLinearEquiv` give the components but no compatibility with the transition
maps, which is exactly what is needed here. -/
def dualizingExtSystemBaseChangeNatIso [IsNoetherianRing A]
    (hf : (algebraMap A S).Flat) (ω : DerivedCategory (ModuleCat.{u} A))
    (hωge : ∃ b : ℤ, ω.IsGE b) (i : ℤ) (M : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hfin : ∀ n : ℕ, Module.Finite A (M.obj (op n))) :
    dualizingExtSystem M ω i ⋙ ModuleCat.extendScalars.{u, u, u} (algebraMap A S) ≅
      M.rightOp ⋙ (ModuleCat.extendScalars.{u, u, u} (algebraMap A S)).op ⋙
        dualizingExtFunctor (F.obj ω) i :=
  NatIso.ofComponents
    (fun n => by
      haveI hn : IsIso ((dualizingExtFunctorBaseChange F comparison hf ω i).app
          (op (M.obj (op n)))) :=
        isIso_dualizingExtFunctorBaseChange_app F comparison hf ω hωge i (M.obj (op n)) (hfin n)
      -- the invertibility is passed to `asIso` explicitly: the expected type here is the
      -- component of the restricted system, which is the component of the comparison only up
      -- to unfolding `Stacks.Algebraization.dualizingExtSystem`
      exact @asIso _ _ _ _ _ hn)
    (fun g => (Functor.whiskerLeft M.rightOp
      (dualizingExtFunctorBaseChange F comparison hf ω i)).naturality g)

/-! ### The localization case -/

section Localization

variable {A : Type u} [CommRing A] (T : Submonoid A)

/-- **The comparison at a localization.** `Stacks.Algebraization.dualizingExtFunctorBaseChange`
for `A → Localization T` and the chosen derived extension of scalars: a localization is flat, so
no flatness hypothesis is needed. -/
def dualizingExtFunctorLocalizationBaseChange (ω : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    dualizingExtFunctor ω i ⋙
        ModuleCat.extendScalars.{u, u, u} (algebraMap A (Localization T)) ⟶
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Localization T))).op ⋙
        dualizingExtFunctor
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            (algebraMap A (Localization T))).functor.obj ω) i :=
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (algebraMap A (Localization T))
  let cmpD : DerivedCategory.Q ⋙ D.functor ⟶
      (ModuleCat.extendScalars.{u, u, u}
          (algebraMap A (Localization T))).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q := D.comparison
  let : D.functor.IsLeftDerivedFunctor cmpD
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) := D.isLeftDerived
  dualizingExtFunctorBaseChange D.functor cmpD
    (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (Localization T) T)) ω i

/-- **An inverse system of finite modules localizes as a system**, which is the statement the
`hzero` input of `Stacks.Algebraization.isEssentiallyConstantModFiniteLength_of_support` asks
for: the vanishing of `Stacks.Algebraization.dualizingExtSystem` at a prime is a statement about
the localized system, and this says the localized system *is* the Ext system of the localized
data, compatibly with the transition maps. -/
def dualizingExtSystemLocalizationNatIso [IsNoetherianRing A]
    (ω : DerivedCategory (ModuleCat.{u} A)) (hωge : ∃ b : ℤ, ω.IsGE b) (i : ℤ)
    (M : ℕᵒᵖ ⥤ ModuleCat.{u} A) (hfin : ∀ n : ℕ, Module.Finite A (M.obj (op n))) :
    dualizingExtSystem M ω i ⋙
        ModuleCat.extendScalars.{u, u, u} (algebraMap A (Localization T)) ≅
      M.rightOp ⋙ (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Localization T))).op ⋙
        dualizingExtFunctor
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            (algebraMap A (Localization T))).functor.obj ω) i :=
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (algebraMap A (Localization T))
  let cmpD : DerivedCategory.Q ⋙ D.functor ⟶
      (ModuleCat.extendScalars.{u, u, u}
          (algebraMap A (Localization T))).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q := D.comparison
  let : D.functor.IsLeftDerivedFunctor cmpD
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) := D.isLeftDerived
  dualizingExtSystemBaseChangeNatIso D.functor cmpD
    (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (Localization T) T)) ω hωge i M hfin

end Localization

/-! ### The adic completion case -/

section AdicCompletion

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (J : Ideal A)

/-- **The comparison at an adic completion.**
`Stacks.Algebraization.dualizingExtFunctorBaseChange` for `A → A^∧` and the chosen derived
extension of scalars. No flatness hypothesis is needed: the `J`-adic completion of a Noetherian
ring is flat over it, `AdicCompletion.flat_of_isNoetherian`. -/
def dualizingExtFunctorAdicCompletionBaseChange (ω : DerivedCategory (ModuleCat.{u} A))
    (i : ℤ) :
    dualizingExtFunctor ω i ⋙
        ModuleCat.extendScalars.{u, u, u} (algebraMap A (AdicCompletion J A)) ⟶
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A (AdicCompletion J A))).op ⋙
        dualizingExtFunctor
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            (algebraMap A (AdicCompletion J A))).functor.obj ω) i :=
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (algebraMap A (AdicCompletion J A))
  let cmpD : DerivedCategory.Q ⋙ D.functor ⟶
      (ModuleCat.extendScalars.{u, u, u}
          (algebraMap A (AdicCompletion J A))).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q := D.comparison
  let : D.functor.IsLeftDerivedFunctor cmpD
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) := D.isLeftDerived
  dualizingExtFunctorBaseChange D.functor cmpD
    (RingHom.flat_algebraMap_iff.mpr inferInstance) ω i

/-- **An inverse system of finite modules completes as a system.** This is the completion half of
the route of [Stacks, Tag 0EHK], and it asks for nothing beyond
`Stacks.Algebraization.dualizingExtSystemBaseChangeNatIso`: the only hypothesis there is
flatness, and `A → A^∧` is flat over a Noetherian ring. So the completion needs no comparison of
its own, and in particular the per-object `Dualizing.extAdicSystemCompletionAddEquiv`, which is
an isomorphism of additive groups at one index with no statement about the transition maps, is
not what the route should consume.

The ring `Rig.CompletedAway I f` of the source is this at `A := Localization.Away f` and
`J := I.map (algebraMap A (Localization.Away f))`, that being what `Rig.CompletedAway` unfolds
to; flatness of `A_f → (A_f)^∧` is then the instance above and nothing else is required. -/
def dualizingExtSystemAdicCompletionNatIso (ω : DerivedCategory (ModuleCat.{u} A))
    (hωge : ∃ b : ℤ, ω.IsGE b) (i : ℤ) (M : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hfin : ∀ n : ℕ, Module.Finite A (M.obj (op n))) :
    dualizingExtSystem M ω i ⋙
        ModuleCat.extendScalars.{u, u, u} (algebraMap A (AdicCompletion J A)) ≅
      M.rightOp ⋙ (ModuleCat.extendScalars.{u, u, u} (algebraMap A (AdicCompletion J A))).op ⋙
        dualizingExtFunctor
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            (algebraMap A (AdicCompletion J A))).functor.obj ω) i :=
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (algebraMap A (AdicCompletion J A))
  let cmpD : DerivedCategory.Q ⋙ D.functor ⟶
      (ModuleCat.extendScalars.{u, u, u}
          (algebraMap A (AdicCompletion J A))).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q := D.comparison
  let : D.functor.IsLeftDerivedFunctor cmpD
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) := D.isLeftDerived
  dualizingExtSystemBaseChangeNatIso D.functor cmpD
    (RingHom.flat_algebraMap_iff.mpr inferInstance) ω hωge i M hfin

end AdicCompletion

end Stacks.Algebraization

end
