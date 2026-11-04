module

public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KernelIdealSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantCoefficients
public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstructibleSheaves
public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.AdicSheaves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.LocallyFiniteTorDimension
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedSites
public import StacksFrontier.Deformation.ToposThickening.DerivedComplexLift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# Constructible derived sheaves on the pro-étale site

Let `Λ` be a Noetherian ring, `I ⊆ Λ` an ideal, and `X` a scheme. An object `K` of
`D(X_proét, Λ)` is *constructible* when it is derived complete with respect to `I` and its
derived reduction `K ⊗_Λ^L Λ/I` has constructible cohomology sheaves and locally has finite Tor
dimension. The constructible objects form the full subcategory `D_cons(X, Λ)`.

An object `K` of `D(X_proét, Λ)` is *adic lisse* when it is pro-étale locally isomorphic to the
complex `\underline{M^a}^∧ → ⋯ → \underline{M^b}^∧` of completed constant sheaves attached to a
finite complex `M^•` of finite projective `Λ^∧`-modules, and *adic constructible* when every
affine open of `X` decomposes into constructible locally closed subschemes on which the
restriction of `K` is adic lisse.

## Main definitions

* `AlgebraicGeometry.ProEtale.constantCoefficientRingedSite`: the small pro-étale site of `X`
  ringed by the constant sheaf of the coefficient ring.
* `AlgebraicGeometry.ProEtale.DerivedSheaves`: the unbounded derived category
  `D(X_proét, Λ)` of sheaves of modules over that ring sheaf.
* `AlgebraicGeometry.ProEtale.toCoefficientModuleSheaf`: a sheaf of modules over the constant
  coefficient ring sheaf, read as a sheaf of `Λ`-modules.
* `AlgebraicGeometry.ProEtale.constantCoefficientReduction`: reduction modulo `I` on constant
  coefficient ring sheaves.
* `AlgebraicGeometry.ProEtale.constantCoefficientRingReduction`: that reduction on the
  underlying sheaves of rings.
* `AlgebraicGeometry.ProEtale.constantCoefficientIdealSheaf`: the ideal sheaf cut out by `I`.
* `AlgebraicGeometry.ProEtale.DerivedReduction`: a derived base change `- ⊗_Λ^L Λ/I`.
* `AlgebraicGeometry.ProEtale.HasConstructibleCohomology`: constructibility of every cohomology
  sheaf.
* `AlgebraicGeometry.ProEtale.IsConstructibleDerivedSheaf`: the constructibility condition.
* `AlgebraicGeometry.ProEtale.constructibleDerivedSheaves`: the full subcategory
  `D_cons(X, Λ)`.
* `AlgebraicGeometry.ProEtale.moduleSheafOverConstantCoefficientsFunctor`: a sheaf of
  `Λ`-modules read as a sheaf of modules over the constant coefficient ring sheaf.
* `AlgebraicGeometry.ProEtale.adicQuotientModuleFunctor`: the tower `n ↦ M/IⁿM`, functorially
  in `M`.
* `AlgebraicGeometry.ProEtale.completedConstantCoefficientSheafFunctor`: the completed constant
  sheaf `\underline{M}^∧`, over the constant coefficient ring sheaf.
* `AlgebraicGeometry.ProEtale.completedConstantCoefficientComplex`: the complex of completed
  constant sheaves attached to a complex of `Λ^∧`-modules.
* `AlgebraicGeometry.ProEtale.CoefficientRestriction`: inverse image of sheaves of coefficient
  modules along a morphism of schemes, with its exactness.
* `AlgebraicGeometry.ProEtale.IsAdicLisseDerivedSheaf`: part (1) of the adic condition.
* `AlgebraicGeometry.ProEtale.IsAdicConstructibleDerivedSheaf`: part (2) of the adic condition.

## Implementation notes

The scheme, the coefficient ring and the size of the module sections have independent universe
parameters `u`, `r` and `w`; sections live in `max (u + 1) r w`, which contains the site and the
coefficients and is otherwise arbitrary. The coefficient ring is lifted into that universe by
`ULift` so that the structure sheaf and the modules have their sections in one universe, which
is what the sheaves-of-modules API of a ringed site asks for; `ULift.ringEquiv` identifies the
lift with `Λ`, so nothing about the coefficients changes. This is the convention of the étale
counterpart `AlgebraicGeometry.constantCoefficientRingedSite` of Stacks 03TR.

Derived reduction is not constructed here. It is derived base change along the reduction map of
constant coefficient ring sheaves, which is taken as a datum
`Deformation.ComplexLift.DerivedExtensionOfScalars` of Stacks 0DIZ: any two such data are
canonically isomorphic by `Deformation.ComplexLift.DerivedExtensionOfScalars.baseChangeIso`, so
the condition below does not depend on the choice, and instantiating the parameter specialises
it. Locally finite Tor dimension is likewise measured against a family of derived tensor
products on the slices, as everywhere in this development and as in the étale counterpart
`Stacks.EtaleCohomology.ConstructibleFiniteTorDerivedCategory` of Stacks 03TQ.

Derived completeness is taken along the ideal sheaf `I·O`, the sectionwise kernel of reduction
modulo `I`, which is `SheafOfModules.kerIdeal` of the reduction map. Cohomology is read as a
sheaf of `Λ`-modules by restricting scalars along the canonical map from `Λ` to the global
sections of the constant coefficient ring sheaf, which is why the site is used through its
terminal object.

The source's two conditions are stated as one nested conjunction, and the subcategory as an
`ObjectProperty.FullSubcategory`, both as abbreviations, so that a client uses the projections
of the conjunction and the existing full-subcategory API directly.

The local model of an adic lisse complex is built as a functor applied degreewise, not as a
complex whose terms happen to be completed constant sheaves: this is what makes its
differentials the ones induced by the differentials of `M^•`, which is exactly the difference
between the definition below and the weaker local structure of Stacks 09C3, where the
differentials need not be constant. Its terms are the completed constant sheaves
`AlgebraicGeometry.ProEtale.completedConstantSheaf` of Stacks 09BT, read over the constant
coefficient ring sheaf, as
`AlgebraicGeometry.ProEtale.completedConstantCoefficientSheafFunctor_obj` records.

Noetherianity of `Λ` is needed nowhere in the two adic conditions, so neither assumes it, as
in the sheaf-level `AlgebraicGeometry.ProEtale.IsAdicLisse` of Stacks 09BT. "Locally
isomorphic" is read as in that sheaf-level condition: every object of the small pro-étale site
has a covering family on whose members the restrictions are isomorphic.

Restriction to an object of the site is `SheafOfModules.overFunctor`, so it involves no choice;
only its right exactness is assumed, left exactness being
`SheafOfModules.preservesFiniteLimits_pushforward`. Restriction along a morphism of schemes is
not constructed: `AlgebraicGeometry.ProEtale.CoefficientRestriction` asks for an exact functor
which is a left adjoint of the pushforward along the canonical comparison
`\underline{Λ} ⟶ i_* \underline{Λ}` of constant coefficient ring sheaves, which determines it
up to a unique isomorphism; since being adic lisse is invariant under isomorphism, quantifying
over such data existentially states the source's condition on `K|_{U_i}`.

## References

* [Stacks Project, Tag 09C1](https://stacks.math.columbia.edu/tag/09C1)
* [Stacks Project, Tag 09C4](https://stacks.math.columbia.edu/tag/09C4)
* [Stacks Project, Tag 09BT](https://stacks.math.columbia.edu/tag/09BT)
* [Stacks Project, Tag 0999](https://stacks.math.columbia.edu/tag/0999)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 09AJ](https://stacks.math.columbia.edu/tag/09AJ)
* [Stacks Project, Tag 0DIZ](https://stacks.math.columbia.edu/tag/0DIZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u r w

namespace AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard
  SheafOfModules.hasSheafify_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat

variable (X : Scheme.{u}) (Λ : Type r) [CommRing Λ]

/-- The small pro-étale site of `X`, ringed by the constant sheaf of the coefficient ring `Λ`
lifted into the universe of the module sections. -/
abbrev constantCoefficientRingedSite : RingedSite.{u + 1, u, max (u + 1) r w} where
  C := X.ProEt
  J := Scheme.ProEt.topology X
  O := (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{max (u + 1) r w}).obj
    (CommRingCat.of (ULift.{max (u + 1) w} Λ))

/-- The unbounded derived category `D(X_proét, Λ)` of pro-étale sheaves of modules over the
constant coefficient ring sheaf. -/
abbrev DerivedSheaves :=
  RingedSite.DerivedModules.{u + 1, u, max (u + 1) r w, max (u + 1) r w + 1}
    (constantCoefficientRingedSite.{u, r, w} X Λ)

/-- The canonical ring map from the coefficients to the sections of the constant coefficient
ring sheaf over the terminal object of the pro-étale site. -/
def toCoefficientSections :
    Λ →+* ((Stacks.SheafOfModules.Tensor.ringSheaf (constantCoefficientRingedSite.{u, r, w} X Λ).O)).obj.obj
      (op (⊤_ X.ProEt)) :=
  (((toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{max (u + 1) w} Λ)))).app (op (⊤_ X.ProEt))).hom).comp
    (ULift.ringEquiv.{r, max (u + 1) w} (R := Λ)).symm.toRingHom

/-- A sheaf of modules over the constant coefficient ring sheaf, read as a sheaf of
`Λ`-modules: take sections over the terminal object of the site and restrict scalars along
`AlgebraicGeometry.ProEtale.toCoefficientSections`. -/
def toCoefficientModuleSheaf :
    RingedSite.Modules.{u + 1, u, max (u + 1) r w}
        (constantCoefficientRingedSite.{u, r, w} X Λ) ⥤
      Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) r w} Λ) := by
  haveI : (Scheme.ProEt.topology X).HasSheafCompose
      (ModuleCat.restrictScalars.{max (u + 1) r w, r, max (u + 1) r w}
        (toCoefficientSections.{u, r, w} X Λ)) := by
    refine ⟨fun P hP ↦ ?_⟩
    apply Presheaf.isSheaf_of_isSheaf_comp (Scheme.ProEt.topology X)
      (P ⋙ ModuleCat.restrictScalars (toCoefficientSections.{u, r, w} X Λ))
      (forget₂ (ModuleCat.{max (u + 1) r w} Λ) AddCommGrpCat.{max (u + 1) r w})
    change Presheaf.IsSheaf (Scheme.ProEt.topology X)
      (P ⋙ forget₂ (ModuleCat.{max (u + 1) r w} _) AddCommGrpCat.{max (u + 1) r w})
    exact GrothendieckTopology.HasSheafCompose.isSheaf P hP
  exact SheafOfModules.forgetToSheafModuleCat
      ((Stacks.SheafOfModules.Tensor.ringSheaf (constantCoefficientRingedSite.{u, r, w} X Λ).O))
      (op (⊤_ X.ProEt)) (terminalIsTerminal (C := X.ProEt)).op ⋙
    sheafCompose (Scheme.ProEt.topology X)
      (ModuleCat.restrictScalars (toCoefficientSections.{u, r, w} X Λ))

variable (I : Ideal Λ)

/-- Reduction modulo `I` on constant coefficient ring sheaves. -/
abbrev constantCoefficientReduction :
    (constantCoefficientRingedSite.{u, r, w} X Λ).O ⟶
      (constantCoefficientRingedSite.{u, r, w} X (Λ ⧸ I)).O :=
  (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{max (u + 1) r w}).map
    (CommRingCat.ofHom
      ((ULift.ringEquiv.{r, max (u + 1) w} (R := Λ ⧸ I)).symm.toRingHom.comp
        ((Ideal.Quotient.mk I).comp (ULift.ringEquiv.{r, max (u + 1) w} (R := Λ)).toRingHom)))

/-- Reduction modulo `I` on the sheaves of rings underlying the constant coefficient ring
sheaves. -/
abbrev constantCoefficientRingReduction :
    (Stacks.SheafOfModules.Tensor.ringSheaf (constantCoefficientRingedSite.{u, r, w} X Λ).O) ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf (constantCoefficientRingedSite.{u, r, w} X (Λ ⧸ I)).O) :=
  (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{max (u + 1) r w} RingCat.{max (u + 1) r w})).map
      (constantCoefficientReduction.{u, r, w} X Λ I)

/-- The ideal sheaf `I·O` cut out by `I` in the constant coefficient ring sheaf: the
sectionwise kernel of reduction modulo `I`. -/
abbrev constantCoefficientIdealSheaf :=
  _root_.SheafOfModules.kerIdeal (constantCoefficientRingReduction.{u, r, w} X Λ I)

/-- A derived base change `- ⊗_Λ^L Λ/I` along reduction modulo `I`, in the sense of
Stacks 0DIZ: a left derived functor of degreewise extension of scalars along
`AlgebraicGeometry.ProEtale.constantCoefficientReduction`. Any two are canonically isomorphic,
so a condition stated against one is a condition against all. -/
abbrev DerivedReduction :=
  Deformation.ComplexLift.DerivedExtensionOfScalars.{max (u + 1) r w + 1,
    max (u + 1) r w + 1, u, max (u + 1) r w, u + 1}
    (constantCoefficientReduction.{u, r, w} X Λ I)

section Constructibility

variable [IsNoetherianRing Λ]

/-- Every cohomology sheaf of `K`, read as a sheaf of `Λ`-modules, is constructible in the
sense of Stacks 09AJ. -/
abbrev HasConstructibleCohomology (K : DerivedSheaves.{u, r, w} X Λ) : Prop :=
  ∀ i : ℤ, IsConstructibleModuleSheaf'.{u, r, max r w} X Λ
    ((toCoefficientModuleSheaf.{u, r, w} X Λ).obj
      ((DerivedCategory.homologyFunctor
        (RingedSite.Modules.{u + 1, u, max (u + 1) r w}
          (constantCoefficientRingedSite.{u, r, w} X Λ)) i).obj K))

variable
  [∀ U : (constantCoefficientRingedSite.{u, r, w} X (Λ ⧸ I)).C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r w, max (u + 1) r w, max (u + 1) r w}
      ((constantCoefficientRingedSite.{u, r, w} X (Λ ⧸ I)).over U).O).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, r, w} X (Λ ⧸ I)).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r w, max (u + 1) r w, max (u + 1) r w}
      ((constantCoefficientRingedSite.{u, r, w} X (Λ ⧸ I)).over U).O).obj M).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, r, w} X (Λ ⧸ I)).C)
    (K L : CochainComplex (RingedSite.Modules.{u + 1, u, max (u + 1) r w}
      ((constantCoefficientRingedSite.{u, r, w} X (Λ ⧸ I)).over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor
        ((constantCoefficientRingedSite.{u, r, w} X (Λ ⧸ I)).over U).O) (ComplexShape.up ℤ)]

/-- **Stacks 09C1.** An object `K` of `D(X_proét, Λ)` is *constructible* with respect to the
ideal `I` of the Noetherian coefficient ring `Λ` when it is derived complete along the ideal
sheaf cut out by `I`, and its derived reduction `K ⊗_Λ^L Λ/I`, formed with the derived base
change `T`, has constructible cohomology sheaves and locally has finite Tor dimension measured
against the derived tensor products `D` on the slices. -/
@[stacks 09C1 "constructible objects"]
abbrev IsConstructibleDerivedSheaf
    (T : DerivedReduction.{u, r, w} X Λ I)
    (D : ∀ U : (constantCoefficientRingedSite.{u, r, w} X (Λ ⧸ I)).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) r w,
          max (u + 1) r w + 1}
        ((constantCoefficientRingedSite.{u, r, w} X (Λ ⧸ I)).over U))
    (K : DerivedSheaves.{u, r, w} X Λ) : Prop :=
  RingedSite.IsDerivedComplete.{u + 1, u, max (u + 1) r w, max r w}
      (constantCoefficientRingedSite.{u, r, w} X Λ)
      (constantCoefficientIdealSheaf.{u, r, w} X Λ I) K ∧
    (HasConstructibleCohomology.{u, r, w} X (Λ ⧸ I) (T.baseChange.obj K) ∧
      Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension
        (X := constantCoefficientRingedSite.{u, r, w} X (Λ ⧸ I)) D (T.baseChange.obj K))

/-- **Stacks 09C1.** The full subcategory `D_cons(X, Λ)` of `D(X_proét, Λ)` on the
constructible objects. -/
@[stacks 09C1 "the full subcategory"]
abbrev constructibleDerivedSheaves
    (T : DerivedReduction.{u, r, w} X Λ I)
    (D : ∀ U : (constantCoefficientRingedSite.{u, r, w} X (Λ ⧸ I)).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) r w,
          max (u + 1) r w + 1}
        ((constantCoefficientRingedSite.{u, r, w} X (Λ ⧸ I)).over U)) :=
  ObjectProperty.FullSubcategory (IsConstructibleDerivedSheaf.{u, r, w} X Λ I T D)

end Constructibility

section AdicLisse

attribute [local instance] SheafOfModules.wEqualsLocallyBijective_commRingCat
  GrothendieckTopology.hasSheafify_addCommGrpCat
  SheafOfModules.wEqualsLocallyBijective_addCommGrpCat

/-- The comparison from the constant presheaf of coefficient rings on the small pro-étale site
to the presheaf of rings underlying the constant coefficient ring sheaf. -/
abbrev constantCoefficientRingMap :
    (Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ULift.{max (u + 1) w} Λ)) ⟶
      ((Stacks.SheafOfModules.Tensor.ringSheaf (constantCoefficientRingedSite.{u, r, w} X Λ).O)).obj :=
  Functor.whiskerRight (toSheafify (Scheme.ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{max (u + 1) w} Λ))))
      (forget₂ CommRingCat.{max (u + 1) r w} RingCat.{max (u + 1) r w})

instance constantCoefficientRingMap_isLocallyInjective :
    Presheaf.IsLocallyInjective (Scheme.ProEt.topology X)
      (constantCoefficientRingMap.{u, r, w} X Λ) := by
  apply (Presheaf.isLocallyInjective_forget_iff _ _).mp
  change Presheaf.IsLocallyInjective _ (Functor.whiskerRight (toSheafify _
    ((Functor.const _).obj (CommRingCat.of (ULift.{max (u + 1) w} Λ))))
      (forget CommRingCat))
  infer_instance

instance constantCoefficientRingMap_isLocallySurjective :
    Presheaf.IsLocallySurjective (Scheme.ProEt.topology X)
      (constantCoefficientRingMap.{u, r, w} X Λ) := by
  apply (Presheaf.isLocallySurjective_iff_whisker_forget _ _).mpr
  change Presheaf.IsLocallySurjective _ (Functor.whiskerRight (toSheafify _
    ((Functor.const _).obj (CommRingCat.of (ULift.{max (u + 1) w} Λ))))
      (forget CommRingCat))
  infer_instance

/-- A sheaf of `Λ`-modules on the small pro-étale site, read as a presheaf of modules over the
constant presheaf of coefficient rings: the scalars are restricted along `ULift.ringEquiv`. -/
def modulePresheafOverConstantCoefficientsFunctor :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) r w} Λ) ⥤
      PresheafOfModules.{max (u + 1) r w}
        ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ULift.{max (u + 1) w} Λ))) where
  obj F :=
    { obj := fun U => (ModuleCat.restrictScalars.{max (u + 1) r w}
        (ULift.ringEquiv.{r, max (u + 1) w} (R := Λ)).toRingHom).obj (F.obj.obj U)
      map := fun f => (ModuleCat.restrictScalars.{max (u + 1) r w}
        (ULift.ringEquiv.{r, max (u + 1) w} (R := Λ)).toRingHom).map (F.obj.map f)
      map_id := fun U => by ext x; exact congrArg (fun h => h x) (F.obj.map_id U)
      map_comp := fun f g => by ext x; exact congrArg (fun h => h x) (F.obj.map_comp f g) }
  map f :=
    { app := fun U => (ModuleCat.restrictScalars.{max (u + 1) r w}
        (ULift.ringEquiv.{r, max (u + 1) w} (R := Λ)).toRingHom).map (f.hom.app U)
      naturality := fun {U V} g => by ext x; exact congrArg (fun h => h x) (f.hom.naturality g) }
  map_id F := by ext U x; rfl
  map_comp f g := by ext U x; rfl

instance modulePresheafOverConstantCoefficientsFunctor_additive :
    (modulePresheafOverConstantCoefficientsFunctor.{u, r, w} X Λ).Additive where
  map_add := by intros; ext U x; rfl

/-- A sheaf of `Λ`-modules on the small pro-étale site, read as a sheaf of modules over the
constant coefficient ring sheaf. Sheafification extends the action of the constant sections to
the locally constant ones. -/
def moduleSheafOverConstantCoefficientsFunctor :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) r w} Λ) ⥤
      RingedSite.Modules.{u + 1, u, max (u + 1) r w}
        (constantCoefficientRingedSite.{u, r, w} X Λ) :=
  modulePresheafOverConstantCoefficientsFunctor.{u, r, w} X Λ ⋙
    PresheafOfModules.sheafification.{max (u + 1) r w}
      (constantCoefficientRingMap.{u, r, w} X Λ)

instance moduleSheafOverConstantCoefficientsFunctor_additive :
    (moduleSheafOverConstantCoefficientsFunctor.{u, r, w} X Λ).Additive := by
  let _ : (PresheafOfModules.sheafification.{max (u + 1) r w}
      (constantCoefficientRingMap.{u, r, w} X Λ)).Additive :=
    Functor.additive_of_preserves_binary_products _
  unfold moduleSheafOverConstantCoefficientsFunctor
  infer_instance

/-- The tower `n ↦ M/IⁿM` of adic quotients of a module, as a functor of the module. On objects
it is `AlgebraicGeometry.ProEtale.adicQuotientModuleSystem` and on morphisms it is reduction
modulo `Iⁿ`. -/
def adicQuotientModuleFunctor.{z, s} (Λ : Type s) [CommRing Λ] (I : Ideal Λ) :
    ModuleCat.{z} Λ ⥤ (ℕᵒᵖ ⥤ ModuleCat.{z} Λ) where
  obj M := adicQuotientModuleSystem Λ I M
  map {M N} f := NatTrans.ofOpSequence
    (fun n => ModuleCat.ofHom ((f.hom.reduceModIdeal (I ^ n)).restrictScalars Λ))
    (fun n => by
      simp only [adicQuotientModuleSystem, Functor.ofOpSequence_map_homOfLE_succ]
      ext x
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rfl)
  map_id M := by
    ext n x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  map_comp f g := by
    ext n x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl

instance adicQuotientModuleFunctor_additive.{z, s} (Λ : Type s) [CommRing Λ] (I : Ideal Λ) :
    (adicQuotientModuleFunctor.{z, s} Λ I).Additive where
  map_add {M N f g} := by
    ext n x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl

/-- The completed constant sheaf `\underline{M}^∧ = limₙ \underline{M/IⁿM}` of a coefficient
module, read as a sheaf of modules over the constant coefficient ring sheaf, functorially in
`M`. -/
def completedConstantCoefficientSheafFunctor :
    ModuleCat.{max (u + 1) r w} Λ ⥤
      RingedSite.Modules.{u + 1, u, max (u + 1) r w}
        (constantCoefficientRingedSite.{u, r, w} X Λ) :=
  adicQuotientModuleFunctor.{max (u + 1) r w, r} Λ I ⋙
    (Functor.whiskeringRight ℕᵒᵖ (ModuleCat.{max (u + 1) r w} Λ)
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) r w} Λ))).obj
      (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) r w} Λ)) ⋙
    lim ⋙ moduleSheafOverConstantCoefficientsFunctor.{u, r, w} X Λ

/-- The completed constant sheaf of coefficient modules is the completed constant sheaf of
Stacks 09BT, read over the constant coefficient ring sheaf. -/
theorem completedConstantCoefficientSheafFunctor_obj (M : ModuleCat.{max (u + 1) r w} Λ) :
    (completedConstantCoefficientSheafFunctor.{u, r, w} X Λ I).obj M =
      (moduleSheafOverConstantCoefficientsFunctor.{u, r, w} X Λ).obj
        (completedConstantSheaf.{u, r, max (u + 1) r w} X Λ I M) :=
  rfl

instance lim_additive :
    (lim (J := ℕᵒᵖ)
      (C := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) r w} Λ))).Additive :=
  Functor.additive_of_preserves_binary_products _

instance completedConstantCoefficientSheafFunctor_additive :
    (completedConstantCoefficientSheafFunctor.{u, r, w} X Λ I).Additive := by
  unfold completedConstantCoefficientSheafFunctor
  infer_instance

/-- Scalars of a coefficient module are restricted along `Λ → Λ^∧`. -/
abbrev restrictToCoefficients.{z, s} (Λ : Type s) [CommRing Λ] (I : Ideal Λ) :
    ModuleCat.{z} (AdicCompletion I Λ) ⥤ ModuleCat.{z} Λ :=
  ModuleCat.restrictScalars (algebraMap Λ (AdicCompletion I Λ))

/-- The complex `\underline{M^a}^∧ → ⋯ → \underline{M^b}^∧` of completed constant sheaves
attached to a complex `M^•` of `Λ^∧`-modules: the completed constant sheaf functor applied
degreewise, so that the differentials are those induced by the differentials of `M^•`. -/
abbrev completedConstantCoefficientComplex :
    CochainComplex (ModuleCat.{max (u + 1) r w} (AdicCompletion I Λ)) ℤ ⥤
      CochainComplex (RingedSite.Modules.{u + 1, u, max (u + 1) r w}
        (constantCoefficientRingedSite.{u, r, w} X Λ)) ℤ :=
  (restrictToCoefficients.{max (u + 1) r w, r} Λ I ⋙
    completedConstantCoefficientSheafFunctor.{u, r, w} X Λ I).mapHomologicalComplex
      (ComplexShape.up ℤ)

variable [∀ (Y : Scheme.{u}) (V : Y.ProEt),
  PreservesFiniteColimits (SheafOfModules.overFunctor.{max (u + 1) r w}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (constantCoefficientRingedSite.{u, r, w} Y Λ).O)) V)]

/-- Restriction of a complex of coefficient modules to an object of the small pro-étale site,
on unbounded derived categories. -/
abbrev overRestrictionDerived (V : X.ProEt) :
    DerivedSheaves.{u, r, w} X Λ ⥤
      DerivedCategory (SheafOfModules.{max (u + 1) r w}
        (((Stacks.SheafOfModules.Tensor.ringSheaf (constantCoefficientRingedSite.{u, r, w} X Λ).O)).over V)) :=
  letI : PreservesFiniteLimits (SheafOfModules.overFunctor.{max (u + 1) r w}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (constantCoefficientRingedSite.{u, r, w} X Λ).O)) V) :=
    SheafOfModules.preservesFiniteLimits_pushforward _
  (SheafOfModules.overFunctor.{max (u + 1) r w}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (constantCoefficientRingedSite.{u, r, w} X Λ).O)) V).mapDerivedCategory

/-- **Stacks 09C4, part (1).** An object `K` of `D(X_proét, Λ)` is *adic lisse* if there is a
finite complex `M^•` of finite projective `Λ^∧`-modules such that `K` is pro-étale locally
isomorphic to the complex `\underline{M^a}^∧ → ⋯ → \underline{M^b}^∧` of completed constant
sheaves, whose differentials are those induced by the differentials of `M^•`. -/
@[stacks 09C4 "part (1): adic lisse"]
abbrev IsAdicLisseDerivedSheaf (K : DerivedSheaves.{u, r, w} X Λ) : Prop :=
  ∃ (a b : ℤ) (M : CochainComplex (ModuleCat.{max (u + 1) r w} (AdicCompletion I Λ)) ℤ),
    M.IsStrictlyGE a ∧ M.IsStrictlyLE b ∧
    (∀ k : ℤ, Module.Finite (AdicCompletion I Λ) (M.X k) ∧
      Module.Projective (AdicCompletion I Λ) (M.X k)) ∧
    ∀ U : X.ProEt, ∃ (ι : Type (u + 1)) (V : ι → X.ProEt) (g : ∀ j, V j ⟶ U),
      Sieve.ofArrows V g ∈ Scheme.ProEt.topology X U ∧
      ∀ j, Nonempty ((overRestrictionDerived.{u, r, w} X Λ (V j)).obj K ≅
        (overRestrictionDerived.{u, r, w} X Λ (V j)).obj
          (DerivedCategory.Q.obj
            ((completedConstantCoefficientComplex.{u, r, w} X Λ I).obj M)))

section Restriction

variable {Z : Scheme.{u}} {X}

/-- The canonical comparison `\underline{Λ} ⟶ i_* \underline{Λ}` of constant coefficient ring
sheaves along a morphism of schemes, adjoint to the sheafification map of the constant presheaf
of coefficient rings on the source. -/
def constantCoefficientRingComparison (i : Z ⟶ X) :
    (constantCoefficientRingedSite.{u, r, w} X Λ).O ⟶
      ((Scheme.proetaleBaseChange i).sheafPushforwardContinuous
          CommRingCat.{max (u + 1) r w} (Scheme.ProEt.topology X)
          (Scheme.ProEt.topology Z)).obj
        (constantCoefficientRingedSite.{u, r, w} Z Λ).O :=
  ((sheafificationAdjunction (Scheme.ProEt.topology X)
      CommRingCat.{max (u + 1) r w}).homEquiv _ _).symm
    (Functor.whiskerLeft (Scheme.proetaleBaseChange i).op
      (toSheafify (Scheme.ProEt.topology Z)
        ((Functor.const Z.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{max (u + 1) w} Λ)))))

/-- The comparison of constant coefficient ring sheaves along a morphism of schemes, as a
morphism of sheaves of rings. -/
def coefficientRingComparison (i : Z ⟶ X) :
    (Stacks.SheafOfModules.Tensor.ringSheaf (constantCoefficientRingedSite.{u, r, w} X Λ).O) ⟶
      ((Scheme.proetaleBaseChange i).sheafPushforwardContinuous
          RingCat.{max (u + 1) r w} (Scheme.ProEt.topology X)
          (Scheme.ProEt.topology Z)).obj
        ((Stacks.SheafOfModules.Tensor.ringSheaf (constantCoefficientRingedSite.{u, r, w} Z Λ).O)) :=
  (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{max (u + 1) r w} RingCat.{max (u + 1) r w})).map
      (constantCoefficientRingComparison.{u, r, w} Λ i)

/-- Inverse image of sheaves of coefficient modules along a morphism of schemes, for the small
pro-étale sites, together with the exactness that induces it on unbounded derived categories.
The adjunction characterizes the functor as a left adjoint of the pushforward along
`AlgebraicGeometry.ProEtale.coefficientRingComparison`, hence determines it up to a unique
isomorphism. -/
structure CoefficientRestriction (i : Z ⟶ X) where
  /-- The inverse image of sheaves of coefficient modules. -/
  functor :
    RingedSite.Modules.{u + 1, u, max (u + 1) r w}
        (constantCoefficientRingedSite.{u, r, w} X Λ) ⥤
      RingedSite.Modules.{u + 1, u, max (u + 1) r w}
        (constantCoefficientRingedSite.{u, r, w} Z Λ)
  /-- The inverse image is additive. -/
  additive : functor.Additive
  /-- The inverse image is left exact. -/
  preservesFiniteLimits : PreservesFiniteLimits functor
  /-- The inverse image is right exact. -/
  preservesFiniteColimits : PreservesFiniteColimits functor
  /-- The inverse image is a left adjoint of the canonical pushforward. -/
  adj : functor ⊣ SheafOfModules.pushforward.{max (u + 1) r w}
    (coefficientRingComparison.{u, r, w} Λ i)

/-- The restriction `K ↦ K|_Z` on unbounded derived categories of sheaves of coefficient
modules, induced by an exact pro-étale inverse image. -/
abbrev CoefficientRestriction.derived {i : Z ⟶ X}
    (ρ : CoefficientRestriction.{u, r, w} Λ i) :
    DerivedSheaves.{u, r, w} X Λ ⥤ DerivedSheaves.{u, r, w} Z Λ :=
  letI := ρ.additive
  letI := ρ.preservesFiniteLimits
  letI := ρ.preservesFiniteColimits
  ρ.functor.mapDerivedCategory

end Restriction

/-- **Stacks 09C4, part (2).** An object `K` of `D(X_proét, Λ)` is *adic constructible* if every
affine open of `X` admits a decomposition into constructible locally closed subschemes on which
the restriction of `K` is adic lisse. -/
@[stacks 09C4 "part (2): adic constructible"]
abbrev IsAdicConstructibleDerivedSheaf (K : DerivedSheaves.{u, r, w} X Λ) : Prop :=
  ∀ U : X.affineOpens, ∃ s : Scheme.ConstructibleStratification X U.1,
    ∀ i, ∃ ρ : CoefficientRestriction.{u, r, w} Λ (s.inclusion i),
      IsAdicLisseDerivedSheaf.{u, r, w} (s.piece i) Λ I (ρ.derived.obj K)

end AdicLisse

end AlgebraicGeometry.ProEtale

end
