module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.DenseSubsite.OneHypercoverDense
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftFiniteColimits
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Size.SmallerUniverse
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Interface

/-!
# The small étale site as a ringed site, and exactness of the change of coefficients

Fix a coefficient ring `Λ` and a scheme `X` in a big étale site. The small étale site of `X`
together with the constant coefficient ring sheaf of Stacks 03TR is a ringed site, and reading
a sheaf of `Λ`-modules as a sheaf of modules over that ring sheaf is a functor between the two
abelian categories. This file makes that reading functorial and proves it exact.

Exactness is what lets the functor be applied degreewise to complexes and descend to unbounded
derived categories, which is how a constructible complex of `Λ`-modules is compared with the
Tor-amplitude notions of Stacks 08FZ, stated for a ringed site.

## Main definitions

* `AlgebraicGeometry.constantCoefficientRingedSite`: the small étale site of `X` with the
  constant coefficient ring sheaf as structure sheaf.
* `AlgebraicGeometry.modulePresheafOverConstantCoefficientsFunctor`: the functorial form of
  `AlgebraicGeometry.modulePresheafOverConstantCoefficients`.
* `AlgebraicGeometry.moduleSheafOverConstantCoefficientsFunctor`: the functorial form of
  `AlgebraicGeometry.moduleSheafOverConstantCoefficients`.

## Main results

* `AlgebraicGeometry.moduleSheafOverConstantCoefficientsFunctor_preservesFiniteLimits` and
  `AlgebraicGeometry.moduleSheafOverConstantCoefficientsFunctor_preservesFiniteColimits`: the
  change of coefficients is exact.

## Implementation notes

The universes of the scheme, of the module sections and of the coefficient ring are
independent; the construction lifts coefficients and sections into one universe containing all
three, as `AlgebraicGeometry.constantCoefficientSheaf` does.

Left exactness is checked objectwise: a limit of presheaves of modules is detected by the
evaluations, and evaluating the presheaf-level construction is a forgetful functor composed
with a `ULift` and a restriction of scalars along a ring equivalence, all of which are left
exact. Sheafification is left exact on the nose.

Right exactness is the substance. Sheafification of `AddCommGrpCat`-valued presheaves preserves
finite colimits when the site is essentially small *at the universe of the sections*, which no
hypothesis guarantees here: the module universe is unrelated to the scheme universe. The proof
therefore splits on whether every cardinal below the size cutoff of the ambient big étale site
has a representative small at the module universe.

* If it does, the objects of the small étale site whose underlying scheme is no larger than `X`
  form a subsite which is essentially small at the module universe — by
  `AlgebraicGeometry.essentiallySmall_schemeBelow_of_small_out` — and which is
  one-hypercover-dense, since every object is covered by the affine opens of its underlying
  scheme and those are no larger than `X` by Stacks 04T7. Sheafification transports along a
  dense subsite, so the colimit-preserving statement descends from the small model.
* If it does not, say for a cardinal `κ` below the cutoff, then every sheaf of `Λ`-modules on
  the small étale site is zero: above any object with a nonzero section module one can form the
  `κ`-fold disjoint union of that object, which is again an object of the site, and the `κ`
  many "indicator" amalgamations of the identity and zero over its tautological covering are
  pairwise distinct, so the module of sections would contain a copy of `κ`. A functor out of a
  category with only zero objects preserves everything.

## References

* [Stacks Project, Tag 03TR](https://stacks.math.columbia.edu/tag/03TR)
* [Stacks Project, Tag 04T7](https://stacks.math.columbia.edu/tag/04T7)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w r

namespace AlgebraicGeometry

attribute [local instance] GrothendieckTopology.hasSheafify_addCommGrpCat
  SheafOfModules.wEqualsLocallyBijective_addCommGrpCat

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ]

/-- The small étale site of `X`, ringed by the constant coefficient ring sheaf of
Stacks 03TR. -/
abbrev constantCoefficientRingedSite : RingedSite.{u + 1, u, max (u + 1) w r} where
  C := SmallEtale B X.obj X.property
  J := SmallEtale.topology B X.obj X.property
  O := constantCoefficientSheaf.{u, w, r} B X Λ

/-- The functorial form of `AlgebraicGeometry.modulePresheafOverConstantCoefficients`: a
morphism of sheaves of `Λ`-modules is lifted and read as a morphism of presheaves of modules
over the constant presheaf of rings. -/
@[implicit_reducible]
def modulePresheafOverConstantCoefficientsFunctor :
    Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ) ⥤
      PresheafOfModules.{max (u + 1) w r}
        ((Functor.const (SmallEtale B X.obj X.property)ᵒᵖ).obj
          (RingCat.of (ULift.{max (u + 1) w} Λ))) where
  obj := modulePresheafOverConstantCoefficients B X Λ
  map f :=
    { app := fun U =>
        (ModuleCat.restrictScalars
          (ULift.ringEquiv.{r, max (u + 1) w} (R := Λ)).toRingHom).map
            ((ModuleCat.uliftFunctor.{max (u + 1) r} Λ).map (f.hom.app U))
      naturality := fun {U V} g => by
        ext x
        exact congrArg (fun h => ULift.up (h x.down)) (f.hom.naturality g) }
  map_id F := by ext U x; rfl
  map_comp f g := by ext U x; rfl

/-- The functorial form of the constant-coefficient module presheaf agrees objectwise with
`AlgebraicGeometry.modulePresheafOverConstantCoefficients`. -/
@[simp]
theorem modulePresheafOverConstantCoefficientsFunctor_obj
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)) :
    (modulePresheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).obj F =
      modulePresheafOverConstantCoefficients B X Λ F :=
  rfl

/-- The presheaf-level change of coefficients is an additive functor. -/
instance modulePresheafOverConstantCoefficientsFunctor_additive :
    (modulePresheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).Additive where
  map_add := by intros; ext U x; rfl

/-- The presheaf-level change of coefficients preserves finite limits, because it does so after
evaluation at every object of the site and limits of presheaves of modules are detected by the
evaluations. -/
private lemma modulePresheafOverConstantCoefficientsFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (modulePresheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ) := by
  let H : ModuleCat.{w} Λ ⥤ ModuleCat.{max (u + 1) w r} (ULift.{max (u + 1) w} Λ) :=
    ModuleCat.uliftFunctor.{max (u + 1) r} Λ ⋙
      ModuleCat.restrictScalars.{max (u + 1) w r}
        (ULift.ringEquiv.{r, max (u + 1) w} (R := Λ)).toRingHom
  have hEval (U : (SmallEtale B X.obj X.property)ᵒᵖ) :
      PreservesFiniteLimits
        (modulePresheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ ⋙
          PresheafOfModules.evaluation
            ((Functor.const (SmallEtale B X.obj X.property)ᵒᵖ).obj
              (RingCat.of (ULift.{max (u + 1) w} Λ))) U) := by
    show PreservesFiniteLimits
      (sheafToPresheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ) ⋙
        (evaluation (SmallEtale B X.obj X.property)ᵒᵖ (ModuleCat.{w} Λ)).obj U ⋙ H)
    infer_instance
  refine ⟨fun J => ⟨fun {F} => ⟨fun {c} hc => ?_⟩⟩⟩
  refine ⟨PresheafOfModules.evaluationJointlyReflectsLimits
    (R := (Functor.const (SmallEtale B X.obj X.property)ᵒᵖ).obj
      (RingCat.of (ULift.{max (u + 1) w} Λ)))
    (F ⋙ modulePresheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ)
    (Functor.mapCone (modulePresheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ) c) ?_⟩
  intro U
  let := hEval U
  exact isLimitOfPreserves
    (modulePresheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ ⋙
      PresheafOfModules.evaluation
        ((Functor.const (SmallEtale B X.obj X.property)ᵒᵖ).obj
          (RingCat.of (ULift.{max (u + 1) w} Λ))) U) hc

/-- The functorial form of `AlgebraicGeometry.moduleSheafOverConstantCoefficients`: a sheaf of
`Λ`-modules on the small étale site, read as a sheaf of modules over the constant coefficient
ring sheaf. Sheafification extends the action of the constant sections to the locally constant
ones. -/
@[implicit_reducible]
def moduleSheafOverConstantCoefficientsFunctor :
    Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ) ⥤
      RingedSite.Modules.{u + 1, u, max (u + 1) w r}
        (constantCoefficientRingedSite.{u, w, r} B X Λ) := by
  letI : Presheaf.IsLocallyInjective (constantCoefficientRingedSite.{u, w, r} B X Λ).J
      (F₂ := (Stacks.SheafOfModules.Tensor.ringSheaf
        (constantCoefficientRingedSite.{u, w, r} B X Λ).O).obj)
      (constantCoefficientRingMap.{u, w, r} B X Λ) :=
    constantCoefficientRingMap_isLocallyInjective B X Λ
  letI : Presheaf.IsLocallySurjective (constantCoefficientRingedSite.{u, w, r} B X Λ).J
      (G := (Stacks.SheafOfModules.Tensor.ringSheaf
        (constantCoefficientRingedSite.{u, w, r} B X Λ).O).obj)
      (constantCoefficientRingMap.{u, w, r} B X Λ) :=
    constantCoefficientRingMap_isLocallySurjective B X Λ
  exact modulePresheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ ⋙
    PresheafOfModules.sheafification.{max (u + 1) w r}
      (R := Stacks.SheafOfModules.Tensor.ringSheaf
        (constantCoefficientRingedSite.{u, w, r} B X Λ).O)
      (constantCoefficientRingMap.{u, w, r} B X Λ)

/-- The functorial change of coefficients agrees objectwise with
`AlgebraicGeometry.moduleSheafOverConstantCoefficients`. -/
@[simp]
theorem moduleSheafOverConstantCoefficientsFunctor_obj
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)) :
    (moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).obj F =
      moduleSheafOverConstantCoefficients B X Λ F :=
  rfl

/-- The change of coefficients is an additive functor. -/
instance moduleSheafOverConstantCoefficientsFunctor_additive :
    (moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).Additive := by
  let : (PresheafOfModules.sheafification.{max (u + 1) w r}
      (constantCoefficientRingMap.{u, w, r} B X Λ)).Additive :=
    Functor.additive_of_preserves_binary_products _
  change (modulePresheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ ⋙
    PresheafOfModules.sheafification (constantCoefficientRingMap.{u, w, r} B X Λ)).Additive
  exact CategoryTheory.Functor.instAdditiveComp _ _

/-- **The change of coefficients is left exact.** -/
instance moduleSheafOverConstantCoefficientsFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ) := by
  change PreservesFiniteLimits
    (modulePresheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ ⋙
      PresheafOfModules.sheafification (constantCoefficientRingMap.{u, w, r} B X Λ))
  let _ := modulePresheafOverConstantCoefficientsFunctor_preservesFiniteLimits.{u, w, r} B X Λ
  infer_instance

/-! ### Right exactness -/

/-- Composing with a right-exact functor and sheafifying preserves finite colimits, when the
composition is compatible with sheafification. -/
private lemma composeAndSheafify_preservesFiniteColimits
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    {A : Type*} [Category A] {D : Type*} [Category D]
    [HasWeakSheafify J A] [HasWeakSheafify J D]
    (F : A ⥤ D) [HasFiniteColimits A] [PreservesFiniteColimits F]
    [J.PreservesSheafification F] :
    PreservesFiniteColimits (Sheaf.composeAndSheafify J F) := by
  let _ : PreservesFiniteColimits ((Functor.whiskeringRight Cᵒᵖ A D).obj F) :=
    ⟨fun shape => ⟨fun {diagram} => inferInstance⟩⟩
  let _ : PreservesFiniteColimits (presheafToSheaf J A ⋙ Sheaf.composeAndSheafify J F) :=
    preservesFiniteColimits_of_natIso
      (presheafToSheafCompComposeAndSheafifyIso J F).symm
  exact Stacks.SheafOfModules.preservesFiniteColimits_of_reflector (sheafificationAdjunction J A) _

/-- A sheaf of `Λ`-modules, read as a sheaf of abelian groups in the ambient universe. -/
private def moduleToLiftedAddCommGrp : ModuleCat.{w} Λ ⥤ AddCommGrpCat.{max (u + 1) w r} :=
  forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w} ⋙ AddCommGrpCat.uliftFunctor.{max (u + 1) r}

/-- The composite of the change of coefficients with the forgetful functor to sheaves of
abelian groups, presented as a sheafified composition. -/
private def moduleSheafToLiftedAddCommGrp :
    Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ) ⥤
      Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) w r} :=
  Sheaf.composeAndSheafify (SmallEtale.topology B X.obj X.property)
    (moduleToLiftedAddCommGrp.{u, w, r} Λ)

/-- The two presentations of the underlying sheaf of abelian groups of the change of
coefficients agree. -/
private def moduleSheafToLiftedAddCommGrpIso :
    moduleSheafToLiftedAddCommGrp.{u, w, r} B X Λ ≅
      moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ ⋙
        SheafOfModules.toSheaf
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (constantCoefficientRingedSite.{u, w, r} B X Λ).O) :=
  Iso.refl _

/-- The change of coefficients is right exact as soon as sheafification of
`AddCommGrpCat`-valued presheaves on the small étale site commutes with the lifted forgetful
functor of `ModuleCat.{w} Λ`. -/
private lemma moduleSheafOverConstantCoefficientsFunctor_preservesFiniteColimits_of_sheafification
    [HasWeakSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)]
    [(SmallEtale.topology B X.obj X.property).PreservesSheafification
      (moduleToLiftedAddCommGrp.{u, w, r} Λ)] :
    PreservesFiniteColimits (moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ) := by
  let _ : PreservesFiniteColimits (moduleSheafToLiftedAddCommGrp.{u, w, r} B X Λ) := by
    unfold moduleSheafToLiftedAddCommGrp
    let _ : PreservesFiniteColimits (moduleToLiftedAddCommGrp.{u, w, r} Λ) := by
      unfold moduleToLiftedAddCommGrp
      let _ : PreservesFiniteColimits (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) :=
        ⟨fun shape => ⟨fun {diagram} => inferInstance⟩⟩
      exact ⟨fun shape => ⟨fun {diagram} => inferInstance⟩⟩
    apply composeAndSheafify_preservesFiniteColimits
  let _ : PreservesFiniteColimits
      (moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ ⋙
        SheafOfModules.toSheaf.{max (u + 1) w r}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (constantCoefficientRingedSite.{u, w, r} B X Λ).O)) :=
    preservesFiniteColimits_of_natIso (moduleSheafToLiftedAddCommGrpIso.{u, w, r} B X Λ)
  let _ : PreservesFiniteColimits (SheafOfModules.toSheaf.{max (u + 1) w r}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (constantCoefficientRingedSite.{u, w, r} B X Λ).O)) :=
    Stacks.SheafOfModules.toSheaf_preservesFiniteColimits.{max (u + 1) w r} _
  let _ : ReflectsFiniteColimits (SheafOfModules.toSheaf.{max (u + 1) w r}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (constantCoefficientRingedSite.{u, w, r} B X Λ).O)) :=
    { reflects := fun shape =>
        ⟨fun {diagram} => reflectsColimit_of_reflectsIsomorphisms _ _⟩ }
  exact preservesFiniteColimits_of_reflects_of_preserves _
    (SheafOfModules.toSheaf.{max (u + 1) w r}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (constantCoefficientRingedSite.{u, w, r} B X Λ).O))

/-- The forgetful functor from `ModuleCat.{w} Λ` preserves filtered colimits. -/
private lemma preservesFilteredColimits_forget_moduleCat :
    PreservesFilteredColimitsOfSize.{w, w} (forget (ModuleCat.{w} Λ)) := by
  let _ : PreservesColimitsOfSize.{w, w} (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{w, r, w, w} Λ
  change PreservesFilteredColimitsOfSize
    (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w} ⋙ forget AddCommGrpCat.{w})
  infer_instance

/-- Modules in universe `w` have sheafification on any site essentially small at that universe. -/
private lemma hasSheafify_moduleCat_of_essentiallySmall {C : Type (u + 1)} [Category.{u} C]
    [EssentiallySmall.{w} C] (J : GrothendieckTopology C) :
    HasSheafify J (ModuleCat.{w} Λ) := by
  let _ := preservesFilteredColimits_forget_moduleCat.{w, r} Λ
  exact hasSheafifyEssentiallySmallSite.{u, w, u + 1, max r (w + 1), w} J _

/-- Sheafification on a site essentially small at the module universe commutes with the lifted
forgetful functor of `ModuleCat.{w} Λ`. -/
private lemma preservesSheafification_moduleToLiftedAddCommGrp {C : Type (u + 1)}
    [Category.{u} C] [EssentiallySmall.{w} C] (J : GrothendieckTopology C) :
    J.PreservesSheafification (moduleToLiftedAddCommGrp.{u, w, r} Λ) := by
  let _ := hasSheafify_moduleCat_of_essentiallySmall.{u, w, r} Λ J
  let _ := preservesFilteredColimits_forget_moduleCat.{w, r} Λ
  let _ : PreservesFilteredColimitsOfSize.{w, w} (forget AddCommGrpCat.{max (u + 1) w r}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max (u + 1) w r, max (u + 1) w r, w, w} _
  let _ : ∀ U : Cᵒᵖ, HasLimitsOfShape (StructuredArrow U (equivSmallModel.{w} C).inverse.op)
      (ModuleCat.{w} Λ) := fun _ =>
    hasLimitsOfShape_of_essentiallySmall.{w, w, w, max r (w + 1), max u w} _ _
  let smallTopology := (equivSmallModel.{w} C).inverse.inducedTopology J
  let _ : smallTopology.PreservesSheafification (moduleToLiftedAddCommGrp.{u, w, r} Λ) := by
    unfold moduleToLiftedAddCommGrp
    let _ : PreservesColimitsOfSize.{w, w}
        (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w} ⋙
          AddCommGrpCat.uliftFunctor.{max (u + 1) r}) :=
      ⟨fun {shape} => ⟨fun {diagram} => inferInstance⟩⟩
    exact GrothendieckTopology.instPreservesSheafification smallTopology _
  exact GrothendieckTopology.PreservesSheafification.transport J smallTopology
    (equivSmallModel.{w} C).inverse AddCommGrpCat.{max (u + 1) w r} _

/-- The change of coefficients is right exact when the small étale site is essentially small at
the universe of the module sections. -/
private lemma moduleSheafOverConstantCoefficientsFunctor_preservesFiniteColimits_of_essentiallySmall
    [EssentiallySmall.{w} (SmallEtale B X.obj X.property)] :
    PreservesFiniteColimits (moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ) := by
  let _ := hasSheafify_moduleCat_of_essentiallySmall.{u, w, r} Λ
    (SmallEtale.topology B X.obj X.property)
  let _ := preservesSheafification_moduleToLiftedAddCommGrp.{u, w, r} Λ
    (SmallEtale.topology B X.obj X.property)
  exact moduleSheafOverConstantCoefficientsFunctor_preservesFiniteColimits_of_sheafification.{u,
    w, r} B X Λ

/-! #### The subsite of objects no larger than the base -/

/-- The objects of the small étale site of `X` whose underlying scheme is no larger than `X`
itself. -/
private def boundedByBase : ObjectProperty (SmallEtale B X.obj X.property) :=
  fun T => ((SmallEtale.toScheme B X.obj X.property).obj T).size ≤ X.obj.size

/-- The subsite of objects no larger than the base is essentially small at any universe at
which the size of the base has a small representative. -/
private lemma boundedByBase_essentiallySmall [Small.{w} X.obj.size.out] :
    EssentiallySmall.{w} (boundedByBase B X).FullSubcategory := by
  classical
  let bound := Cardinal.mk (Set X.obj.size.out)
  let _ : Small.{w} bound.out := small_out_cardinalMk (Set X.obj.size.out)
  have size_lt : X.obj.size < bound := by
    simpa only [bound, Cardinal.mk_set, Cardinal.mk_out] using Cardinal.cantor X.obj.size
  let base : SchemeBelow bound := ⟨X.obj, size_lt⟩
  let _ : EssentiallySmall.{w} (SchemeBelow bound) :=
    essentiallySmall_schemeBelow_of_small_out bound
  let _ : LocallySmall.{w} (SchemeBelow bound) := locallySmall_schemeBelow bound
  let _ : EssentiallySmall.{w} (Over base) := by
    show EssentiallySmall.{w} (CostructuredArrow (𝟭 (SchemeBelow bound)) base)
    infer_instance
  let comparison : (boundedByBase B X).FullSubcategory ⥤ Over base :=
    { obj := fun T => Over.mk
        (ObjectProperty.homMk T.obj.obj.hom.hom :
          (⟨T.obj.obj.left.obj, T.property.trans_lt size_lt⟩ : SchemeBelow bound) ⟶ base)
      map := fun f => Over.homMk
        (ObjectProperty.homMk f.hom.hom.left.hom) (by
          apply ObjectProperty.hom_ext
          exact congrArg (fun k => k.hom) (Over.w f.hom.hom)) }
  let _ : comparison.Full := by
    constructor
    intro T T' f
    refine ⟨ObjectProperty.homMk (ObjectProperty.homMk
      (Over.homMk (ObjectProperty.homMk f.left.hom) ?_)), ?_⟩
    · apply ObjectProperty.hom_ext
      exact congrArg (fun k => k.hom) (Over.w f)
    · apply Over.OverMorphism.ext
      rfl
  let _ : comparison.Faithful := by
    constructor
    intro T T' f g h
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact congrArg (fun k => k.left.hom) h
  exact essentiallySmall_of_fully_faithful comparison

/-- An affine open of the underlying scheme of an object of the small étale site, as an object
no larger than the base: it is of finite type over `X`, so Stacks 04T7 bounds its size. -/
private def affineCoverObj (T : SmallEtale B X.obj X.property)
    (i : ((SmallEtale.toScheme B X.obj X.property).obj T).affineCover.I₀) :
    (boundedByBase B X).FullSubcategory :=
  let S := (SmallEtale.toScheme B X.obj X.property).obj T
  let structureMap := S.affineCover.f i ≫ B.inclusion.map T.obj.hom
  have _ : Etale (B.inclusion.map T.obj.hom) := Stacks.EtaleCohomology.etale_hom B X.property T
  have bound : (S.affineCover.X i).size ≤ X.obj.size :=
    Scheme.size_le_of_locallyOfFiniteType structureMap
  ⟨Stacks.EtaleCohomology.mkObj B X.property (S.affineCover.X i) structureMap
    (bound.trans_lt X.property) inferInstance, bound⟩

/-- The structure morphism of an affine open of the underlying scheme of an object, as a
morphism of the small étale site. -/
private def affineCoverHom (T : SmallEtale B X.obj X.property)
    (i : ((SmallEtale.toScheme B X.obj X.property).obj T).affineCover.I₀) :
    (affineCoverObj B X T i).obj ⟶ T :=
  Stacks.EtaleCohomology.mkHom B X.property
    (((SmallEtale.toScheme B X.obj X.property).obj T).affineCover.f i) rfl

/-- The affine opens of the underlying scheme of an object cover it. -/
private lemma affineCover_mem_topology (T : SmallEtale B X.obj X.property) :
    Sieve.ofArrows _ (affineCoverHom B X T) ∈ SmallEtale.topology B X.obj X.property T :=
  Stacks.EtaleCohomology.ofArrows_mem_topology B X.property _ _ fun x =>
    ((SmallEtale.toScheme B X.obj X.property).obj T).affineCover.exists_eq x

/-- The subsite of objects no larger than the base is cover dense. -/
private lemma boundedByBase_coverDense :
    (boundedByBase B X).ι.IsCoverDense (SmallEtale.topology B X.obj X.property) := by
  constructor
  intro T
  apply (SmallEtale.topology B X.obj X.property).superset_covering _
    (affineCover_mem_topology B X T)
  rintro S f ⟨M, a, b, ⟨i⟩, hf⟩
  exact ⟨⟨affineCoverObj B X T i, a, affineCoverHom B X T i, hf⟩⟩

/-- The subsite of objects no larger than the base is one-hypercover dense, at any universe at
which every cardinal below the cutoff of the ambient big étale site has a small
representative. -/
private lemma boundedByBase_oneHypercoverDense
    (hsmall : ∀ κ : Cardinal.{u}, κ < B.cutoff → Small.{w} κ.out) :
    (boundedByBase B X).ι.IsOneHypercoverDense.{w}
      ((boundedByBase B X).ι.inducedTopology (SmallEtale.topology B X.obj X.property))
      (SmallEtale.topology B X.obj X.property) := by
  classical
  let _ : (boundedByBase B X).ι.IsCoverDense (SmallEtale.topology B X.obj X.property) :=
    boundedByBase_coverDense B X
  apply Functor.IsOneHypercoverDense.of_hasPullbacks
  intro T
  let S := (SmallEtale.toScheme B X.obj X.property).obj T
  let _ : Small.{w} S.size.out := hsmall S.size T.obj.left.property
  let _ : Small.{w} S := S.small_of_size_le S.size le_rfl
  let _ : Small.{w} S.affineCover.I₀ := inferInstanceAs (Small.{w} S)
  let e := equivShrink.{w} S.affineCover.I₀
  refine ⟨Shrink.{w} S.affineCover.I₀, fun i => affineCoverObj B X T (e.symm i),
    fun i => affineCoverHom B X T (e.symm i), ?_⟩
  have hequal : Sieve.ofArrows _ (fun i => affineCoverHom B X T (e.symm i)) =
      Sieve.ofArrows _ (affineCoverHom B X T) := by
    apply le_antisymm <;> rw [Sieve.generate_le_iff]
    · rintro S' f ⟨i⟩
      exact Sieve.ofArrows_mk _ _ (e.symm i)
    · rintro S' f ⟨i⟩
      have hmem := Sieve.ofArrows_mk
        (fun i => (affineCoverObj B X T (e.symm i)).obj)
        (fun i => affineCoverHom B X T (e.symm i)) (e i)
      rwa [e.symm_apply_apply i] at hmem
  show Sieve.ofArrows _ (fun i => affineCoverHom B X T (e.symm i)) ∈ _
  rw [hequal]
  exact affineCover_mem_topology B X T

/-- **The change of coefficients is right exact** when every cardinal below the cutoff of the
ambient big étale site has a representative small at the universe of the module sections: the
subsite of objects no larger than the base is then a small dense subsite, along which
sheafification transports. -/
private lemma moduleSheafOverConstantCoefficientsFunctor_preservesFiniteColimits_of_small_sizes
    (hsmall : ∀ κ : Cardinal.{u}, κ < B.cutoff → Small.{w} κ.out) :
    PreservesFiniteColimits (moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ) := by
  let inclusion := (boundedByBase B X).ι
  let topology := inclusion.inducedTopology (SmallEtale.topology B X.obj X.property)
  let _ : Small.{w} X.obj.size.out := hsmall X.obj.size X.property
  have := boundedByBase_essentiallySmall B X
  have := boundedByBase_coverDense B X
  let _ : inclusion.IsOneHypercoverDense.{w} topology
      (SmallEtale.topology B X.obj X.property) :=
    boundedByBase_oneHypercoverDense B X hsmall
  let _ : (inclusion.sheafPushforwardContinuous (ModuleCat.{w} Λ) topology
      (SmallEtale.topology B X.obj X.property)).IsEquivalence :=
    Functor.isEquivalence_of_isOneHypercoverDense.{w} inclusion topology
      (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)
  let _ : (inclusion.sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) w r} topology
      (SmallEtale.topology B X.obj X.property)).IsEquivalence :=
    Functor.isEquivalence_of_isOneHypercoverDense.{w} inclusion topology
      (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) w r}
  let _ := hasSheafify_moduleCat_of_essentiallySmall.{u, w, r} Λ topology
  let _ : HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ) :=
    Functor.IsDenseSubsite.hasSheafify_of_isEquivalence topology
      (SmallEtale.topology B X.obj X.property) inclusion
  let _ := preservesSheafification_moduleToLiftedAddCommGrp.{u, w, r} Λ topology
  let _ : (SmallEtale.topology B X.obj X.property).PreservesSheafification
      (moduleToLiftedAddCommGrp.{u, w, r} Λ) :=
    GrothendieckTopology.PreservesSheafification.transport
      (SmallEtale.topology B X.obj X.property) topology inclusion
        AddCommGrpCat.{max (u + 1) w r} _
  exact moduleSheafOverConstantCoefficientsFunctor_preservesFiniteColimits_of_sheafification
    B X Λ

/-! #### The degenerate case -/

/-- A sheaf of modules on the small étale site vanishes on an object with empty underlying
scheme, that object being covered by the empty family. -/
private lemma moduleSheaf_isZero_obj_of_isEmpty
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ))
    (T : SmallEtale B X.obj X.property)
    [IsEmpty ((SmallEtale.toScheme B X.obj X.property).obj T)] :
    IsZero (F.obj.obj (op T)) := by
  let arrows : ∀ i : Empty, T ⟶ T := fun i => nomatch i
  have covering : Sieve.ofArrows (fun _ : Empty => T) arrows ∈
      SmallEtale.topology B X.obj X.property T :=
    Stacks.EtaleCohomology.ofArrows_mem_topology B X.property _ _ fun x => isEmptyElim x
  exact (IsZero.iff_id_eq_zero _).mpr
    (F.property.hom_ext_ofArrows arrows covering fun i => nomatch i)

/-- The `κ`-fold disjoint union of an object of the small étale site, again an object of the
site as soon as `κ` is below the cutoff. -/
private def coproductObj (κ : Cardinal.{u}) (hκ : κ < B.cutoff)
    (T : SmallEtale B X.obj X.property) : SmallEtale B X.obj X.property :=
  have hS : Etale (B.inclusion.map T.obj.hom) := Stacks.EtaleCohomology.etale_hom B X.property T
  have _ : IsZariskiLocalAtSource @Etale :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Etale)
  have bound : (∐ fun _ : κ.out =>
      (SmallEtale.toScheme B X.obj X.property).obj T).size < B.cutoff := by
    refine (schemeSize_coproduct_le _
      (max κ ((SmallEtale.toScheme B X.obj X.property).obj T).size)
      (((SmallEtale.toScheme B X.obj X.property).obj T).aleph0_le_size.trans
        (le_max_right _ _))
      (by simpa only [Cardinal.mk_out] using
        le_max_left κ ((SmallEtale.toScheme B X.obj X.property).obj T).size)
      (fun _ => le_max_right _ _)).trans_lt ?_
    exact max_lt hκ T.obj.left.property
  Stacks.EtaleCohomology.mkObj B X.property
    (∐ fun _ : κ.out => (SmallEtale.toScheme B X.obj X.property).obj T)
    (Sigma.desc fun _ => B.inclusion.map T.obj.hom) bound
    (IsZariskiLocalAtSource.sigmaDesc (P := @Etale) fun _ => hS)

/-- The `κ` tautological inclusions of an object into its `κ`-fold disjoint union. -/
private def coproductHom (κ : Cardinal.{u}) (hκ : κ < B.cutoff)
    (T : SmallEtale B X.obj X.property) (i : κ.out) : T ⟶ coproductObj B X κ hκ T :=
  Stacks.EtaleCohomology.mkHom B X.property
    (Sigma.ι (fun _ : κ.out => (SmallEtale.toScheme B X.obj X.property).obj T) i)
    (Sigma.ι_desc _ i)

/-- The tautological inclusions cover the disjoint union. -/
private lemma coproduct_mem_topology (κ : Cardinal.{u}) (hκ : κ < B.cutoff)
    (T : SmallEtale B X.obj X.property) :
    Sieve.ofArrows _ (coproductHom B X κ hκ T) ∈
      SmallEtale.topology B X.obj X.property (coproductObj B X κ hκ T) :=
  Stacks.EtaleCohomology.ofArrows_mem_topology B X.property _ _ fun x =>
    (sigmaOpenCover
      (fun _ : κ.out => (SmallEtale.toScheme B X.obj X.property).obj T)).exists_eq x

/-- Any family of sections indexed by the tautological covering of the disjoint union is
compatible: two distinct inclusions have empty intersection, and a sheaf of modules vanishes
there. -/
private lemma coproductHom_compatible (κ : Cardinal.{u}) (hκ : κ < B.cutoff)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ))
    (T : SmallEtale B X.obj X.property) {M : ModuleCat.{w} Λ}
    (s : κ.out → (M ⟶ F.obj.obj (op T)))
    {Z : SmallEtale B X.obj X.property} {i j : κ.out} (a : Z ⟶ T) (b : Z ⟶ T)
    (hab : a ≫ coproductHom B X κ hκ T i = b ≫ coproductHom B X κ hκ T j) :
    s i ≫ F.obj.map a.op = s j ≫ F.obj.map b.op := by
  classical
  by_cases hij : i = j
  · subst hij
    have hunderlying : (SmallEtale.toScheme B X.obj X.property).map a =
        (SmallEtale.toScheme B X.obj X.property).map b := by
      apply (cancel_mono (Sigma.ι
        (fun _ : κ.out => (SmallEtale.toScheme B X.obj X.property).obj T) i)).mp
      exact congrArg (SmallEtale.toScheme B X.obj X.property).map hab
    rw [Stacks.EtaleCohomology.hom_ext B X.property hunderlying]
  · let _ : IsEmpty ((SmallEtale.toScheme B X.obj X.property).obj Z) :=
      isEmpty_of_commSq_sigmaι_of_ne
        (g := fun _ : κ.out => (SmallEtale.toScheme B X.obj X.property).obj T)
        ⟨congrArg (SmallEtale.toScheme B X.obj X.property).map hab⟩ hij
    exact (moduleSheaf_isZero_obj_of_isEmpty B X Λ F Z).eq_of_tgt _ _

/-- The morphisms between two modules in universe `w` form a `w`-small type. -/
private lemma small_moduleHom (M N : ModuleCat.{w} Λ) : Small.{w} (M ⟶ N) :=
  small_of_injective (f := fun φ : M ⟶ N => φ.hom.toFun)
    (fun _ _ h => ModuleCat.hom_ext (LinearMap.ext (congrFun h)))

/-- **Every sheaf of `Λ`-modules on the small étale site is zero** when some cardinal below the
cutoff of the ambient big étale site fails to be small at the universe of the module sections.
Above an object with a nonzero module of sections, the indicator amalgamations over the
tautological covering of the `κ`-fold disjoint union are pairwise distinct, embedding `κ` into
a module of homomorphisms. -/
private lemma moduleSheaf_isZero_of_nonsmall_cardinal
    (κ : Cardinal.{u}) (hκ : κ < B.cutoff) (hnot : ¬ Small.{w} κ.out)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)) : IsZero F := by
  classical
  have hzero (T : SmallEtale B X.obj X.property) : IsZero (F.obj.obj (op T)) := by
    by_contra hne
    have hid : (𝟙 (F.obj.obj (op T))) ≠ 0 := fun h => hne ((IsZero.iff_id_eq_zero _).mpr h)
    let s : κ.out → (F.obj.obj (op T) ⟶ F.obj.obj (op (coproductObj B X κ hκ T))) :=
      fun i => F.property.amalgamateOfArrows (coproductHom B X κ hκ T)
        (coproduct_mem_topology B X κ hκ T)
        (fun j => if j = i then 𝟙 _ else 0)
        (fun {Z j j'} a b hab => coproductHom_compatible B X Λ κ hκ F T
          (fun j => if j = i then 𝟙 _ else 0) a b hab)
    have hrestrict (i j : κ.out) :
        s i ≫ F.obj.map (coproductHom B X κ hκ T j).op = if j = i then 𝟙 _ else 0 :=
      F.property.amalgamateOfArrows_map _ _ _ _ j
    have hinj : Function.Injective s := by
      intro i j hij
      by_contra hne'
      have hcontra := congrArg
        (fun φ => φ ≫ F.obj.map (coproductHom B X κ hκ T i).op) hij
      rw [hrestrict, hrestrict, ite_eq_left rfl, ite_eq_right hne'] at hcontra
      exact hid hcontra
    let _ : Small.{w}
        (F.obj.obj (op T) ⟶ F.obj.obj (op (coproductObj B X κ hκ T))) :=
      small_moduleHom Λ _ _
    exact hnot (small_of_injective hinj)
  apply (IsZero.iff_id_eq_zero _).mpr
  apply Sheaf.hom_ext
  ext T x
  exact ConcreteCategory.congr_hom ((IsZero.iff_id_eq_zero _).mp (hzero T.unop)) x

/-- The change of coefficients is right exact in the degenerate case: its source has only zero
objects, so it is the zero functor. -/
private lemma moduleSheafOverConstantCoefficientsFunctor_preservesFiniteColimits_of_nonsmall
    (κ : Cardinal.{u}) (hκ : κ < B.cutoff) (hnot : ¬ Small.{w} κ.out) :
    PreservesFiniteColimits (moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ) :=
  have hzero : IsZero (moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ) :=
    (moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).isZero fun F =>
      Functor.map_isZero _ (moduleSheaf_isZero_of_nonsmall_cardinal B X Λ κ hκ hnot F)
  ⟨fun shape => Functor.preservesColimitsOfShape_of_isZero _ hzero shape⟩

/-- **The change of coefficients is right exact.** -/
instance moduleSheafOverConstantCoefficientsFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ) := by
  classical
  by_cases hsmall : ∀ κ : Cardinal.{u}, κ < B.cutoff → Small.{w} κ.out
  · exact moduleSheafOverConstantCoefficientsFunctor_preservesFiniteColimits_of_small_sizes
      B X Λ hsmall
  push Not at hsmall
  obtain ⟨κ, hκ, hnot⟩ := hsmall
  exact moduleSheafOverConstantCoefficientsFunctor_preservesFiniteColimits_of_nonsmall
    B X Λ κ hκ hnot

end AlgebraicGeometry

end
