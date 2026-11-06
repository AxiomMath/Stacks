module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWattsPhi
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Basic

/-!
# The geometric factor of the affine case of Tag 0EX3 (b), and its `R`-linearity

The proof of [Stacks, Tag 0EX3] (b) reduces to an affine base `Y' = Spec R'` and there considers
the endofunctor of `R'`-modules

> `Φ(M) = H^d(X', F' ⊗_{𝒪_{X'}} (f')^* M~)`.

`StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWattsPhi` assembles `Φ` out of the
cohomological tail and a **geometric factor** `T : ModuleCat R' ⥤ QCoh(X')`,
`M ↦ F' ⊗ (f')^* M~`, which it takes as an argument together with the four properties
Eilenberg-Watts asks of it. This file **constructs that argument** and proves
the four properties, so that the Eilenberg-Watts isomorphism holds for the functor the source
actually writes down rather than for a hypothetical one.

The `R`-linearity of `T` comes in three pieces. The tilde half is proved here from Mathlib's
tilde-Gamma adjunction; the pullback and tensor halves are the linearity lemmas of
`StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Basic`.

## Main definitions

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.geometricFactorFormula`:
  `tilde ⋙ (f')^* ⋙ (F' ⊗ -)`, with codomain all module sheaves on `X'`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.geometricFactor`: the same functor with its
  codomain restricted to quasi-coherent modules. This is the `T` of `affineTopDegreeFunctor`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.tensorFactorMap` and
  `Stacks.AlgebraicGeometry.TopDegreeBaseChange.geometricFactorFormulaMap`: the natural
  transformation a morphism `F ⟶ F'` of the *fixed* factor induces, with its identity and
  composition laws. Only the tensor factor depends on `F`, so the geometric one is the tensor one
  whiskered by `tildeFactor` and `pullbackFactor`.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.linear_moduleSpecΓFunctor`: taking global
  sections of a module on `Spec R` is `R`-linear.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.linear_tildeFunctor`: **the tilde functor is
  `R`-linear**, for the linear structure the base `Spec R → Spec R` induces; it is the left
  adjoint of the previous item.
* `additive_geometricFactor`, `linear_geometricFactor`,
  `preservesFiniteColimits_geometricFactor` and
  `preservesColimitsOfShape_discrete_geometricFactor`: the four hypotheses of
  `Stacks.EilenbergWatts.iso`, for `T`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.affineTopDegreeTensorIso`: **Eilenberg-Watts for
  the functor of the affine case of [Stacks, Tag 0EX3] (b)**, with its geometric factor
  constructed. `M ↦ H^d(X', F' ⊗ (f')^* M~)` is tensoring with the `R`-module
  `H^d(X', F' ⊗ (f')^* R~)`.

## Implementation notes

*Declared types everywhere.* Each of the three factors is named by a `def` carrying its declared
functor type (`tildeFactor`, `pullbackFactor`, `tensorFactor`) and the formula is their composite.
This is not cosmetic: instance search does not cross between the two spellings
`SheafOfModules X.ringCatSheaf` and `X.Modules` of the same category, so a composite written out
of the underlying Mathlib terms has no additivity, linearity or colimit instance, while the
composite of the three named factors has all three.

*Two linear structures on one category, and the spelling decides which resolves.*
`AlgebraicGeometry.modulesLinear R W` is declared at `Linear R W.left.Modules`. Supplying it at
that spelling gives `Linear R W.left.Modules` and supplying it at
`Linear R (SheafOfModules.{u} W.left.ringCatSheaf)` gives the quasi-coherent full subcategory's
structure; neither is derivable from the other, so `linear_geometricFactorFormula` is stated at
the first (its codomain is `W.left.Modules`) and `linear_geometricFactor` at the second (its
codomain is the full subcategory), matching the hypothesis shape of `affineTopDegreeFunctorIso`.

*Why the two `CommRingCat`-variable restatements.* `additive_tildeFunctor` and
`preservesColimitsOfSize_tildeFunctor` repeat Mathlib facts verbatim. They are needed because
Mathlib states them for a variable `A : CommRingCat` and they do not synthesize at
`CommRingCat.of R` for `R : Type u` with `[CommRing R]`; instantiating a named lemma at
`CommRingCat.of R` does work.

*Transfer through the quasi-coherent inclusion.* `ObjectProperty.liftCompιIso` is `Iso.refl`, so
the composite `T ⋙ ι` is definitionally the formula; colimit preservation therefore transfers by
`inferInstanceAs` with no natural isomorphism, while additivity and linearity use the iso with
`Functor.additive_of_comp_faithful` and `AlgebraicGeometry.linear_of_faithful_comp`.

*What is still a hypothesis, and why.* `affineTopDegreeTensorIso` takes the top-degree vanishing
`H^{d+1}(X', -) = 0` on quasi-coherent modules as a hypothesis, and quasi-compactness and
quasi-separatedness of the morphism `f'` as instances. In a
`Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation` over an affine base all three are
discharged, by `isZero_cohomology_of_lt`, `quasiCompact_f'` and `quasiSeparated_f'`; identifying
that situation's `Y'` with `Spec R'` is a separate step.

*No `@[stacks 0EX3]` attribute.* The tag asserts conclusions (a), (b) and (c); (a) carries the
attribute in `StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeVanishing` and (b) in
`StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TensorComparisonBase`, over a base with no
hypothesis. What is proved *here* is the affine case of (b) — the source's own
reduction — and not (b) itself, which is why this file places no attribute. The global form
follows from this reduction together with the nested-opens
compatibility of [Stacks, Tag 01E5] for the comparison that carries that tag,
`Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIso`, at the situation's own
(possibly positive) degree `d`. That compatibility holds **at the ringed-space level in
every degree**, for the comparison that carries the tag:
`Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIso_ofLE`, in
`StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.LocalizationCocycle`. Relating it to
the comparison built from the composite pushforward-then-restrict functor uses a composition law
for `Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` and a compatibility between
the two engines
(`Stacks.Cohomology.DerivedCompTransport.compRightDerivedNatIso_comp`,
`...rightDerivedCompIso_comp_compRightDerivedNatIso`, and the degree-zero normalisation
`higherDirectImageRestrictIsoSucc_zero`). What (b) waits on at this level is the transport
of that clause to the scheme-level, `ℤ`-indexed comparison. A full proof of (b) over a
non-affine `Y'`
would also need a sheaf-gluing construction assembling the affine-case isomorphisms over
an open cover of `Y'`, and a local-to-global invertibility argument. Withholding the attribute
is therefore deliberate.

The affine-case isomorphisms themselves are available over an **arbitrary** `Y'`, one for
each affine open of it, by restricting the situation to that open
(`Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.restrictBase` and the two results beside
it in `StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWattsUnitor`, which carry the
tag with that restriction named). It is the gluing described above, and not the affineness of the
base, that stands between those and (b).

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

noncomputable section

/-- **Mathlib's additivity of the tilde functor, at the `CommRingCat` variable.** Mathlib's
instance does not synthesize at `CommRingCat.of R` for a bare commutative ring `R`; this lemma
does, by instantiation. -/
theorem additive_tildeFunctor (A : CommRingCat.{u}) :
    (AlgebraicGeometry.tilde.functor A).Additive :=
  inferInstance

/-- **The tilde functor preserves all small colimits**, being the left adjoint of global
sections. -/
theorem preservesColimitsOfSize_tildeFunctor (A : CommRingCat.{u}) :
    PreservesColimitsOfSize.{u, u} (AlgebraicGeometry.tilde.functor A) :=
  (AlgebraicGeometry.tilde.adjunction (R := A)).leftAdjoint_preservesColimits

variable (R : Type u) [CommRing R]

/-- `Spec R` as an `R`-scheme, through its identity structure morphism. This is the affine base
of the reduction in [Stacks, Tag 0EX3] (b). -/
abbrev specBase : Over (Spec (CommRingCat.of R)) := Over.mk (𝟙 (Spec (CommRingCat.of R)))

set_option backward.isDefEq.respectTransparency false in
/-- **Taking global sections of a module on `Spec R` is `R`-linear.** The `R`-action on sections
over an open is multiplication by the image of the scalar under `R ⟶ Γ(Spec R, ⊤) ⟶ Γ(Spec R, U)`,
which is exactly the scalar that the linear structure of the base multiplies by, so the two sides
agree on the nose. -/
theorem linear_moduleSpecΓFunctor :
    letI : Linear R (Spec (CommRingCat.of R)).Modules := modulesLinear R (specBase R)
    (moduleSpecΓFunctor (R := CommRingCat.of R)).Linear R := by
  let : Linear R (Spec (CommRingCat.of R)).Modules := modulesLinear R (specBase R)
  rw [Functor.linear_iff]
  intro M r
  apply ModuleCat.hom_ext
  ext x
  with_unfolding_all rfl

/-- **The tilde functor is `R`-linear.** It is the left adjoint of the `R`-linear global-sections
functor, and a left adjoint of a linear functor is linear. -/
theorem linear_tildeFunctor :
    letI : Linear R (Spec (CommRingCat.of R)).Modules := modulesLinear R (specBase R)
    (AlgebraicGeometry.tilde.functor (CommRingCat.of R)).Linear R := by
  let : Linear R (Spec (CommRingCat.of R)).Modules := modulesLinear R (specBase R)
  let : (moduleSpecΓFunctor (R := CommRingCat.of R)).Linear R := linear_moduleSpecΓFunctor R
  exact leftAdjoint_linear_of_rightAdjoint_linear R
    (AlgebraicGeometry.tilde.adjunction (R := CommRingCat.of R))

variable (W : Over (Spec (CommRingCat.of R)))

/-- The structure morphism of `W`, read as a morphism of `R`-schemes into the affine base. -/
abbrev toSpecBase : W ⟶ specBase R := Over.homMk W.hom (by simp)

/-- The underlying morphism of `toSpecBase R W` is the structure morphism of `W`. -/
lemma toSpecBase_left : (toSpecBase R W).left = W.hom := rfl

/-- The tilde factor `M ↦ M~` of the geometric factor, with a declared functor type. -/
def tildeFactor : ModuleCat.{u} R ⥤ (Spec (CommRingCat.of R)).Modules :=
  AlgebraicGeometry.tilde.functor (CommRingCat.of R)

/-- The pullback factor `(f')^*` of the geometric factor, with a declared functor type. -/
def pullbackFactor : (Spec (CommRingCat.of R)).Modules ⥤ W.left.Modules :=
  Scheme.Modules.pullback (toSpecBase R W).left

/-- The tensor factor `F ⊗ -` of the geometric factor, with a declared endofunctor type. -/
def tensorFactor (F : SheafOfModules.{u} W.left.ringCatSheaf) :
    W.left.Modules ⥤ W.left.Modules :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
    ⟨W.left.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (W.left.presheaf)
      (forget₂ CommRingCat RingCat) ((ringSheafCond W.left))⟩).obj (F))

/-- The tilde functor `M ↦ M~` is additive. -/
instance additive_tildeFactor : (tildeFactor R).Additive :=
  additive_tildeFunctor (CommRingCat.of R)

/-- The tilde functor `M ↦ M~` preserves colimits. -/
instance preservesColimitsOfSize_tildeFactor : PreservesColimitsOfSize.{u, u} (tildeFactor R) :=
  preservesColimitsOfSize_tildeFunctor (CommRingCat.of R)

/-- The pullback functor `(f')^*` is additive. -/
instance additive_pullbackFactor : (pullbackFactor R W).Additive :=
  inferInstanceAs (Scheme.Modules.pullback (toSpecBase R W).left).Additive

/-- The pullback functor `(f')^*` preserves colimits. -/
instance preservesColimitsOfSize_pullbackFactor :
    PreservesColimitsOfSize.{u, u} (pullbackFactor R W) :=
  inferInstanceAs (PreservesColimitsOfSize.{u, u}
    (Scheme.Modules.pullback (toSpecBase R W).left))

/-- The tensor functor `F ⊗ -` preserves colimits. -/
instance preservesColimitsOfSize_tensorFactor (F : SheafOfModules.{u} W.left.ringCatSheaf) :
    PreservesColimitsOfSize.{u, u} (tensorFactor R W F) :=
  Stacks.SheafOfModules.TensorColimits.tensorLeft_preservesColimits
    (Opens.grothendieckTopology W.left.carrier) ⟨W.left.presheaf, W.left.IsSheaf⟩ F

/-- The tensor functor `F ⊗ -` is additive. -/
instance additive_tensorFactor (F : SheafOfModules.{u} W.left.ringCatSheaf) :
    (tensorFactor R W F).Additive := by
  let : PreservesColimit (Functor.empty.{0} _) (tensorFactor R W F) := by infer_instance
  let : Functor.PreservesZeroMorphisms (tensorFactor R W F) :=
    Functor.preservesZeroMorphisms_of_preserves_initial_object (F := tensorFactor R W F)
  let : PreservesBinaryBiproducts (tensorFactor R W F) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorFactor R W F)
  exact Functor.additive_of_preservesBinaryBiproducts (tensorFactor R W F)

/-- **The tensor factor is functorial in the fixed factor**: a morphism `F ⟶ F'` of sheaves of
modules on `X'` induces `(F ⊗ -) ⟶ (F' ⊗ -)`. -/
noncomputable def tensorFactorMap {F F' : SheafOfModules.{u} W.left.ringCatSheaf} (f : F ⟶ F') :
    tensorFactor R W F ⟶ tensorFactor R W F' :=
  Stacks.SheafOfModules.tensorLeftFunctorMap W.left.presheaf (ringSheafCond W.left) f

/-- `tensorFactorMap` sends the identity of `F` to the identity of `F ⊗ -`. -/
@[simp]
theorem tensorFactorMap_id (F : SheafOfModules.{u} W.left.ringCatSheaf) :
    tensorFactorMap R W (𝟙 F) = 𝟙 _ :=
  Stacks.SheafOfModules.tensorLeftFunctorMap_id _ _ _

/-- `tensorFactorMap` sends a composite to the composite of the induced transformations. -/
@[simp]
theorem tensorFactorMap_comp {F F' F'' : SheafOfModules.{u} W.left.ringCatSheaf}
    (f : F ⟶ F') (g : F' ⟶ F'') :
    tensorFactorMap R W (f ≫ g) = tensorFactorMap R W f ≫ tensorFactorMap R W g :=
  Stacks.SheafOfModules.tensorLeftFunctorMap_comp _ _ f g

/-- **`M ↦ F ⊗ (f')^* M~`**, before restricting the codomain to quasi-coherent modules. -/
def geometricFactorFormula (F : SheafOfModules.{u} W.left.ringCatSheaf) :
    ModuleCat.{u} R ⥤ W.left.Modules :=
  tildeFactor R ⋙ pullbackFactor R W ⋙ tensorFactor R W F

/-- **The geometric factor is functorial in the fixed factor**: a morphism `F ⟶ F'` induces
`(M ↦ F ⊗ (f')^* M~) ⟶ (M ↦ F' ⊗ (f')^* M~)`, namely `tensorFactorMap` whiskered by the tilde
and pullback factors. -/
noncomputable def geometricFactorFormulaMap
    {F F' : SheafOfModules.{u} W.left.ringCatSheaf} (f : F ⟶ F') :
    geometricFactorFormula R W F ⟶ geometricFactorFormula R W F' :=
  Functor.whiskerLeft (tildeFactor R)
    (Functor.whiskerLeft (pullbackFactor R W) (tensorFactorMap R W f))

/-- Equal morphisms `f = g` induce equal transformations under `geometricFactorFormulaMap`. -/
theorem geometricFactorFormulaMap_congr {F F' : SheafOfModules.{u} W.left.ringCatSheaf}
    {f g : F ⟶ F'} (h : f = g) :
    geometricFactorFormulaMap R W f = geometricFactorFormulaMap R W g := by
  subst h
  rfl

/-- `geometricFactorFormulaMap` sends the identity of `F` to the identity transformation. -/
@[simp]
theorem geometricFactorFormulaMap_id (F : SheafOfModules.{u} W.left.ringCatSheaf) :
    geometricFactorFormulaMap R W (𝟙 F) = 𝟙 _ := by
  simp only [geometricFactorFormulaMap, tensorFactorMap_id, Functor.whiskerLeft_id']
  rfl

/-- `geometricFactorFormulaMap` sends a composite to the composite of the induced
transformations. -/
@[simp]
theorem geometricFactorFormulaMap_comp {F F' F'' : SheafOfModules.{u} W.left.ringCatSheaf}
    (f : F ⟶ F') (g : F' ⟶ F'') :
    geometricFactorFormulaMap R W (f ≫ g) =
      geometricFactorFormulaMap R W f ≫ geometricFactorFormulaMap R W g := by
  simp only [geometricFactorFormulaMap, tensorFactorMap_comp, Functor.whiskerLeft_comp]
  rfl

section

variable (F : SheafOfModules.{u} W.left.ringCatSheaf)

/-- The functor `M ↦ F ⊗ (f')^* M~` is additive. -/
instance additive_geometricFactorFormula : (geometricFactorFormula R W F).Additive :=
  inferInstanceAs ((tildeFactor R ⋙ pullbackFactor R W ⋙ tensorFactor R W F).Additive)

/-- The functor `M ↦ F ⊗ (f')^* M~` preserves colimits. -/
instance preservesColimitsOfSize_geometricFactorFormula :
    PreservesColimitsOfSize.{u, u} (geometricFactorFormula R W F) :=
  inferInstanceAs (PreservesColimitsOfSize.{u, u}
    (tildeFactor R ⋙ pullbackFactor R W ⋙ tensorFactor R W F))

/-- The functor `M ↦ F ⊗ (f')^* M~` preserves finite colimits. -/
instance preservesFiniteColimits_geometricFactorFormula :
    PreservesFiniteColimits (geometricFactorFormula R W F) := inferInstance

/-- **`R`-linearity of `M ↦ F ⊗ (f')^* M~`.** The tilde half is `linear_tildeFunctor`, the
pullback half `AlgebraicGeometry.over_pullback_linear` and the tensor half
`AlgebraicGeometry.tensorLeft_linear`. -/
theorem linear_geometricFactorFormula :
    letI : Linear R W.left.Modules := modulesLinear R W
    (geometricFactorFormula R W F).Linear R := by
  let : Linear R (SheafOfModules.{u} W.left.ringCatSheaf) := modulesLinear R W
  let : Linear R W.left.Modules := modulesLinear R W
  let : Linear R (Spec (CommRingCat.of R)).Modules := modulesLinear R (specBase R)
  let : (tildeFactor R).Linear R := linear_tildeFunctor R
  let : (pullbackFactor R W).Linear R := over_pullback_linear R (toSpecBase R W)
  let : (tensorFactor R W F).Linear R := tensorLeft_linear R W F
  exact inferInstanceAs
    ((tildeFactor R ⋙ pullbackFactor R W ⋙ tensorFactor R W F).Linear R)

end

section Lift

variable (F : (SheafOfModules.isQuasicoherent W.left.ringCatSheaf).FullSubcategory)

/-- Every value of `M ↦ F ⊗ (f')^* M~` is quasi-coherent, for `F` quasi-coherent: `M~` is
quasi-coherent, pullback preserves quasi-coherence, and so does tensoring two quasi-coherent
modules. -/
theorem isQuasicoherent_geometricFactorFormula (M : ModuleCat.{u} R) :
    ((geometricFactorFormula R W F.obj).obj M).IsQuasicoherent := by
  have h1 : ((tildeFactor R).obj M).IsQuasicoherent :=
    inferInstanceAs (((AlgebraicGeometry.tilde.functor (CommRingCat.of R)).obj M).IsQuasicoherent)
  have h2 : ((pullbackFactor R W).obj ((tildeFactor R).obj M)).IsQuasicoherent :=
    @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _
      (toSpecBase R W).left.toLRSHom.toShHom _ h1
  show ((((Stacks.SheafOfModules.Tensor.sheafTensor
    ⟨((W.left.toRingedSpace)).presheaf, ((W.left.toRingedSpace)).IsSheaf⟩).obj (F.obj)).obj
    (((pullbackFactor R W).obj ((tildeFactor R).obj M))))).IsQuasicoherent
  exact @AlgebraicGeometry.tensorSheaf_isQuasicoherent _ _ _ F.property h2

/-- **The geometric factor `T` of the affine case of [Stacks, Tag 0EX3] (b)**:
`M ↦ F ⊗ (f')^* M~`, as a functor from `R`-modules to quasi-coherent modules on `X'`. -/
def geometricFactor : ModuleCat.{u} R ⥤
    (SheafOfModules.isQuasicoherent W.left.ringCatSheaf).FullSubcategory :=
  ObjectProperty.lift _ (geometricFactorFormula R W F.obj)
    (isQuasicoherent_geometricFactorFormula R W F)

/-- After forgetting quasi-coherence, `T` is the formula. This is the identity isomorphism. -/
def geometricFactorCompιIso :
    geometricFactor R W F ⋙
      ObjectProperty.ι (SheafOfModules.isQuasicoherent W.left.ringCatSheaf) ≅
    geometricFactorFormula R W F.obj :=
  ObjectProperty.liftCompιIso _ _ _

/-- **The first hypothesis of `Stacks.EilenbergWatts.iso` for `T`.** -/
instance additive_geometricFactor : (geometricFactor R W F).Additive :=
  @Functor.additive_of_comp_faithful _ _ _ _ _ _ _ _ _
    (geometricFactor R W F)
    (ObjectProperty.ι (SheafOfModules.isQuasicoherent W.left.ringCatSheaf))
    ⟨by intros; rfl⟩
    (@Functor.additive_of_iso _ _ _ _ _ _ _ (additive_geometricFactorFormula R W F.obj) _
      (geometricFactorCompιIso R W F).symm)
    inferInstance

/-- **The second hypothesis of `Stacks.EilenbergWatts.iso` for `T`**: `R`-linearity. This is the
one named object between
`StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWattsPhi` and the affine case of
[Stacks, Tag 0EX3] (b). -/
theorem linear_geometricFactor :
    letI : Linear R (SheafOfModules.{u} W.left.ringCatSheaf) := modulesLinear R W
    (geometricFactor R W F).Linear R := by
  let : Linear R (SheafOfModules.{u} W.left.ringCatSheaf) := modulesLinear R W
  let : Linear R W.left.Modules := modulesLinear R W
  let : (geometricFactor R W F ⋙
      ObjectProperty.ι (SheafOfModules.isQuasicoherent W.left.ringCatSheaf)).Linear R :=
    @Functor.linear_of_iso R _ _ _ _ _ _ _ _ _ _ _
      (geometricFactorCompιIso R W F).symm (linear_geometricFactorFormula R W F.obj)
  exact linear_of_faithful_comp R (geometricFactor R W F)
    (ObjectProperty.ι (SheafOfModules.isQuasicoherent W.left.ringCatSheaf))

/-- **The third hypothesis of `Stacks.EilenbergWatts.iso` for `T`**: right exactness. All three
factors preserve colimits, and quasi-coherence is closed under them. -/
instance preservesFiniteColimits_geometricFactor :
    PreservesFiniteColimits (geometricFactor R W F) := by
  constructor
  intro J _ _
  let : (SheafOfModules.isQuasicoherent W.left.ringCatSheaf).IsClosedUnderColimitsOfShape J :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isClosedUnderColimitsOfShape (K := J) W.left
  let : PreservesColimitsOfShape J (geometricFactor R W F ⋙
      ObjectProperty.ι (SheafOfModules.isQuasicoherent W.left.ringCatSheaf)) :=
    inferInstanceAs (PreservesColimitsOfShape J (geometricFactorFormula R W F.obj))
  exact preservesColimitsOfShape_of_reflects_of_preserves (geometricFactor R W F)
    (ObjectProperty.ι (SheafOfModules.isQuasicoherent W.left.ringCatSheaf))

/-- **The fourth hypothesis of `Stacks.EilenbergWatts.iso` for `T`**: `T` commutes with arbitrary
direct sums. -/
theorem preservesColimitsOfShape_discrete_geometricFactor (J : Type u) :
    PreservesColimitsOfShape (Discrete J) (geometricFactor R W F) := by
  let : (SheafOfModules.isQuasicoherent W.left.ringCatSheaf).IsClosedUnderColimitsOfShape
      (Discrete J) :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isClosedUnderColimitsOfShape
      (K := Discrete J) W.left
  let : PreservesColimitsOfShape (Discrete J) (geometricFactor R W F ⋙
      ObjectProperty.ι (SheafOfModules.isQuasicoherent W.left.ringCatSheaf)) :=
    inferInstanceAs (PreservesColimitsOfShape (Discrete J) (geometricFactorFormula R W F.obj))
  exact preservesColimitsOfShape_of_reflects_of_preserves (geometricFactor R W F)
    (ObjectProperty.ι (SheafOfModules.isQuasicoherent W.left.ringCatSheaf))

section Capstone

open Stacks.Cohomology.AffineBase

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.modulesLinear baseSectionsAlgebra

/-- **Eilenberg-Watts for the functor of the affine case of [Stacks, Tag 0EX3] (b), with its
geometric factor constructed.** The endofunctor `M ↦ H^d(X', F ⊗ (f')^* M~)` of `R`-modules is
tensoring with the `R`-module `H^d(X', F ⊗ (f')^* R~)`, which is the conclusion the source draws
from

> *"Any right exact `R'`-linear functor `Mod_{R'} → Mod_{R'}` which commutes with direct sums is
> given by tensoring with an `R'`-module (omitted; left as exercise for the reader)."*

The vanishing hypothesis is the one conclusion (a) of the tag supplies through
[Stacks, Tag 01XK]; quasi-compactness and quasi-separatedness of `f'` give those of `X'` because
the affine base has both. -/
def affineTopDegreeTensorIso (d : ℕ)
    [QuasiCompact W.hom] [QuasiSeparated W.hom]
    (hvan : ∀ G : W.left.Modules, G.IsQuasicoherent →
      IsZero (((moduleGlobalSections W.left).rightDerivedPlus ((d : ℤ) + 1)).obj G)) :
    MonoidalCategory.tensorLeft
        ((affineTopDegreeFunctor R W d (geometricFactor R W F)).obj (ModuleCat.of R R)) ≅
      affineTopDegreeFunctor R W d (geometricFactor R W F) :=
  haveI : CompactSpace (W.left : Type u) :=
    QuasiCompact.compactSpace_of_compactSpace W.hom
  haveI : QuasiSeparatedSpace (W.left : Type u) :=
    quasiSeparatedSpace_of_quasiSeparated W.hom
  affineTopDegreeFunctorIso R W d (geometricFactor R W F)
    (preservesColimitsOfShape_discrete_geometricFactor R W F)
    (linear_geometricFactor R W F) hvan

/-- **`Φ` with its geometric factor constructed lies in the full subcategory classified by
[Stacks, Tag 0GNV]**, the library's second and stronger Eilenberg-Watts theorem
`ModuleCat.tensorFunctorEquivalence`. The affine case of (b) therefore has two independent routes
to its conclusion. -/
theorem isLinearRightExactAndPreservesDirectSums_affineTopDegreeFunctor_geometricFactor (d : ℕ)
    [QuasiCompact W.hom] [QuasiSeparated W.hom]
    (hvan : ∀ G : W.left.Modules, G.IsQuasicoherent →
      IsZero (((moduleGlobalSections W.left).rightDerivedPlus ((d : ℤ) + 1)).obj G)) :
    ModuleCat.IsLinearRightExactAndPreservesDirectSums R R R
      (affineTopDegreeFunctor R W d (geometricFactor R W F)) :=
  have : CompactSpace (W.left : Type u) :=
    QuasiCompact.compactSpace_of_compactSpace W.hom
  have : QuasiSeparatedSpace (W.left : Type u) :=
    quasiSeparatedSpace_of_quasiSeparated W.hom
  isLinearRightExactAndPreservesDirectSums_affineTopDegreeFunctor R W d (geometricFactor R W F)
    (preservesColimitsOfShape_discrete_geometricFactor R W F)
    (linear_geometricFactor R W F) hvan

end Capstone

end Lift

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
