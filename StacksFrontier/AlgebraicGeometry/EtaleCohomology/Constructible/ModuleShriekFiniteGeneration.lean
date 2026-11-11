module

public import Mathlib.CategoryTheory.Limits.Constructions.Filtered
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteTypeStalks
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleSheafGenerationByQCQS
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ShriekGeneratorConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StalkLocus
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.ModuleCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleSheafification
import StacksCore.Tactic.StacksAttribute

/-!
# Generating a constructible sheaf of modules by finitely many extensions by zero

Let `X` be a quasi-compact and quasi-separated scheme of a big étale site and `Λ` a Noetherian
ring. Stacks 093B part (2) presents every sheaf of `Λ`-modules on `X_étale` as a quotient of a
direct sum of the sheaves `j_{U!}\underline{\Lambda}_U` at quasi-compact quasi-separated — indeed
affine — étale objects `U`, indexed by a possibly infinite set. The finite generation step of the
proof of Stacks 095N asserts that for a *constructible* sheaf finitely many of those summands
suffice. That step is proved here, and with it Stacks 095N becomes unconditional.

The argument is the source's, in two stages.

At each geometric point `t` of `X`, finitely many summands already surject onto the stalk. The
stalk of a constructible sheaf of `Λ`-modules is a finitely generated `Λ`-module, by
`AlgebraicGeometry.isFG_etaleStalk_of_isConstructibleModuleSheaf`; the stalk functor is a left
adjoint, its right adjoint being the skyscraper sheaf at the corresponding point of the site, so it
carries the presentation of the direct sum as the filtered colimit of the subsums spanned by the
finite subsets of the index set to a filtered colimit of modules; and an element of a filtered
colimit of modules comes from a stage. Finitely many generators of the stalk therefore come from
one finite subsum.

From there a quasi-compactness argument on the base gives a *single* finite subsum surjecting onto
the sheaf. For a finite subset `s` of the index set let `T s` be the set of points of `X` carrying
a nonzero geometric stalk of the cokernel of the subsum spanned by `s`. That cokernel is
constructible, being a cokernel of a map between constructible sheaves, so `T s` is a constructible
subset of `X` by Stacks 09YS (3). The family is antitone, because the range of a subsum grows with
the subsum, and its intersection is empty, by the stalkwise statement together with the fact that
the stalk functor at a geometric point depends only on the point of `X` beneath it. A constructible
subset is closed in the constructible topology of `X`, and `X` is quasi-compact in that topology
because it is a spectral space (Stacks 0901, Mathlib's `compactSpace_withConstructibleTopology`),
so Cantor's intersection theorem yields an `s` with `T s` empty. The subsum spanned by that `s` is
then surjective on every geometric stalk, hence locally surjective by Stacks 03PU for module
coefficients, hence an epimorphism.

## Main results

* `AlgebraicGeometry.exists_finset_epi_etaleStalk_map_sigma_of_isConstructibleModuleSheaf` — a
  finite subsum of a surjection onto a constructible sheaf of `Λ`-modules is already surjective on
  the stalk at a given geometric point.
* `AlgebraicGeometry.exists_finite_epi_sigma_moduleShriekConstant_of_isConstructibleModuleSheaf`
  and its affine companion — **the finite generation step of the proof of Stacks 095N**: a
  constructible sheaf of `Λ`-modules is a quotient of a finite direct sum of the sheaves
  `j_{U!}\underline{\Lambda}_U`.
* `AlgebraicGeometry.exists_finset_epi_sigma_desc_of_isConstructibleModuleSheaf` — **Stacks 095P**:
  a finite subsum of a surjection onto a constructible sheaf of `Λ`-modules, from a direct sum of
  constructible sheaves, is already a surjection.
* `AlgebraicGeometry.exists_epi_sigma_moduleShriekConstant_affine` — **Stacks 093B part (2)** with
  the generators taken at affine étale objects.
* `AlgebraicGeometry.isConstructibleModuleSheaf_sigma_moduleShriekConstant` — a finite direct sum
  of the sheaves `j_{V!}\underline{\Lambda}_V` at affine `V` is constructible: Stacks 03S8 for
  sheaves of modules on each summand, assembled by the weak Serre property of Stacks 03RZ (3),
  which closes the class under finite direct sums.
* `AlgebraicGeometry.exists_finite_epi_comp_sigma_moduleShriekConstant_affine` — **Stacks 093B
  part (2) followed by Stacks 095P**: an epimorphism onto a constructible sheaf of `Λ`-modules is
  refined by a finite direct sum of the sheaves `j_{U!}\underline{\Lambda}_U` at affine `U`. This
  is the covering property the bounded above resolution of Stacks 0960 asks of its class of terms,
  and it is unconditional.
* `AlgebraicGeometry.isConstructibleModuleSheaf_iff_qcqsShriekPresentation` and
  `AlgebraicGeometry.isConstructibleModuleSheaf_iff_hasFiniteAffineShriekPresentation` —
  **Stacks 095N** at its two presentations, the quasi-compact quasi-separated one and the affine
  one, with nothing granted. The constructibility of the generators which the library's
  hypothesis-carrying forms of the tag also take as given is
  `AlgebraicGeometry.isConstructibleModuleSheaf_moduleShriekConstant`.

## Implementation notes

The stalk at a geometric point is used as the fibre functor
`CategoryTheory.GrothendieckTopology.Point.sheafFiber` of the point of the small étale site
attached to it, which is the same functor as `AlgebraicGeometry.etaleStalkFunctorModule` by
`AlgebraicGeometry.etaleStalk_eq_presheafFiber`. What that buys is its left adjoint, the skyscraper
sheaf: a left adjoint preserves colimits of every size, while the fibre functor is only known to
preserve colimits of size `u` as an instance, while the direct sum indexed by
`A : Type (max (u + 1) r)` is a colimit of size `max (u + 1) r`. Being a left adjoint also makes
the stalk functor carry a cokernel of sheaves to the cokernel of the induced map of stalks, which
is what identifies `T s` above.

The file is in two sections. In `GeneralRing` the ring `Λ` lives in a universe `r` of its own
and the coefficient universe is `ModuleCat.{max (u + 1) r} Λ`, the smallest one containing both
the small étale site and the ring; this is the universe at which the bounded above resolution of
Stacks 0960 is stated, and everything above holds there. In `SelfRing` the ring is pinned to
`Type (u + 1)`. Stacks 03S8 for sheaves of modules,
`AlgebraicGeometry.isConstructibleModuleSheaf_moduleShriekConstant`, no longer forces that pin:
it is proved through `AlgebraicGeometry.moduleShriekConstantIsoCopower` and `ModuleCat.copower`,
which leave the ring universe free, where `AlgebraicGeometry.moduleShriekConstantIsoFree` and
`ModuleCat.free Λ`, whose source `Type r ⥤ ModuleCat.{r} Λ`, carried the ring and the module in
one universe. The pin in `SelfRing` is that of the other inputs of the statements collected
there, Stacks 095N among them, which are not reproved here; Stacks 095N and the unconditional
finite generation step are therefore in the pinned section.

Several of the general results used here are stated at a module universe `max u v w` with `w`
free, and instance synthesis cannot solve `max (u + 1) ?w` against a given universe; the
theorems declared as local instances here pin those universes so that the instances apply. The
sheafification and the colimits of the sheaf category are
`AlgebraicGeometry.smallEtaleHasSheafifyModuleMax` and
`AlgebraicGeometry.smallEtaleHasColimitsOfSizeModuleMax`.

## References

* [Stacks Project, Tag 095N](https://stacks.math.columbia.edu/tag/095N)
* [Stacks Project, Tag 095P](https://stacks.math.columbia.edu/tag/095P)
* [Stacks Project, Tag 093B](https://stacks.math.columbia.edu/tag/093B)
* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
* [Stacks Project, Tag 03S8](https://stacks.math.columbia.edu/tag/03S8)
* [Stacks Project, Tag 09YS](https://stacks.math.columbia.edu/tag/09YS)
* [Stacks Project, Tag 0901](https://stacks.math.columbia.edu/tag/0901)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Limits.CoproductsFromFiniteFiltered
open Opposite

universe u r

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts
attribute [local implicit_reducible] CoproductsFromFiniteFiltered.liftToFinsetObj
  CoproductsFromFiniteFiltered.finiteSubcoproductsCocone

namespace AlgebraicGeometry

section GeneralRing

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ]

attribute [local instance] smallEtaleHasColimitsOfSizeModuleMax
  SmallEtale.isRightAdjointPushforward_moduleCat SmallEtale.hasWeakSheafifyOver_moduleCat

/-- The forgetful functor of `Λ`-modules preserves the filtered colimits over which the geometric
stalks are formed, at the coefficient universe of this section. -/
private theorem preservesFilteredColimitsModuleMax :
    PreservesFilteredColimits (forget (ModuleCat.{max (u + 1) r} Λ)) :=
  preservesFilteredColimits_forget_moduleCatMax.{u, r} Λ

/-- Sheafification of presheaves of `Λ`-modules on a slice of the small étale site inverts
exactly the locally bijective morphisms, at the coefficient universe of this section. This is
`AlgebraicGeometry.SmallEtale.wEqualsLocallyBijective_over_moduleCat` with the ring universe
freed. -/
private theorem wEqualsLocallyBijectiveModuleMax (T : B.Scheme)
    (V : SmallEtale B T.obj T.property) :
    ((SmallEtale.topology B T.obj T.property).over V).WEqualsLocallyBijective
      (ModuleCat.{max (u + 1) r} Λ) :=
  Stacks.ConstantSheaf.wEqualsLocallyBijective_moduleCat.{u, u + 1, r, r}
    ((SmallEtale.topology B T.obj T.property).over V) Λ

attribute [local instance 2000] wEqualsLocallyBijectiveModuleMax

/-- Products indexed by a type of size `u` exist in `Λ`-modules at the coefficient universe
`max (u + 1) r`; this is what the skyscraper sheaf at a point of the small étale site asks for. -/
private theorem hasProductsModuleMax : HasProducts.{u} (ModuleCat.{max (u + 1) r} Λ) :=
  fun _ => ModuleCat.hasLimitsOfShape

/-- Limits of size `u` exist in `Λ`-modules at the coefficient universe `max (u + 1) r`. -/
private theorem hasLimitsOfSizeModuleMax : HasLimitsOfSize.{u, u} (ModuleCat.{max (u + 1) r} Λ) :=
  ModuleCat.hasLimitsOfSize.{u, u, max (u + 1) r, r}

attribute [local instance] hasProductsModuleMax hasLimitsOfSizeModuleMax

/-- The stalk at a geometric point, as the fibre functor on sheaves of `Λ`-modules of the point of
the small étale site attached to it. This is `AlgebraicGeometry.etaleStalkFunctorModule`; it is
written this way so that its left adjoint, the skyscraper sheaf, is available. -/
private abbrev moduleStalk (t : GeometricPoint X.1) :
    Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max (u + 1) r} Λ) ⥤
      ModuleCat.{max (u + 1) r} Λ :=
  (geometricPointSitePoint B X.1 X.property t).sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)

/-- The stalk functor on sheaves of `Λ`-modules preserves colimits of size `max (u + 1) r`, being
a left adjoint; its right adjoint is the skyscraper sheaf at the point. -/
private theorem preservesColimitsOfSize_moduleStalk (t : GeometricPoint X.1) :
    PreservesColimitsOfSize.{u + 1, u + 1} (moduleStalk B X Λ t) :=
  ((geometricPointSitePoint B X.1 X.property t).skyscraperSheafAdjunction
    (A := ModuleCat.{max (u + 1) r} Λ)).leftAdjoint_preservesColimits

/-- The stalk functor at a geometric point on sheaves of `Λ`-modules is a left adjoint, its right
adjoint being the skyscraper sheaf at the corresponding point of the site. -/
private theorem isLeftAdjoint_moduleStalk (t : GeometricPoint X.1) :
    (moduleStalk B X Λ t).IsLeftAdjoint :=
  ((geometricPointSitePoint B X.1 X.property t).skyscraperSheafAdjunction
    (A := ModuleCat.{max (u + 1) r} Λ)).isLeftAdjoint

/-- **The stalk of a cokernel vanishes exactly where the map is surjective on stalks.** The stalk
functor at a geometric point is a left adjoint, so it carries the cokernel of a map of sheaves of
`Λ`-modules to the cokernel of the induced map of stalks, and a map of modules is surjective
exactly when its cokernel vanishes. -/
private theorem isZero_etaleStalk_cokernel_iff
    {F F' : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max (u + 1) r} Λ)} (f : F' ⟶ F)
    (t : GeometricPoint X.1) :
    IsZero (etaleStalk B X.1 X.property t (cokernel f).obj) ↔
      Epi ((moduleStalk B X Λ t).map f) := by
  have := isLeftAdjoint_moduleStalk B X Λ t
  have e : (moduleStalk B X Λ t).obj (cokernel f) ≅ cokernel ((moduleStalk B X Λ t).map f) :=
    PreservesCokernel.iso _ _
  rw [Preadditive.epi_iff_isZero_cokernel]
  exact ⟨fun h => h.of_iso e.symm, fun h => h.of_iso e⟩

variable [IsNoetherianRing Λ]

omit [IsNoetherianRing Λ] in
/-- **The range of a subsum of a map out of a direct sum grows with the subsum.** The restriction
of `Ψ` to the subsum spanned by `s` factors through the restriction to the subsum spanned by a
larger `s'`, so the same holds of the induced maps of stalks. -/
private theorem range_moduleStalk_map_sigma_desc_le
    {F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max (u + 1) r} Λ)}
    {A : Type max (u + 1) r}
    (M : A → Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max (u + 1) r} Λ))
    (Ψ : (∐ M) ⟶ F) (t : GeometricPoint X.1) {s s' : Finset (Discrete A)} (h : s ≤ s') :
    LinearMap.range ((moduleStalk B X Λ t).map
        ((Sigma.desc fun a : {a // a ∈ s} => Sigma.ι M a.1.as) ≫ Ψ)).hom ≤
      LinearMap.range ((moduleStalk B X Λ t).map
        ((Sigma.desc fun a : {a // a ∈ s'} => Sigma.ι M a.1.as) ≫ Ψ)).hom := by
  have hw : ((Sigma.desc fun a : {a // a ∈ s} => Sigma.ι M a.1.as) ≫ Ψ) =
      (Sigma.desc fun a : {a // a ∈ s} =>
          Sigma.ι (fun a : {a // a ∈ s'} => M a.1.as) ⟨a.1, h a.2⟩) ≫
        ((Sigma.desc fun a : {a // a ∈ s'} => Sigma.ι M a.1.as) ≫ Ψ) := by
    rw [← Category.assoc]
    congr 1
    apply Sigma.hom_ext
    intro a
    simp
  rw [hw, Functor.map_comp]
  exact LinearMap.range_comp_le_range _ _

omit [IsNoetherianRing Λ] in
/-- **A finite subsum already surjects onto every stalk.** Let `Λ` be a Noetherian ring, let `F` be
a constructible sheaf of `Λ`-modules on the small étale site of `X`, and let `Ψ` be an epimorphism
onto `F` from a direct sum of sheaves of `Λ`-modules indexed by an arbitrary set `A`. Then for
every geometric point of `X` the restriction of `Ψ` to the subsum spanned by some *finite* subset
of `A` is already surjective on the stalk there.

The stalk of `F` is a finitely generated `Λ`-module, the stalk of `Ψ` is surjective, and the stalk
functor is a left adjoint, so it carries the direct sum to the filtered colimit of the subsums
spanned by the finite subsets of `A`; finitely many generators of the stalk of `F` are therefore
hit by one finite subsum.

This is the stalkwise form of the finite generation step of the proof of Stacks 095N. -/
public theorem exists_finset_epi_etaleStalk_map_sigma_of_isConstructibleModuleSheaf
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max (u + 1) r} Λ))
    {A : Type max (u + 1) r}
    (G : A → Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max (u + 1) r} Λ))
    (Ψ : (∐ G) ⟶ F) [Epi Ψ] (hF : IsConstructibleModuleSheaf B X Λ F)
    (t : GeometricPoint X.1) :
    ∃ s : Finset (Discrete A), Epi ((etaleStalkFunctorModule B X.1 X.property Λ t).map
      ((Sigma.desc fun a : {a // a ∈ s} => Sigma.ι G a.1.as) ≫ Ψ)) := by
  classical
  have := preservesFilteredColimitsModuleMax.{u, r} Λ
  have hpres := preservesColimitsOfSize_moduleStalk B X Λ t
  have hcolim : IsColimit ((moduleStalk B X Λ t).mapCocone (finiteSubcoproductsCocone G)) :=
    isColimitOfPreserves (moduleStalk B X Λ t) (isColimitFiniteSubproductsCocone G)
  have hsurjΨ : Function.Surjective ((moduleStalk B X Λ t).map Ψ) :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  have hfg : ModuleCat.isFG Λ ((moduleStalk B X Λ t).obj F) :=
    isFG_etaleStalk_of_isConstructibleModuleSheaf B Λ X F hF t
  rw [ModuleCat.isFG_iff] at hfg
  obtain ⟨T, hT⟩ := Module.finite_def.1 hfg
  have hmono : ∀ {s s' : Finset (Discrete A)}, s ≤ s' →
      LinearMap.range ((moduleStalk B X Λ t).map
          ((Sigma.desc fun a : {a // a ∈ s} => Sigma.ι G a.1.as) ≫ Ψ)).hom ≤
        LinearMap.range ((moduleStalk B X Λ t).map
          ((Sigma.desc fun a : {a // a ∈ s'} => Sigma.ι G a.1.as) ≫ Ψ)).hom :=
    fun h => range_moduleStalk_map_sigma_desc_le B X Λ G Ψ t h
  have hmem : ∀ y : ToType ((moduleStalk B X Λ t).obj F), ∃ s : Finset (Discrete A),
      y ∈ LinearMap.range ((moduleStalk B X Λ t).map
        ((Sigma.desc fun a : {a // a ∈ s} => Sigma.ι G a.1.as) ≫ Ψ)).hom := by
    intro y
    obtain ⟨n, hn⟩ := hsurjΨ y
    obtain ⟨s, z, hz⟩ := Concrete.isColimit_exists_rep _ hcolim n
    refine ⟨s, z, ?_⟩
    have hz' : ((moduleStalk B X Λ t).map
        (Sigma.desc fun a : {a // a ∈ s} => Sigma.ι G a.1.as)) z = n := hz
    have hcomp : ((moduleStalk B X Λ t).map
        ((Sigma.desc fun a : {a // a ∈ s} => Sigma.ι G a.1.as) ≫ Ψ)) z = y := by
      rw [Functor.map_comp, ConcreteCategory.comp_apply, hz', hn]
    exact hcomp
  refine ⟨T.sup fun y => (hmem y).choose, ?_⟩
  rw [ModuleCat.epi_iff_range_eq_top]
  refine eq_top_iff.2 (le_trans (le_of_eq hT.symm) (Submodule.span_le.2 ?_))
  intro y hy
  exact hmono (Finset.le_sup (Finset.mem_coe.1 hy)) (hmem y).choose_spec
variable [CompactSpace X.1] [QuasiSeparatedSpace X.1]

/-- The constructible sheaves of `Λ`-modules on `X_étale`, as a property of objects of the category
of sheaves of `Λ`-modules, at the universes of this file. -/
private abbrev constructibleModuleSheavesMax :
    ObjectProperty (Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max (u + 1) r} Λ)) :=
  fun F => IsConstructibleModuleSheaf B X Λ F

/-- The constructible sheaves of `Λ`-modules form a weak Serre subcategory; this is Stacks 03RZ (3)
with its coefficient universe pinned to the one of this file. -/
private instance isWeakSerreClass_constructibleModuleSheavesMax :
    (constructibleModuleSheavesMax B X Λ).IsWeakSerreClass :=
  SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf.{u, r, r} B X Λ

/-- A weak Serre subcategory is closed under finite coproducts: a binary coproduct is a binary
biproduct, hence an extension of one summand by the other. -/
private instance isClosedUnderFiniteCoproducts_constructibleModuleSheavesMax :
    (constructibleModuleSheavesMax B X Λ).IsClosedUnderFiniteCoproducts := by
  have : (constructibleModuleSheavesMax B X Λ).IsClosedUnderBinaryCoproducts :=
    ObjectProperty.IsClosedUnderColimitsOfShape.mk' (fun _ ⟨H, hH⟩ =>
      (constructibleModuleSheavesMax B X Λ).prop_of_iso
        ((biprod.isoCoprod _ _).trans (HasColimit.isoOfNatIso (diagramIsoPair H)).symm)
        ((constructibleModuleSheavesMax B X Λ).prop_biprod (hH ⟨.left⟩) (hH ⟨.right⟩)))
  exact ObjectProperty.IsClosedUnderFiniteCoproducts.mk'

/-- **Stacks 03S8 for sheaves of modules, in the shape the presentations use it.** The extension
by zero of a constant free rank-one module sheaf at a quasi-compact quasi-separated étale object
is constructible. This is
`AlgebraicGeometry.isConstructibleModuleSheaf_moduleShriekConstant` with the two space-level
hypotheses taken as a conjunction rather than as instances. -/
private theorem isConstructibleModuleSheaf_moduleShriekConstant_of_compact_of_quasiSeparated
    (R : Type r) [CommRing R] (U : SmallEtale B X.1 X.property)
    (hU : CompactSpace ((SmallEtale.toScheme B X.1 X.property).obj U) ∧
      QuasiSeparatedSpace ((SmallEtale.toScheme B X.1 X.property).obj U)) :
    IsConstructibleModuleSheaf B X R (moduleShriekConstant.{u, r, r} B X R U) := by
  have hc := hU.1
  have hq := hU.2
  have hc' : CompactSpace U.obj.left.obj :=
    inferInstanceAs (CompactSpace ((SmallEtale.toScheme B X.1 X.property).obj U))
  have hq' : QuasiSeparatedSpace U.obj.left.obj :=
    inferInstanceAs (QuasiSeparatedSpace ((SmallEtale.toScheme B X.1 X.property).obj U))
  exact isConstructibleModuleSheaf_moduleShriekConstant B X R U

/-- The extension by zero of a constant free rank-one module sheaf at an affine étale object is
constructible, an affine scheme being quasi-compact and quasi-separated. -/
private theorem isConstructibleModuleSheaf_moduleShriekConstant_of_isAffine
    (R : Type r) [CommRing R] (U : SmallEtale B X.1 X.property)
    (hU : SmallEtale.IsAffine B X.1 X.property U) :
    IsConstructibleModuleSheaf B X R (moduleShriekConstant.{u, r, r} B X R U) := by
  have := hU
  exact isConstructibleModuleSheaf_moduleShriekConstant_of_compact_of_quasiSeparated B X R U
    ⟨inferInstance, inferInstance⟩

/-- **A finite direct sum of extensions by zero of constant free rank-one module sheaves at
affine étale objects is constructible.** Let `X` be a quasi-compact and quasi-separated scheme of
a big étale site and `Λ` a Noetherian ring in a universe `r` of its own. For affine objects
`V_1, …, V_n` of the small étale site of `X` the sheaf
`⊕_j j_{V_j!}\underline{\Lambda}_{V_j}` of `Λ`-modules is constructible.

Each summand is constructible by Stacks 03S8 for sheaves of modules,
`AlgebraicGeometry.isConstructibleModuleSheaf_moduleShriekConstant`, an affine object of the
small étale site being quasi-compact and quasi-separated; and constructibility is closed under
finite direct sums because the constructible sheaves of `Λ`-modules form a weak Serre
subcategory, Stacks 03RZ (3), so a binary coproduct — being a biproduct, hence an extension of
one summand by the other — stays in the class. -/
@[sga "4 IX 2.9" "(ii), special case"]
public theorem isConstructibleModuleSheaf_sigma_moduleShriekConstant {n : ℕ}
    (V : Fin n → SmallEtale B X.1 X.property)
    (hV : ∀ j, SmallEtale.IsAffine B X.1 X.property (V j)) :
    IsConstructibleModuleSheaf B X Λ
      (∐ fun j => moduleShriekConstant.{u, r, r} B X Λ (V j)) :=
  (constructibleModuleSheavesMax B X Λ).prop_coproduct fun j =>
    isConstructibleModuleSheaf_moduleShriekConstant_of_isAffine B X Λ (V j) (hV j)

/-- **Stacks 09YS (3) at the cokernel of a map of constructible sheaves of `Λ`-modules.** The set
of points of `X` carrying a nonzero geometric stalk of that cokernel is a constructible subset:
the cokernel is constructible, being a cokernel of a map between constructible sheaves. -/
private theorem isConstructible_setOf_not_isZero_etaleStalk_cokernel
    {F F' : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max (u + 1) r} Λ)} (f : F' ⟶ F)
    (hF' : IsConstructibleModuleSheaf B X Λ F') (hF : IsConstructibleModuleSheaf B X Λ F) :
    Topology.IsConstructible {x : X.1 | ∃ t : GeometricPoint X.1, t.LiesOver x ∧
      ¬ IsZero (etaleStalk B X.1 X.property t (cokernel f).obj)} :=
  have := preservesFilteredColimitsModuleMax.{u, r} Λ
  isConstructible_support_moduleSheaf.{max (u + 1) r, u, r} B X Λ _
    ((constructibleModuleSheavesMax B X Λ).prop_cokernel f hF' hF)

/-- **A constructible subset is closed in the constructible topology.** It is open there, that
topology being generated by the constructible subsets, and so is its complement, which is
constructible as well; the statement is given for the preimage in the type synonym carrying the
constructible topology as its instance. -/
private theorem isClosed_preimage_ofConstructible_of_isConstructible {Z : Set X.1}
    (hZ : Topology.IsConstructible Z) :
    IsClosed (WithConstructibleTopology.ofConstructible ⁻¹' Z) := by
  rw [← isOpen_compl_iff, ← Set.preimage_compl,
    WithConstructibleTopology.isOpen_preimage_ofConstructible,
    constructibleTopology_eq_generateFrom_isConstructible ↥X.1]
  exact TopologicalSpace.isOpen_generateFrom_of_mem hZ.compl

/-- **The finite generation step of the proof of Stacks 095N, before reindexing.** Let `X` be a
quasi-compact and quasi-separated scheme and `Λ` a Noetherian ring, let `F` be a constructible
sheaf of `Λ`-modules on `X_étale` and let `Ψ` be an epimorphism onto `F` from a direct sum of
*constructible* sheaves of `Λ`-modules indexed by an arbitrary set `A`. Then the restriction of
`Ψ` to the subsum spanned by some *finite* subset of `A` is already an epimorphism.

The argument is the source's. For a finite subset `s` of `A` let `T s` be the set of points of
`X` over which the cokernel of the restricted map has a nonzero geometric stalk; it is a
constructible subset of `X` by Stacks 09YS (3), the cokernel being constructible. The family is
antitone, the range of a subsum growing with the subsum, and its intersection is empty, because
at every geometric point some finite subsum is already surjective
(`AlgebraicGeometry.exists_finset_epi_etaleStalk_map_sigma_of_isConstructibleModuleSheaf`) and
the stalk functor at a geometric point depends only on the point of `X` beneath it. A
constructible subset is closed in the constructible topology of `X`, in which `X` is
quasi-compact by Stacks 0901, so Cantor's intersection theorem produces an `s` with `T s` empty.
The restricted map is then surjective on every geometric stalk, hence locally surjective by
Stacks 03PU, hence an epimorphism. -/
public theorem exists_finset_epi_sigma_desc_of_isConstructibleModuleSheaf
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max (u + 1) r} Λ))
    {A : Type max (u + 1) r}
    (M : A → Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max (u + 1) r} Λ))
    (Ψ : (∐ M) ⟶ F) [Epi Ψ] (hM : ∀ a, IsConstructibleModuleSheaf B X Λ (M a))
    (hF : IsConstructibleModuleSheaf B X Λ F) :
    ∃ s : Finset (Discrete A),
      Epi ((Sigma.desc fun a : {a // a ∈ s} => Sigma.ι M a.1.as) ≫ Ψ) := by
  classical
  let T : Finset (Discrete A) → Set X.1 := fun s =>
    {x : X.1 | ∃ t : GeometricPoint X.1, t.LiesOver x ∧
      ¬ IsZero (etaleStalk B X.1 X.property t
        (cokernel ((Sigma.desc fun a : {a // a ∈ s} => Sigma.ι M a.1.as) ≫ Ψ)).obj)}
  have hTiff : ∀ (s : Finset (Discrete A)) (x : X.1), x ∈ T s ↔ ∃ t : GeometricPoint X.1,
      t.LiesOver x ∧ ¬ Epi ((moduleStalk B X Λ t).map
        ((Sigma.desc fun a : {a // a ∈ s} => Sigma.ι M a.1.as) ≫ Ψ)) := fun s x =>
    exists_congr fun t => and_congr_right fun _ =>
      not_congr (isZero_etaleStalk_cokernel_iff B X Λ _ t)
  have hcons : ∀ s, Topology.IsConstructible (T s) := fun s =>
    isConstructible_setOf_not_isZero_etaleStalk_cokernel B X Λ _
      ((constructibleModuleSheavesMax B X Λ).prop_coproduct fun a => hM a.1.as) hF
  have hanti : ∀ {s s' : Finset (Discrete A)}, s ≤ s' → T s' ⊆ T s := by
    intro s s' hss x hx
    obtain ⟨t, ht, hne⟩ := (hTiff s' x).1 hx
    refine (hTiff s x).2 ⟨t, ht, fun hepi => hne ?_⟩
    have hr := range_moduleStalk_map_sigma_desc_le B X Λ M Ψ t hss
    rw [ModuleCat.epi_iff_range_eq_top] at hepi ⊢
    exact eq_top_iff.2 (le_trans (le_of_eq hepi.symm) hr)
  have hempty : (⋂ s, T s) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
    obtain ⟨s, hs⟩ := exists_finset_epi_etaleStalk_map_sigma_of_isConstructibleModuleSheaf
      B X Λ F M Ψ hF (GeometricPoint.ofPoint X.1 x)
    obtain ⟨t, ht, hne⟩ := (hTiff s x).1 (Set.mem_iInter.1 hx s)
    refine hne ((ModuleCat.epi_iff_surjective _).2 ?_)
    exact surjective_map_of_natIsoOfCoefficients (ModuleCat.{max (u + 1) r} Λ)
      (etaleStalkPresheafFunctorIsoOfEqBase B X.1 X.property
        (ht.trans (GeometricPoint.ofPoint_liesOver X.1 x).symm) (ModuleCat.{max (u + 1) r} Λ))
      ((Sigma.desc fun a : {a // a ∈ s} => Sigma.ι M a.1.as) ≫ Ψ).hom
      ((ModuleCat.epi_iff_surjective _).1 hs)
  obtain ⟨s, hs⟩ : ∃ s : Finset (Discrete A), T s = ∅ := by
    by_contra hcon
    have hne : ∀ s : Finset (Discrete A),
        (WithConstructibleTopology.ofConstructible ⁻¹' T s).Nonempty := by
      intro s
      obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.2 fun h => hcon ⟨s, h⟩
      exact ⟨WithConstructibleTopology.toConstructible y, by simpa using hy⟩
    have hcl : ∀ s : Finset (Discrete A),
        IsClosed (WithConstructibleTopology.ofConstructible ⁻¹' T s) := fun s =>
      isClosed_preimage_ofConstructible_of_isConstructible B X (hcons s)
    have hdir : Directed (· ⊇ ·)
        fun s : Finset (Discrete A) => WithConstructibleTopology.ofConstructible ⁻¹' T s :=
      fun s s' => ⟨s ∪ s', Set.preimage_mono (hanti le_sup_left),
        Set.preimage_mono (hanti le_sup_right)⟩
    obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      (fun s : Finset (Discrete A) => WithConstructibleTopology.ofConstructible ⁻¹' T s)
      hdir hne (fun s => (hcl s).isCompact) hcl
    have hmem : WithConstructibleTopology.ofConstructible y ∈ ⋂ s, T s :=
      Set.mem_iInter.2 fun s => Set.mem_iInter.1 hy s
    rw [hempty] at hmem
    exact hmem
  refine ⟨s, ?_⟩
  have hstalk : ∀ t : GeometricPoint X.1, Function.Surjective
      ((etaleStalkPresheafFunctor B X.1 X.property t (ModuleCat.{max (u + 1) r} Λ)).map
        ((Sigma.desc fun a : {a // a ∈ s} => Sigma.ι M a.1.as) ≫ Ψ).hom) := by
    intro t
    by_contra hcon
    have hx : t.hom default ∈ T s :=
      (hTiff s _).2 ⟨t, rfl, fun hepi => hcon ((ModuleCat.epi_iff_surjective _).1 hepi)⟩
    rw [hs] at hx
    exact hx
  have := preservesFilteredColimitsOfSize_forget_moduleCatMax.{u, r} Λ
  have := isLocallySurjective_of_surjective_etaleStalkMapOfCoefficients B X.1 X.property
    (ModuleCat.{max (u + 1) r} Λ) _ hstalk
  exact inferInstance
/-- **A finite subsum of a presentation of a constructible sheaf, reindexed by `Fin`.** Let `P` be a
property of étale objects of `X` whose generators `j_{U!}\underline{\Lambda}_U` are constructible,
and let `q` be a map from a direct sum of such generators over an arbitrary index set to `Z` such
that `q ≫ p` is an epimorphism onto a constructible sheaf `H`. Then `p` is refined by a map from a
*finite* direct sum of such generators.

A finite subsum is already surjective, by
`AlgebraicGeometry.exists_finset_epi_sigma_desc_of_isConstructibleModuleSheaf`; reindexing that
finite subset by `Fin` of its cardinality puts the result in the shape the presentations use. -/
private theorem exists_finite_epi_comp_sigma_moduleShriekConstant_of_epi
    (P : SmallEtale B X.1 X.property → Prop)
    (hP : ∀ U : SmallEtale B X.1 X.property, P U →
      IsConstructibleModuleSheaf B X Λ (moduleShriekConstant.{u, r, r} B X Λ U))
    {H Z : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max (u + 1) r} Λ)}
    (p : Z ⟶ H) (hH : IsConstructibleModuleSheaf B X Λ H)
    {A : Type max (u + 1) r} (U : A → SmallEtale B X.1 X.property) (hU : ∀ a, P (U a))
    (q : (∐ fun a => moduleShriekConstant.{u, r, r} B X Λ (U a)) ⟶ Z) [Epi (q ≫ p)] :
    ∃ (n : ℕ) (V : Fin n → SmallEtale B X.1 X.property), (∀ i, P (V i)) ∧
      ∃ f : (∐ fun i : Fin n => moduleShriekConstant.{u, r, r} B X Λ (V i)) ⟶ Z,
        Epi (f ≫ p) := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_epi_sigma_desc_of_isConstructibleModuleSheaf B X Λ H
    (fun a => moduleShriekConstant.{u, r, r} B X Λ (U a)) (q ≫ p) (fun a => hP _ (hU a)) hH
  refine ⟨s.card, fun i => U (s.equivFin.symm i).1.as, fun i => hU _,
    (Sigma.reindex s.equivFin.symm
        (fun a : {a // a ∈ s} =>
          moduleShriekConstant.{u, r, r} B X Λ (U a.1.as))).hom ≫
      (Sigma.desc fun a : {a // a ∈ s} =>
        Sigma.ι (fun a => moduleShriekConstant.{u, r, r} B X Λ (U a)) a.1.as) ≫ q, ?_⟩
  have := hs
  rw [Category.assoc, Category.assoc]
  infer_instance

/-- **From a presentation by arbitrarily many generators to a finite one.** Let `P` be a property
of étale objects of `X` whose generators `j_{U!}\underline{\Lambda}_U` are constructible. A
constructible sheaf of `Λ`-modules which is a quotient of a direct sum of those generators over an
arbitrary index set is a quotient of a *finite* direct sum of them. -/
private theorem exists_finite_epi_sigma_moduleShriekConstant_of_exists_epi
    (P : SmallEtale B X.1 X.property → Prop)
    (hP : ∀ U : SmallEtale B X.1 X.property, P U →
      IsConstructibleModuleSheaf B X Λ (moduleShriekConstant.{u, r, r} B X Λ U))
    (G : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max (u + 1) r} Λ))
    (hG : IsConstructibleModuleSheaf B X Λ G)
    (hpres : ∃ (A : Type max (u + 1) r) (U : A → SmallEtale B X.1 X.property), (∀ a, P (U a)) ∧
      ∃ p : (∐ fun a => moduleShriekConstant.{u, r, r} B X Λ (U a)) ⟶ G, Epi p) :
    ∃ (n : ℕ) (U : Fin n → SmallEtale B X.1 X.property), (∀ i, P (U i)) ∧
      ∃ p : (∐ fun i => moduleShriekConstant.{u, r, r} B X Λ (U i)) ⟶ G, Epi p := by
  obtain ⟨A, U, hU, Ψ, hΨ⟩ := hpres
  have : Epi (Ψ ≫ 𝟙 G) := by simpa
  obtain ⟨n, V, hV, f, hf⟩ :=
    exists_finite_epi_comp_sigma_moduleShriekConstant_of_epi B X Λ P hP (𝟙 G) hG U hU Ψ
  exact ⟨n, V, hV, f, by simpa using hf⟩
attribute [local instance] smallEtaleHasSheafifyModuleMax

/-- The small étale site of `X` with the *affine* étale objects of `X` as its distinguished
collection of objects. -/
private def affineObjectsSituation :
    Stacks.QuasiCompactObjectsSituation (SmallEtale B X.1 X.property) where
  topology := SmallEtale.topology B X.1 X.property
  objects := {U | SmallEtale.IsAffine B X.1 X.property U}

omit [CompactSpace X.1] [QuasiSeparatedSpace X.1] in
/-- **The affine étale objects cover every étale object of `X`.** The covering of an étale object
by its affine opens lying over affine opens of `X`,
`AlgebraicGeometry.SmallEtale.affineSubordinateCover`, has affine members. -/
private theorem hasEnoughObjects_affineObjectsSituation :
    (affineObjectsSituation B X).HasEnoughObjects := fun U =>
  ⟨SmallEtale.affineSubordinateCover B X.1 X.property U,
    SmallEtale.mem_topology_sieve₀_affineSubordinateCover B X.1 X.property U,
    fun i => i.down.1.2⟩

omit [IsNoetherianRing Λ] [CompactSpace X.1] [QuasiSeparatedSpace X.1] in
/-- **Stacks 093B part (2) for sheaves of `Λ`-modules, generation by affine étale objects.**
Every sheaf of `Λ`-modules on the small étale site of `X` is a quotient of a direct sum
`⊕ j_{U_a!}\underline{\Lambda}_{U_a}` of extensions by zero of constant free rank-one module
sheaves at *affine* étale objects `U_a` of `X`.

This is `AlgebraicGeometry.exists_epi_sigma_moduleShriekConstant_qcqs` with the distinguished
collection of the source taken to be the affine étale objects rather than the quasi-compact
quasi-separated ones; they cover every étale object just as well. -/
@[stacks 093B "part (2), sheaves of modules, generation by affine étale objects"]
public theorem exists_epi_sigma_moduleShriekConstant_affine
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max (u + 1) r} Λ)) :
    ∃ (A : Type max (u + 1) r) (U : A → SmallEtale B X.1 X.property),
      (∀ a, SmallEtale.IsAffine B X.1 X.property (U a)) ∧
        ∃ p : (∐ fun a => moduleShriekConstant.{u, r, r} B X Λ (U a)) ⟶ F, Epi p :=
  Sheaf.exists_epi_sigma_of_coyonedaSections.{u, u + 1, r, r} (affineObjectsSituation B X)
    (hasEnoughObjects_affineObjectsSituation B X) Λ
    (fun U => moduleShriekConstant.{u, r, r} B X Λ U)
    (fun U => moduleShriekConstantCoyonedaIso.{u, r, r} B X Λ U) F

/-- **The finite affine shriek sums cover epimorphisms onto constructible sheaves of
`Λ`-modules.** Let `X` be a quasi-compact and quasi-separated scheme, let `Λ` be a Noetherian
ring, and let `p : Z ⟶ H` be an epimorphism of sheaves of `Λ`-modules onto a *constructible* one.
Then `p` is refined by a *finite* direct sum of extensions by zero of constant free rank-one
module sheaves at affine étale objects: there is a map `f` from such a sum to `Z` with `f ≫ p`
again an epimorphism.

This is Stacks 093B part (2) followed by the finite generation step of the proof of Stacks 095N.
The source `Z` is presented by a direct sum of affine shriek constants over a possibly infinite
index set, `AlgebraicGeometry.exists_epi_sigma_moduleShriekConstant_affine`, whose composite with
`p` is again an epimorphism onto `H`; since `H` is constructible, finitely many of those summands
already suffice, by
`AlgebraicGeometry.exists_finset_epi_sigma_desc_of_isConstructibleModuleSheaf`, and the finite
subset is reindexed by `Fin` of its cardinality.

The constructibility of the generators is Stacks 03S8 for sheaves of modules,
`AlgebraicGeometry.isConstructibleModuleSheaf_moduleShriekConstant`, which holds at this ring
universe; an affine object of the small étale site is quasi-compact and quasi-separated, which is
what that statement asks of it. Nothing is assumed. -/
@[sga "4 IX 2.9" "(ii)"]
public theorem exists_finite_epi_comp_sigma_moduleShriekConstant_affine
    {H Z : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max (u + 1) r} Λ)}
    (p : Z ⟶ H) [Epi p] (hH : IsConstructibleModuleSheaf B X Λ H) :
    ∃ (n : ℕ) (V : Fin n → SmallEtale B X.1 X.property),
      (∀ i, SmallEtale.IsAffine B X.1 X.property (V i)) ∧
        ∃ f : (∐ fun i : Fin n => moduleShriekConstant.{u, r, r} B X Λ (V i)) ⟶ Z,
          Epi (f ≫ p) := by
  obtain ⟨A, U, hU, q, hq⟩ := exists_epi_sigma_moduleShriekConstant_affine B X Λ Z
  have : Epi (q ≫ p) := epi_comp _ _
  exact exists_finite_epi_comp_sigma_moduleShriekConstant_of_epi B X Λ _
    (isConstructibleModuleSheaf_moduleShriekConstant_of_isAffine B X Λ) p hH U hU q

end GeneralRing

section SelfRing

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type (u + 1)) [CommRing Λ]
  [IsNoetherianRing Λ] [CompactSpace X.1] [QuasiSeparatedSpace X.1]

attribute [local instance] smallEtaleHasSheafifyModuleMax

omit [IsNoetherianRing Λ] in
/-- **Stacks 03S8 for sheaves of modules, in the shape the presentations use it.** The extension
by zero of a constant free rank-one module sheaf at a quasi-compact quasi-separated étale object
is constructible. This is
`AlgebraicGeometry.isConstructibleModuleSheaf_moduleShriekConstant` with the two space-level
hypotheses taken as a conjunction rather than as instances. -/
@[sga "4 IX 2.9" "(ii), special case"]
private theorem isConstructibleModuleSheaf_moduleShriekConstant_qcqs
    (U : SmallEtale B X.1 X.property)
    (hU : CompactSpace ((SmallEtale.toScheme B X.1 X.property).obj U) ∧
      QuasiSeparatedSpace ((SmallEtale.toScheme B X.1 X.property).obj U)) :
    IsConstructibleModuleSheaf B X Λ (moduleShriekConstant.{u, u + 1, u + 1} B X Λ U) :=
  isConstructibleModuleSheaf_moduleShriekConstant_of_compact_of_quasiSeparated B X Λ U hU
/-- **The finite generation step of the proof of Stacks 095N.** Let `X` be a quasi-compact and
quasi-separated scheme and `Λ` a Noetherian ring. A constructible sheaf of `Λ`-modules on
`X_étale` is a quotient of a *finite* direct sum of extensions by zero of constant free rank-one
module sheaves at quasi-compact quasi-separated objects of `X_étale`.

Stacks 093B (2) presents the sheaf as a quotient of a direct sum of such sheaves over a possibly
infinite index set, `AlgebraicGeometry.exists_epi_sigma_moduleShriekConstant_qcqs`, and the
summands are constructible by Stacks 03S8 for modules. -/
@[sga "4 IX 2.9" "(ii)"]
public theorem exists_finite_epi_sigma_moduleShriekConstant_of_isConstructibleModuleSheaf
    (G : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} Λ))
    (hG : IsConstructibleModuleSheaf B X Λ G) :
    ∃ (n : ℕ) (U : Fin n → SmallEtale B X.1 X.property),
      (∀ i, CompactSpace ((SmallEtale.toScheme B X.1 X.property).obj (U i)) ∧
          QuasiSeparatedSpace ((SmallEtale.toScheme B X.1 X.property).obj (U i))) ∧
        ∃ p : (∐ fun i => moduleShriekConstant.{u, u + 1, u + 1} B X Λ (U i)) ⟶ G, Epi p :=
  exists_finite_epi_sigma_moduleShriekConstant_of_exists_epi B X Λ _
    (isConstructibleModuleSheaf_moduleShriekConstant_qcqs B X Λ) G hG
    (exists_epi_sigma_moduleShriekConstant_qcqs B X Λ G)
/-- **The finite generation step of the proof of Stacks 095N, at affine objects.** Let `X` be a
quasi-compact and quasi-separated scheme and `Λ` a Noetherian ring. A constructible sheaf of
`Λ`-modules on `X_étale` is a quotient of a *finite* direct sum of extensions by zero of constant
free rank-one module sheaves at *affine* objects of `X_étale`. -/
@[sga "4 IX 2.9" "(ii)"]
public theorem exists_finite_epi_sigma_moduleShriekConstant_affine_of_isConstructibleModuleSheaf
    (G : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} Λ))
    (hG : IsConstructibleModuleSheaf B X Λ G) :
    ∃ (n : ℕ) (U : Fin n → SmallEtale B X.1 X.property),
      (∀ i, SmallEtale.IsAffine B X.1 X.property (U i)) ∧
        ∃ p : (∐ fun i => moduleShriekConstant.{u, u + 1, u + 1} B X Λ (U i)) ⟶ G, Epi p :=
  exists_finite_epi_sigma_moduleShriekConstant_of_exists_epi B X Λ _
    (isConstructibleModuleSheaf_moduleShriekConstant_of_isAffine B X Λ) G hG
    (exists_epi_sigma_moduleShriekConstant_affine B X Λ G)

/-- **Stacks 095N, the quasi-compact quasi-separated presentation.** Let `X` be a quasi-compact and
quasi-separated scheme and `Λ` a Noetherian ring. A sheaf of `Λ`-modules on `X_étale` is
constructible exactly when it is the cokernel of a map between finite direct sums of extensions by
zero of constant free rank-one module sheaves at quasi-compact and quasi-separated objects of
`X_étale`.

Nothing is granted. The two inputs of
`AlgebraicGeometry.isConstructibleModuleSheaf_iff_hasFiniteShriekPresentation` are discharged:
constructibility of the generators is
`AlgebraicGeometry.isConstructibleModuleSheaf_moduleShriekConstant` (Stacks 03S8 for modules) and
the finite generation step of the proof is
`AlgebraicGeometry.exists_finite_epi_sigma_moduleShriekConstant_of_isConstructibleModuleSheaf`.
This theorem and the affine one below carry the registration of 095N; the assembly steps with
those inputs as arguments carry none. -/
@[stacks 095N "quasi-compact quasi-separated presentation",
  sga "4 IX 2.7" "special case",
  sga "4 IX 2.9" "(ii)"]
public theorem isConstructibleModuleSheaf_iff_qcqsShriekPresentation
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} Λ)) :
    IsConstructibleModuleSheaf B X Λ F ↔
      HasFiniteShriekPresentation.{u, u + 1, u + 1} B X Λ
        (fun W ↦ CompactSpace ((SmallEtale.toScheme B X.1 X.property).obj W) ∧
          QuasiSeparatedSpace ((SmallEtale.toScheme B X.1 X.property).obj W)) F :=
  isConstructibleModuleSheaf_iff_hasFiniteShriekPresentation B X Λ
    (fun U hc hq => isConstructibleModuleSheaf_moduleShriekConstant_qcqs B X Λ U ⟨hc, hq⟩)
    (exists_finite_epi_sigma_moduleShriekConstant_of_isConstructibleModuleSheaf B X Λ) F

/-- **Stacks 095N, the affine presentation.** Let `X` be a quasi-compact and quasi-separated
scheme and `Λ` a Noetherian ring. A sheaf of `Λ`-modules on `X_étale` is constructible exactly
when it is the cokernel of a map between finite direct sums of extensions by zero of constant free
rank-one module sheaves at *affine* objects of `X_étale`.

Nothing is granted: this is
`AlgebraicGeometry.isConstructibleModuleSheaf_iff_affineShriekPresentation_of_gen` with its
hypothesis discharged by the affine form of the finite generation step proved just above. -/
@[stacks 095N "affine presentation", sga "4 IX 2.7" "Module sheaves", sga "4 IX 2.9" "(ii)"]
public theorem isConstructibleModuleSheaf_iff_hasFiniteAffineShriekPresentation
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} Λ)) :
    IsConstructibleModuleSheaf B X Λ F ↔
      HasFiniteShriekPresentation.{u, u + 1, u + 1} B X Λ
        (SmallEtale.IsAffine B X.1 X.property) F :=
  isConstructibleModuleSheaf_iff_affineShriekPresentation_of_gen B X Λ
    (exists_finite_epi_sigma_moduleShriekConstant_affine_of_isConstructibleModuleSheaf B X Λ) F
end SelfRing


end AlgebraicGeometry

end
