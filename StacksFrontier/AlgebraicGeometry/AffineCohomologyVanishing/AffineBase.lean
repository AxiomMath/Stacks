module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicPreservesHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.Qcqs
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.BoundedBelowEdgeIsomorphism
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.PushforwardOfAnInjective
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.DerivedSectionsOfAPushforward
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen

/-!
# Cohomology over an affine base

Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes with `S` affine and
let `F` be a quasi-coherent `𝒪_X`-module.  [Stacks, Tag 01XK] asserts

`H^q(X, F) = H^0(S, R^q f_* F)` for every `q ∈ ℤ`.

Since `S` is affine, `H^0(S, −)` is global sections, and the two sides are compared as modules
over `Γ(S, ⊤)`: the left-hand side carries its `Γ(X, ⊤)`-module structure restricted along
`f^♯ : Γ(S, ⊤) ⟶ Γ(X, ⊤)`.  The comparison is natural in the module, so it is stated as an
isomorphism of functors on the full subcategory of quasi-coherent modules.

The source proves this from the Leray spectral sequence of [Stacks, Tag 01F2] together with its
degeneration criterion [Stacks, Tag 01F4]; no spectral sequence is used here.  Instead the
argument is the one [Stacks, Tag 01F4] rests on, run directly: global sections over the affine
base are acyclic on quasi-coherent modules by [Stacks, Tag 01XB], the higher direct images are
quasi-coherent by [Stacks, Tag 01XJ], and the pushforward of an injective module has acyclic
sections by [Stacks, Tag 01EX].  Those three inputs make the Grothendieck comparison for the
composite `Γ(S, ⊤) ∘ f_*` an isomorphism in each degree, and the commutative square of
underived functors `Γ(X, ⊤) ∘ (−) ≅ Γ(S, ⊤) ∘ f_*` of [Stacks, Tag 01EZ] then identifies the
two derived functors.

## Main definitions

* `moduleGlobalSections`: global sections of a sheaf of modules on a scheme, valued in modules
  over the ring of global functions.

## Main results

* `rightDerivedCompNatIso`: Grothendieck's comparison `R^n(G ∘ F) ≅ G ∘ R^n F`, with the
  homology-preservation hypothesis on `G` taken pointwise on the short complexes that occur
  rather than globally.
* `rightAcyclic_moduleGlobalSections`: global sections on an affine scheme are acyclic on
  quasi-coherent modules, which is [Stacks, Tag 01XB] in acyclicity form.
* `affineBaseHigherDirectImageIso`: the comparison in a nonnegative degree, for Mathlib's
  `ℕ`-indexed right derived functors.
* `cohomologyIsoGlobalSectionsRightDerivedPushforward`: **[Stacks, Tag 01XK]**, in every integer
  degree.

## Implementation notes

The three Stacks inputs are consumed in their library spellings and nothing is restated.  The
pushforward side crosses from the ringed-space spelling of [Stacks, Tag 01EZ] to the
scheme-level one: the induced morphism of ringed spaces `asRingedSpaceHom f` satisfies
`opensMap (asRingedSpaceHom f) ⊤ = ⊤`, `structureSheafHom (asRingedSpaceHom f)` at `⊤` is
`f.appTop`, and `modulePushforward (asRingedSpaceHom f)` is `Scheme.Modules.pushforward f`, all
three by `rfl`, so the crossing is made once in `sectionsRestrictionIsoTop` and nowhere else.

Negative degrees are handled separately: both sides vanish there, because a right derived
functor on the bounded below derived category vanishes in negative degrees.  The two indexings
of the higher right derived functors are compared by `Stacks.DerivedIndexing.rightDerivedIso`.

The priority bump via `attribute [local instance 2000]` on
`HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso` follows the precedent of
`StacksFrontier/Algebra/Homology/DerivedCategory/RightDerivedFunctorInjective.lean`: without it the
instance needed merely to *state* `Functor.rightAcyclic` exhausts the instance search budget.

## References

* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped AlgebraicGeometry

namespace Stacks.Cohomology.AffineBase

open RingedSpaceModuleAdjunction

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### Grothendieck's comparison with a pointwise hypothesis -/

section Composition

/-- **Grothendieck's comparison for the `n`-th right derived functor of a composite.** The
homology-preservation hypothesis on `G` is asked only of the short complexes in degree `n` of
the images under `F` of the chosen injective resolutions, rather than of `G` globally, which is
what makes it available when `G` is merely acyclic on the objects that occur. -/
public noncomputable def rightDerivedCompNatIso
    {D A B C : Type*} [Category* D] [Category* A] [Category* B] [Category* C]
    [Abelian A] [Abelian B] [Abelian C] [HasInjectiveResolutions A]
    (E : D ⥤ A) (F : A ⥤ B) (G : B ⥤ C) [instF : F.Additive] [instG : G.Additive] (n : ℕ)
    (h : ∀ X : D, G.PreservesLeftHomologyOf
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (E.obj X)).cocomplex).sc n)) :
    E ⋙ F.rightDerived n ⋙ G ≅ E ⋙ (F ⋙ G).rightDerived n := by
  classical
  refine NatIso.ofComponents
    (fun X => by
      let K := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((injectiveResolutions A).obj (E.obj X)).as
      let _ : G.PreservesLeftHomologyOf (K.sc n) := by
        simpa [K, injectiveResolutions, HomotopyCategory.quotient_obj_as] using h X
      unfold Functor.rightDerived Functor.rightDerivedToHomotopyCategory
        HomotopyCategory.homologyFunctor
      exact (K.sc n).mapHomologyIso G |>.symm) ?_
  intro X Y f
  obtain ⟨g, hg⟩ := (HomotopyCategory.quotient A (ComplexShape.up ℕ)).map_surjective
    ((injectiveResolutions A).map (E.map f))
  let K := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
    ((injectiveResolutions A).obj (E.obj X)).as
  let L := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
    ((injectiveResolutions A).obj (E.obj Y)).as
  let _ : G.PreservesLeftHomologyOf (K.sc n) := by
    simpa [K, injectiveResolutions, HomotopyCategory.quotient_obj_as] using h X
  let _ : G.PreservesLeftHomologyOf (L.sc n) := by
    simpa [L, injectiveResolutions, HomotopyCategory.quotient_obj_as] using h Y
  unfold Functor.rightDerived Functor.rightDerivedToHomotopyCategory
  simp only [Functor.comp_map]
  rw [← hg]
  unfold HomotopyCategory.homologyFunctor
  dsimp [Functor.comp_map, Functor.mapHomotopyCategory, HomologicalComplex.homologyFunctor]
  exact ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor B (ComplexShape.up ℕ) n).map
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map g)) G

end Composition


/-! ### Global sections on a scheme -/

/-- Global sections of sheaves of modules on a scheme, valued in modules over the ring of
global functions. -/
public noncomputable abbrev moduleGlobalSections (X : AlgebraicGeometry.Scheme.{u}) :
    X.Modules ⥤ ModuleCat.{u} Γ(X, ⊤) :=
  SheafOfModules.evaluation X.ringCatSheaf (op ⊤)

/-- Global sections of sheaves of modules on a scheme form an additive functor. -/
public instance moduleGlobalSections_additive (X : AlgebraicGeometry.Scheme.{u}) :
    (moduleGlobalSections X).Additive :=
  inferInstanceAs (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).Additive

/-- Global sections of sheaves of modules on a scheme preserve finite limits. -/
public instance moduleGlobalSections_preservesFiniteLimits
    (X : AlgebraicGeometry.Scheme.{u}) : PreservesFiniteLimits (moduleGlobalSections X) :=
  inferInstanceAs (PreservesFiniteLimits (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)))

/-- A sheaf of modules whose underlying additive group is a zero object is itself a zero
object. -/
public theorem module_isZero_of_forget₂_isZero {R : Type u} [Ring R] (M : ModuleCat.{u} R)
    (h : IsZero ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj M)) : IsZero M := by
  rw [ModuleCat.isZero_iff_subsingleton]
  rwa [AddCommGrpCat.isZero_iff_subsingleton] at h

/-- **Global sections on an affine scheme are acyclic on quasi-coherent modules.** This is
[Stacks, Tag 01XB] read as acyclicity of the module-valued global sections functor: the
positive-degree cohomology groups vanish, and a module with vanishing underlying group
vanishes. -/
public theorem rightAcyclic_moduleGlobalSections (S : AlgebraicGeometry.Scheme.{u})
    [AlgebraicGeometry.IsAffine S] (F : S.Modules) [F.IsQuasicoherent] :
    (moduleGlobalSections S).rightAcyclic F := by
  refine (Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat
    (moduleGlobalSections S) F).2 fun n hn => module_isZero_of_forget₂_isZero _ (IsZero.of_iso
      (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen S F ⊤
        (AlgebraicGeometry.isAffineOpen_top S) n hn)
      ((Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso
        S.ringCatSheaf ⊤ n).app F))

/-! ### The comparison over an affine base -/

section AffineBase

variable {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)

/-- A morphism of schemes as a morphism of the underlying ringed spaces. -/
public noncomputable abbrev asRingedSpaceHom :
    X.toLocallyRingedSpace.toRingedSpace ⟶ S.toLocallyRingedSpace.toRingedSpace :=
  { hom := { base := f.base, c := f.c } }

/-- **[Stacks, Tag 01EZ] over the whole space, at the scheme-level spelling.** Global sections
of a pushforward, with scalars restricted along `f^♯`, are the global sections upstairs. The
ringed-space statement applies on the nose: the inverse image of `⊤` is `⊤`, the structure
morphism at `⊤` is `f.appTop` and the ringed-space pushforward of modules is
`Scheme.Modules.pushforward f`, each by `rfl`. -/
public noncomputable def sectionsRestrictionIsoTop :
    moduleGlobalSections X ⋙ ModuleCat.restrictScalars f.appTop.hom ≅
      AlgebraicGeometry.Scheme.Modules.pushforward f ⋙ moduleGlobalSections S :=
  Stacks.Cohomology.DerivedPushforwardSections.sectionsRestrictionIso (asRingedSpaceHom f) ⊤

variable [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]
  [AlgebraicGeometry.IsAffine S]

/-- **Global sections over the affine base preserve the homology of the pushforward of an
injective resolution.** The terms of that complex are pushforwards of injective modules, hence
have acyclic sections by [Stacks, Tag 01EX]; its homology objects are the higher direct images,
quasi-coherent by [Stacks, Tag 01XJ], hence acyclic by [Stacks, Tag 01XB]. -/
public theorem preservesLeftHomology_pushforward_injectiveResolution
    (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    (moduleGlobalSections S).PreservesLeftHomologyOf
      ((((AlgebraicGeometry.Scheme.Modules.pushforward f).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (injectiveResolution F).cocomplex).sc n) := by
  let P := AlgebraicGeometry.Scheme.Modules.pushforward f
  let T := moduleGlobalSections S
  let I := injectiveResolution F
  let K := (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  have hX : ∀ i, T.rightAcyclic (K.X i) := fun i =>
    @Stacks.Cohomology.PushforwardAcyclic.pushforward_injective_rightAcyclic _ _
      (asRingedSpaceHom f) (I.cocomplex.X i) (I.injective i) ⊤
  have hH : ∀ i, T.rightAcyclic (K.homology i) := fun i =>
    T.rightAcyclic.prop_of_iso (I.isoRightDerivedObj P i)
      (rightAcyclic_moduleGlobalSections S ((P.rightDerived i).obj F))
  exact (T.rightAcyclic_cycles_and_preservesLeftHomologyOf_sc K hX hH n).2

/-- **[Stacks, Tag 01XK] in a nonnegative degree**, for Mathlib's `ℕ`-indexed right derived
functors. The left-hand side is turned into the right derived functor of the composite
`Γ(S, ⊤) ∘ f_*` by [Stacks, Tag 01EZ] together with exactness of restriction of scalars, and
Grothendieck's comparison then splits that composite, its hypothesis being
`preservesLeftHomology_pushforward_injectiveResolution`. -/
public noncomputable def affineBaseHigherDirectImageIso (n : ℕ) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙
        (moduleGlobalSections X).rightDerived n ⋙
        ModuleCat.restrictScalars f.appTop.hom ≅
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙
        (AlgebraicGeometry.Scheme.Modules.pushforward f).rightDerived n ⋙
        moduleGlobalSections S :=
  let R := ModuleCat.restrictScalars.{u} f.appTop.hom
  have _ : R.Additive := ⟨by intros; rfl⟩
  have _ : PreservesFiniteLimits R := ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩
  have _ : PreservesFiniteColimits R := ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩
  have _ : R.PreservesHomology := Functor.preservesHomologyOfExact R
  Functor.isoWhiskerLeft (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι
      (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso (moduleGlobalSections X) R
        (AlgebraicGeometry.Scheme.Modules.pushforward f ⋙ moduleGlobalSections S)
        (sectionsRestrictionIsoTop f) n) ≪≫
    (rightDerivedCompNatIso (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι
      (AlgebraicGeometry.Scheme.Modules.pushforward f) (moduleGlobalSections S)
      (instF := inferInstanceAs (AlgebraicGeometry.Scheme.Modules.pushforward f).Additive) n
      (fun A =>
        have _ : ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.obj A).IsQuasicoherent :=
          A.property
        preservesLeftHomology_pushforward_injectiveResolution f
          ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.obj A) n)).symm

/-- **[Stacks, Tag 01XK].** For a quasi-compact and quasi-separated morphism `f : X ⟶ S` with
affine target, the cohomology of a quasi-coherent module on `X` is naturally isomorphic, as a
module over `Γ(S, ⊤)`, to the global sections of its higher direct image. -/
@[stacks 01XK, ega "III 1.4.14" "affine base, Z=point"]
public noncomputable def cohomologyIsoGlobalSectionsRightDerivedPushforward (q : ℤ) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙
        (moduleGlobalSections X).rightDerivedPlus q ⋙
        ModuleCat.restrictScalars f.appTop.hom ≅
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙
        (AlgebraicGeometry.Scheme.Modules.pushforward f).rightDerivedPlus q ⋙
        moduleGlobalSections S := by
  classical
  let Q := (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι
  let Sx := moduleGlobalSections X
  let P := AlgebraicGeometry.Scheme.Modules.pushforward f
  let T := moduleGlobalSections S
  let R := ModuleCat.restrictScalars.{u} f.appTop.hom
  by_cases hq : 0 ≤ q
  · have hqn : q = (q.toNat : ℤ) := (Int.toNat_of_nonneg hq).symm
    rw [hqn]
    exact Functor.isoWhiskerRight (Functor.isoWhiskerLeft Q
          (Stacks.DerivedIndexing.rightDerivedIso Sx q.toNat).symm) R ≪≫
        affineBaseHigherDirectImageIso f q.toNat ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft Q
        (Stacks.DerivedIndexing.rightDerivedIso P q.toNat)) T
  · refine NatIso.ofComponents (fun A => ?_) (fun {A B} g => ?_)
    · exact IsZero.iso
        (R.map_isZero (CategoryTheory.Functor.isZero_rightDerivedPlus_of_neg
          Sx (Q.obj A) q (by omega)))
        (T.map_isZero (CategoryTheory.Functor.isZero_rightDerivedPlus_of_neg
          P (Q.obj A) q (by omega)))
    · exact (T.map_isZero
        (CategoryTheory.Functor.isZero_rightDerivedPlus_of_neg
          P (Q.obj B) q (by omega))).eq_of_tgt _ _

end AffineBase

end Stacks.Cohomology.AffineBase

end
