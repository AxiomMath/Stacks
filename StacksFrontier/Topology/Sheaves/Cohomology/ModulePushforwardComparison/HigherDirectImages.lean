module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionOfRightDerivedFunctors
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.SheafifiedCohomologyPresheaf
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.LocalizationComparison
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksCore.Tactic.StacksAttribute

/-!
# Higher direct images of a sheaf of modules and of its underlying abelian sheaf

Let `f : X ⟶ Y` be a morphism of ringed spaces.  A sheaf of `𝒪_X`-modules has higher direct
images computed in two ways: push forward in sheaves of modules and derive there, forgetting
the module structure only at the end, or forget the coefficient sheaf to a sheaf of abelian
groups first and derive the pushforward of abelian sheaves.  This is Stacks Tag 01F1 part (2);
part (1), the comparison for sections over an open subset, is
`Stacks.Cohomology.ModuleComparison.rightDerivedSectionsForgetIso`.

## Main results

* `modulePushforwardCompToSheafIso`: pushing modules forward and then forgetting *is*
  forgetting and then pushing abelian sheaves forward; the two functors are definitionally
  equal.
* `rightDerivedModulePushforwardCompIso`: deriving the module pushforward and then forgetting
  agrees with deriving the composite `𝒪_X`-modules `⥤` abelian sheaves on `Y`.  This is the
  canonical half of part (2); no choices are involved.
* `rightAcyclic_sections_toSheaf_obj_of_injective`: the underlying abelian sheaf of an injective
  sheaf of modules is acyclic for sections over every open subset.
* `rightAcyclic_abelianPushforward_toSheaf_obj_of_injective`: it is acyclic for the abelian
  pushforward.
* `rightDerivedToSheafAbelianPushforwardIso`: the forgetful functor commutes with deriving the
  abelian pushforward — the `Sheaf`-valued analogue of Tag 03FD.
* `rightDerived_modulePushforward_forget_iso` is Tag 01F1 part (2) itself, and
  `rightDerived_modulePushforward_forget_iso_zero` normalizes it in degree zero.

## Implementation notes

Write `T = SheafOfModules.toSheaf (structureSheafRing X)`,
`S = SheafOfModules.toSheaf (structureSheafRing Y)`, `E = modulePushforward f` and `A` for the
pushforward of abelian sheaves along `opensMap f`. Part (2) of the tag asks for
`E.rightDerived n ⋙ S ≅ T ⋙ A.rightDerived n`.  It factors as

`E.rightDerived n ⋙ S ≅ (E ⋙ S).rightDerived n = (T ⋙ A).rightDerived n ≅ T ⋙ A.rightDerived n`.

The first isomorphism is `rightDerivedCompIso` of part (1) — an exact functor commutes with
right derived functors — applied to the exact forgetful functor `S`; the middle equality is
`modulePushforwardCompToSheafIso`.

The third isomorphism is the statement that `T` commutes with deriving `A`.  It is *not* an
instance of Tag 03FD (`ModuleSheafCohomology.moduleSheafCohomologyIsoUnderlying`): the δ-functor
engine proving 03FD realizes its comparison through `Ext` groups, so
`ModuleSheafCohomology.represented_succ_comparison` requires the functor being derived to be
`AddCommGrpCat`-valued and corepresentable, whereas `A` is valued in a category of sheaves.  It
is obtained instead from Stacks 015M, `Functor.isIso_iff_rightAcyclic_obj_injective`: the
canonical comparison `R(A ∘ T) ⟶ RA ∘ RT` of bounded below derived functors is invertible
exactly when `T` carries injective objects to `A`-acyclic ones, and `RT` is `T` itself because
`T` is exact (`Stacks.Cohomology.HigherDirectImage.isIso_rightDerivedFunctorPlusUnit`).

The acyclicity input is the content proved here.  Tag 03FD *is* used, but only for its
vanishing consequence: it identifies `Hⁿ(U, T I)` with the cohomology of `I` computed in sheaves
of modules, which vanishes in positive degree on an injective object, so `T I` is acyclic for
sections over every open subset.  Stacks 05T8 (`Functor.le_rightAcyclic`) then upgrades this to
acyclicity for `A`, the adapted class being `sectionsAcyclic`, the abelian sheaves acyclic for
all the sections functors: it is closed under quotients by Stacks 015D, and the abelian
pushforward of a short exact sequence of such sheaves stays short exact because it is
sectionwise the sequence of sections over the inverse image, hence epi on underlying presheaves,
and sheafification preserves epimorphisms.  Only the existence form of 03FD is needed, since
only a vanishing is extracted from it.

In degree zero the comparison is defined to be the canonical one coming from left exactness of
the two pushforwards, which is what makes `rightDerived_modulePushforward_forget_iso_zero` hold
by construction.

The cocycle characterization of the comparison is
`Stacks.Cohomology.ModuleComparison.rightDerivedSectionsForgetIso_cocycles`.

## References

* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cohomology.ModulePushforwardComparison

/-! ### Exactness of the forgetful functor to abelian sheaves -/

section ToSheafExact

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})

/-- The forgetful functor from sheaves of `R`-modules to sheaves of abelian groups preserves
finite colimits: both categories compute colimits by sheafifying the colimit of the underlying
presheaves, and `toSheaf` commutes with that.  Concretely, sheafification of presheaves of
modules is a left adjoint, hence preserves all colimits, the counit of its adjunction with the
forgetful functor is an isomorphism, and `sheafificationCompToSheaf` identifies sheafification
followed by `toSheaf` with a composite of two colimit-preserving functors. -/
noncomputable instance toSheaf_preservesFiniteColimits :
    PreservesFiniteColimits (SheafOfModules.toSheaf.{u} R) := by
  let sheafification := PresheafOfModules.sheafification (𝟙 R.obj)
  let adjunction := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  let counitIso := asIso adjunction.counit
  have composite : PreservesFiniteColimits (sheafification ⋙ SheafOfModules.toSheaf R) :=
    preservesFiniteColimits_of_natIso
      (PresheafOfModules.sheafificationCompToSheaf (𝟙 R.obj)).symm
  let _ : PreservesColimitsOfSize.{0, 0} sheafification :=
    adjunction.leftAdjoint_preservesColimits
  refine ⟨fun {index} _ _ => ⟨fun {diagram} => ?_⟩⟩
  let forgetful := SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)
  have comparison : (diagram ⋙ forgetful) ⋙ sheafification ≅ diagram :=
    NatIso.ofComponents (fun point => counitIso.app (diagram.obj point)) fun map =>
      counitIso.hom.naturality (diagram.map map)
  have : PreservesColimit (diagram ⋙ forgetful)
      (sheafification ⋙ SheafOfModules.toSheaf R) :=
    (composite.preservesFiniteColimits index).preservesColimit
  have : PreservesColimit ((diagram ⋙ forgetful) ⋙ sheafification)
      (SheafOfModules.toSheaf R) :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves sheafification (colimit.isColimit (diagram ⋙ forgetful)))
      (isColimitOfPreserves (sheafification ⋙ SheafOfModules.toSheaf R)
        (colimit.isColimit (diagram ⋙ forgetful)))
  exact preservesColimit_of_iso_diagram _ comparison

end ToSheafExact

/-! ### The two pushforward functors -/

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- Pushforward of abelian sheaves along the map of sites underlying a morphism of ringed
spaces is additive: it is given by precomposition of the underlying presheaf with
`(opensMap f).op`, so addition of morphisms is unchanged. -/
instance abelianPushforward_additive :
    ((opensMap f).sheafPushforwardContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology Y.carrier)
      (Opens.grothendieckTopology X.carrier)).Additive where
  map_add := by intros; rfl

/-- **Pushing modules forward and then forgetting is forgetting and then pushing abelian
sheaves forward.**  The two functors are definitionally equal: `SheafOfModules.pushforward`
is `PresheafOfModules.pushforward` of the underlying presheaf of modules followed by
restriction of scalars, so the underlying presheaf of abelian groups of `f_* M` is literally
`V ↦ M(f⁻¹V)`, which is the abelian pushforward of the underlying presheaf of `M`. -/
@[sga "4 IV 11.2.3" "special case"]
noncomputable def modulePushforwardCompToSheafIso :
    modulePushforward f ⋙ SheafOfModules.toSheaf (structureSheafRing Y) ≅
      SheafOfModules.toSheaf (structureSheafRing X) ⋙
        (opensMap f).sheafPushforwardContinuous AddCommGrpCat.{u}
          (Opens.grothendieckTopology Y.carrier)
          (Opens.grothendieckTopology X.carrier) :=
  Iso.refl _

/-- **The canonical half of Stacks 01F1 part (2).**  Deriving the pushforward of sheaves of
modules and then forgetting the module structure agrees with deriving the composite functor
from sheaves of `𝒪_X`-modules to sheaves of abelian groups on `Y`, naturally in the module
sheaf.  This is `rightDerivedCompIso` for the exact forgetful functor
`SheafOfModules.toSheaf (structureSheafRing Y)`, transported along
`modulePushforwardCompToSheafIso`. -/
noncomputable def rightDerivedModulePushforwardCompIso (n : ℕ) :
    (modulePushforward f).rightDerived n ⋙ SheafOfModules.toSheaf (structureSheafRing Y) ≅
      (SheafOfModules.toSheaf (structureSheafRing X) ⋙
        (opensMap f).sheafPushforwardContinuous AddCommGrpCat.{u}
          (Opens.grothendieckTopology Y.carrier)
          (Opens.grothendieckTopology X.carrier)).rightDerived n :=
  ModuleComparison.rightDerivedCompIso _ _ _ (modulePushforwardCompToSheafIso f) n

/-! ### Acyclicity of the underlying abelian sheaf of an injective sheaf of modules -/

section Acyclicity

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

open Stacks.Cohomology.HigherDirectImagePresheaf in
/-- **The underlying abelian sheaf of an injective sheaf of modules is acyclic for sections
over every open.**  By Tag 03FD the cohomology of the underlying abelian sheaf over `U` is the
cohomology of the module sheaf computed in sheaves of modules, which vanishes in positive
degree on an injective object.  Acyclicity in the sense of Stacks 0157 then follows from
Stacks 015C part (2), sections over an open being left exact. -/
theorem rightAcyclic_sections_toSheaf_obj_of_injective (U : Opens X.carrier)
    (M : SheafOfModules.{u} (structureSheafRing X)) (hM : Injective M) :
    ((sheafSections (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).obj
        (op U)).rightAcyclic ((SheafOfModules.toSheaf (structureSheafRing X)).obj M) := by
  have := hM
  refine ((Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus
    ((sheafSections (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).obj (op U))
    _).2 inferInstance).2 ?_
  intro i hi
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = ((n + 1 : ℕ) : ℤ) := ⟨(i - 1).toNat, by omega⟩
  refine IsZero.of_iso ?_ ((derivedPlusToStandard _ (n + 1)).app _)
  refine IsZero.of_iso
    (Functor.isZero_rightDerived_obj_injective_succ
      (SheafOfModules.toSheaf (structureSheafRing X) ⋙
        (sheafSections (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).obj (op U))
      n M)
    ((ModuleComparison.underlyingSectionsIso (structureSheafRing X) U (n + 1)).app M).symm

/-- The adjunction `f^{-1} ⊣ f_*` between the categories of abelian sheaves on `Y` and on `X`
attached to the continuous map of sites underlying a morphism of ringed spaces. -/
noncomputable def abelianPushforwardAdjunction :
    (opensMap f).sheafPullback AddCommGrpCat.{u}
        (Opens.grothendieckTopology Y.carrier) (Opens.grothendieckTopology X.carrier) ⊣
      (opensMap f).sheafPushforwardContinuous AddCommGrpCat.{u}
        (Opens.grothendieckTopology Y.carrier) (Opens.grothendieckTopology X.carrier) :=
  (opensMap f).sheafAdjunctionContinuous AddCommGrpCat.{u} _ _

/-- The abelian pushforward is left exact: it is a right adjoint. -/
noncomputable instance abelianPushforward_preservesFiniteLimits :
    PreservesFiniteLimits ((opensMap f).sheafPushforwardContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology Y.carrier)
      (Opens.grothendieckTopology X.carrier)) := by
  have := (abelianPushforwardAdjunction f).rightAdjoint_preservesLimits
  infer_instance

/-- The class of abelian sheaves on `X` that are acyclic for taking sections over every open
subset.  This is the adapted class of Stacks 05T8 used to establish acyclicity for the abelian
pushforward. -/
def sectionsAcyclic (Z : RingedSpace.{u, u}) :
    ObjectProperty (Sheaf (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}) :=
  fun F => ∀ U : Opens Z.carrier,
    ((sheafSections (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}).obj
      (op U)).rightAcyclic F

/-- **An injective object is right acyclic for every additive functor.**  Right acyclicity is
invertibility of the derived-functor unit at the complex `I[0]`, and that complex is a bounded
below complex of injective objects, so it computes the right derived functor. -/
theorem rightAcyclic_of_injective {A B : Type*} [Category* A] [Category* B] [Abelian A]
    [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B] (F : A ⥤ B) [F.Additive]
    [EnoughInjectives A] (M : A) (hM : Injective M) : F.rightAcyclic M := by
  have : ∀ m : ℤ, Injective (((HomotopyCategory.Plus.singleFunctor A 0).obj M).obj.as.X m) := by
    intro m
    have := hM
    exact inferInstanceAs
      (Injective (((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj M).X m))
  show IsIso _
  infer_instance

/-- Every abelian sheaf embeds into one that is acyclic for sections over every open: embed it
into an injective sheaf, which is acyclic for every additive functor. -/
theorem exists_mono_sectionsAcyclic
    (F : Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) :
    ∃ (G : Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})
      (_ : sectionsAcyclic X G) (i : F ⟶ G), Mono i :=
  ⟨Injective.under F,
    fun _ => rightAcyclic_of_injective _ _ (Injective.injective_under F),
    Injective.ι F, inferInstance⟩

/-- A morphism of abelian sheaves on `X` whose abelian pushforward is an epimorphism on sections
over every open of `Y` has an epimorphic pushforward. -/
theorem epi_sheafPushforwardContinuous_map_of_epi_app
    {F G : Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}} (g : F ⟶ G)
    (h : ∀ V : (Opens Y.carrier)ᵒᵖ,
      Epi (((sheafToPresheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}).map
        (((opensMap f).sheafPushforwardContinuous AddCommGrpCat.{u}
          (Opens.grothendieckTopology Y.carrier)
          (Opens.grothendieckTopology X.carrier)).map g)).app V)) :
    Epi (((opensMap f).sheafPushforwardContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology Y.carrier)
      (Opens.grothendieckTopology X.carrier)).map g) := by
  have hR : Epi ((sheafToPresheaf (Opens.grothendieckTopology Y.carrier)
      AddCommGrpCat.{u}).map (((opensMap f).sheafPushforwardContinuous AddCommGrpCat.{u}
        (Opens.grothendieckTopology Y.carrier)
        (Opens.grothendieckTopology X.carrier)).map g)) :=
    NatTrans.epi_of_epi_app _
  have hL : Epi ((presheafToSheaf (Opens.grothendieckTopology Y.carrier)
      AddCommGrpCat.{u}).map
        ((sheafToPresheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}).map
          (((opensMap f).sheafPushforwardContinuous AddCommGrpCat.{u}
            (Opens.grothendieckTopology Y.carrier)
            (Opens.grothendieckTopology X.carrier)).map g))) := inferInstance
  have hcomp : Epi (((sheafToPresheaf (Opens.grothendieckTopology Y.carrier)
        AddCommGrpCat.{u} ⋙
      presheafToSheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}).map
        (((opensMap f).sheafPushforwardContinuous AddCommGrpCat.{u}
          (Opens.grothendieckTopology Y.carrier)
          (Opens.grothendieckTopology X.carrier)).map g)) ≫
      (sheafificationAdjunction (Opens.grothendieckTopology Y.carrier)
        AddCommGrpCat.{u}).counit.app _) := by
    rw [Functor.comp_map]
    exact epi_comp _ _
  have hnat : (sheafificationAdjunction (Opens.grothendieckTopology Y.carrier)
        AddCommGrpCat.{u}).counit.app _ ≫
        ((opensMap f).sheafPushforwardContinuous AddCommGrpCat.{u}
          (Opens.grothendieckTopology Y.carrier)
          (Opens.grothendieckTopology X.carrier)).map g =
      (sheafToPresheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u} ⋙
        presheafToSheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}).map
          (((opensMap f).sheafPushforwardContinuous AddCommGrpCat.{u}
            (Opens.grothendieckTopology Y.carrier)
            (Opens.grothendieckTopology X.carrier)).map g) ≫
        (sheafificationAdjunction (Opens.grothendieckTopology Y.carrier)
          AddCommGrpCat.{u}).counit.app _ :=
    ((sheafificationAdjunction (Opens.grothendieckTopology Y.carrier)
      AddCommGrpCat.{u}).counit.naturality _).symm
  have hfac : Epi ((sheafificationAdjunction (Opens.grothendieckTopology Y.carrier)
      AddCommGrpCat.{u}).counit.app _ ≫
      ((opensMap f).sheafPushforwardContinuous AddCommGrpCat.{u}
        (Opens.grothendieckTopology Y.carrier)
        (Opens.grothendieckTopology X.carrier)).map g) := by
    rwa [hnat]
  exact epi_of_epi ((sheafificationAdjunction (Opens.grothendieckTopology Y.carrier)
      AddCommGrpCat.{u}).counit.app _) _

/-- The class of sheaves acyclic for all sections functors is closed under the quotient in a
short exact sequence, and the abelian pushforward of such a short exact sequence remains short
exact.  The first assertion and the exactness of the sections sequences come from Stacks 015D;
the pushforward sequence is short exact because it is sectionwise the sequence of sections over
the inverse image, hence epi on underlying presheaves, and sheafification preserves epimorphisms
while the counit of the sheafification adjunction is invertible on sheaves. -/
theorem sectionsAcyclic_and_shortExact_map_abelianPushforward
    (S : ShortComplex (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}))
    (hS : S.ShortExact) (h₁ : sectionsAcyclic X S.X₁) (h₂ : sectionsAcyclic X S.X₂) :
    sectionsAcyclic X S.X₃ ∧
      (S.map ((opensMap f).sheafPushforwardContinuous AddCommGrpCat.{u}
        (Opens.grothendieckTopology Y.carrier)
        (Opens.grothendieckTopology X.carrier))).ShortExact := by
  have key : ∀ U : Opens X.carrier,
      ((sheafSections (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).obj
            (op U)).rightAcyclic S.X₃ ∧
        (S.map ((sheafSections (Opens.grothendieckTopology X.carrier)
          AddCommGrpCat.{u}).obj (op U))).ShortExact :=
    fun U => (Functor.rightAcyclic_and_shortExact_map_of_shortExact _ S hS).2.1 (h₁ U) (h₂ U)
  refine ⟨fun U => (key U).1, ?_⟩
  have hlex := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    ((opensMap f).sheafPushforwardContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology Y.carrier)
      (Opens.grothendieckTopology X.carrier))).1 inferInstance S hS
  exact
    { exact := hlex.1
      mono_f := hlex.2
      epi_g := epi_sheafPushforwardContinuous_map_of_epi_app f S.g
        fun V => (key ((opensMap f).obj V.unop)).2.epi_g }

/-- **The underlying abelian sheaf of an injective sheaf of modules is acyclic for the abelian
pushforward.**  Stacks 05T8 applies to the class `sectionsAcyclic`, and Tag 03FD puts the
underlying abelian sheaf of an injective sheaf of modules into that class.

This is the acyclicity hypothesis of Stacks 015E and 015M for the pair
`(SheafOfModules.toSheaf (structureSheafRing X), f_*)`. -/
theorem rightAcyclic_abelianPushforward_toSheaf_obj_of_injective
    (M : SheafOfModules.{u} (structureSheafRing X)) (hM : Injective M) :
    ((opensMap f).sheafPushforwardContinuous AddCommGrpCat.{u}
        (Opens.grothendieckTopology Y.carrier)
        (Opens.grothendieckTopology X.carrier)).rightAcyclic
      ((SheafOfModules.toSheaf (structureSheafRing X)).obj M) :=
  Functor.le_rightAcyclic _ (sectionsAcyclic X) exists_mono_sectionsAcyclic
    (fun S hS h₁ h₂ => sectionsAcyclic_and_shortExact_map_abelianPushforward f S hS h₁ h₂) _
    (fun U => rightAcyclic_sections_toSheaf_obj_of_injective U M hM)

/-! ### The forgetful functor commutes with deriving the abelian pushforward -/

/-- The abelian pushforward along `f`, abbreviated for the constructions below. -/
noncomputable abbrev abelianPushforward :
    Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u} :=
  (opensMap f).sheafPushforwardContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology Y.carrier) (Opens.grothendieckTopology X.carrier)

/-- The transformation of Stacks 05T2 for the pair (forget, abelian pushforward), assembled
from the units of the two bounded below right derived functors.  It is the datum that pins the
canonical comparison `R(f_* ∘ forget) ⟶ Rf_* ∘ R(forget)`. -/
noncomputable def derivedCompositionUnit :
    (SheafOfModules.toSheaf (structureSheafRing X) ⋙ abelianPushforward f).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙
        (SheafOfModules.toSheaf (structureSheafRing X)).rightDerivedFunctorPlus ⋙
        (abelianPushforward f).rightDerivedFunctorPlus :=
  Functor.whiskerRight
      (Functor.mapHomotopyCategoryPlusCompIso
        (Iso.refl (SheafOfModules.toSheaf (structureSheafRing X) ⋙
          abelianPushforward f))).inv DerivedCategory.Plus.Qh ≫
    Functor.whiskerLeft (SheafOfModules.toSheaf (structureSheafRing X)).mapHomotopyCategoryPlus
      (abelianPushforward f).rightDerivedFunctorPlusUnith ≫
    Functor.whiskerRight (SheafOfModules.toSheaf (structureSheafRing X)).rightDerivedFunctorPlusUnith
      (abelianPushforward f).rightDerivedFunctorPlus

/-- The canonical comparison `R(f_* ∘ forget) ⟶ Rf_* ∘ R(forget)` of Stacks 05T2, obtained from
the universal property of the right derived functor of the composite. -/
noncomputable def derivedComposition :
    (SheafOfModules.toSheaf (structureSheafRing X) ⋙ abelianPushforward f).rightDerivedFunctorPlus ⟶
      (SheafOfModules.toSheaf (structureSheafRing X)).rightDerivedFunctorPlus ⋙
        (abelianPushforward f).rightDerivedFunctorPlus :=
  Functor.rightDerivedDesc _
    (SheafOfModules.toSheaf (structureSheafRing X) ⋙
      abelianPushforward f).rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso _) _ (derivedCompositionUnit f)

/-- **The canonical comparison is invertible.**  Stacks 015M: it is invertible exactly when the
underlying abelian sheaf of an injective sheaf of modules is acyclic for the abelian
pushforward, which is `rightAcyclic_abelianPushforward_toSheaf_obj_of_injective`. -/
instance isIso_derivedComposition : IsIso (derivedComposition f) :=
  (Functor.isIso_iff_rightAcyclic_obj_injective _ _ (derivedComposition f)
    (Functor.rightDerived_fac _ _ _ _ _)).2
    fun M hM => rightAcyclic_abelianPushforward_toSheaf_obj_of_injective f M hM

/-- Since the forgetful functor to abelian sheaves is exact, its bounded below right derived
functor carries a sheaf of modules placed in degree zero to its underlying abelian sheaf placed
in degree zero. -/
noncomputable def toSheafSingleFunctorIso :
    DerivedCategory.Plus.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0 ⋙
        (SheafOfModules.toSheaf (structureSheafRing X)).rightDerivedFunctorPlus ≅
      SheafOfModules.toSheaf (structureSheafRing X) ⋙
        DerivedCategory.Plus.singleFunctor
          (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) 0 :=
  have : IsIso (SheafOfModules.toSheaf (structureSheafRing X)).rightDerivedFunctorPlusUnith :=
    Stacks.Cohomology.HigherDirectImage.isIso_rightDerivedFunctorPlusUnit _
  Functor.isoWhiskerRight (Functor.singleFunctorPlusIsoCompQh 0)
      (SheafOfModules.toSheaf (structureSheafRing X)).rightDerivedFunctorPlus ≪≫
    Functor.isoWhiskerLeft
      (HomotopyCategory.Plus.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0)
      (asIso (SheafOfModules.toSheaf (structureSheafRing X)).rightDerivedFunctorPlusUnith).symm ≪≫
    Functor.mapSingleFunctorCompQhIso (SheafOfModules.toSheaf (structureSheafRing X))

/-- **The forgetful functor commutes with deriving the abelian pushforward.**  This is the
`Sheaf`-valued analogue of Tag 03FD, in the shape needed for part (2) of Tag 01F1: the right
derived functors of the composite `Mod(𝒪_X) ⥤ Ab(Y)` are the abelian higher direct images of
the underlying abelian sheaf.  It is obtained from the invertibility of the canonical
comparison of Stacks 015M, together with the identification of the derived functor of the
exact forgetful functor with the functor itself; the passage between the derived-category and
the injective-resolution conventions for `Rⁱ` is `derivedPlusToStandard`. -/
noncomputable def rightDerivedToSheafAbelianPushforwardIso (n : ℕ) :
    (SheafOfModules.toSheaf (structureSheafRing X) ⋙ abelianPushforward f).rightDerived n ≅
      SheafOfModules.toSheaf (structureSheafRing X) ⋙ (abelianPushforward f).rightDerived n :=
  (Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandard
      (SheafOfModules.toSheaf (structureSheafRing X) ⋙ abelianPushforward f) n).symm ≪≫
    Functor.isoWhiskerLeft
        (DerivedCategory.Plus.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0)
        (Functor.isoWhiskerRight (asIso (derivedComposition f))
          (DerivedCategory.Plus.homologyFunctor
            (Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}) (n : ℤ))) ≪≫
    Functor.isoWhiskerRight (toSheafSingleFunctorIso (X := X))
      ((abelianPushforward f).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor
          (Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}) (n : ℤ)) ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.toSheaf (structureSheafRing X))
      (Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandard
        (abelianPushforward f) n)

/-! ### Stacks 01F1, part (2) -/

/-- Pushforward of sheaves of modules along a morphism of ringed spaces is left exact: it is a
right adjoint. -/
noncomputable instance modulePushforward_preservesFiniteLimits :
    PreservesFiniteLimits (modulePushforward f) := by
  have := modulePushforward_isRightAdjoint f
  infer_instance

/-- The comparison of part (2) in degree zero: both sides are canonically the underived
functor, by left exactness of the two pushforwards. -/
noncomputable def rightDerivedModulePushforwardForgetIsoZero :
    (modulePushforward f).rightDerived 0 ⋙ SheafOfModules.toSheaf (structureSheafRing Y) ≅
      SheafOfModules.toSheaf (structureSheafRing X) ⋙
        ((opensMap f).sheafPushforwardContinuous AddCommGrpCat.{u}
          (Opens.grothendieckTopology Y.carrier)
          (Opens.grothendieckTopology X.carrier)).rightDerived 0 :=
  Functor.isoWhiskerRight (modulePushforward f).rightDerivedZeroIsoSelf
      (SheafOfModules.toSheaf (structureSheafRing Y)) ≪≫
    modulePushforwardCompToSheafIso f ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.toSheaf (structureSheafRing X))
      ((opensMap f).sheafPushforwardContinuous AddCommGrpCat.{u}
        (Opens.grothendieckTopology Y.carrier)
        (Opens.grothendieckTopology X.carrier)).rightDerivedZeroIsoSelf.symm

/-- **Stacks 01F1, part (2).**  Higher direct images of a sheaf of modules, computed in sheaves
of modules and then forgotten to abelian sheaves, agree canonically and naturally with the
higher direct images of the underlying abelian sheaf.

In degree zero the isomorphism is the canonical one coming from left exactness of the two
pushforwards, which is what makes `rightDerived_modulePushforward_forget_iso_zero` true; in
positive degree it is `rightDerivedModulePushforwardCompIso` followed by
`rightDerivedToSheafAbelianPushforwardIso`. -/
@[stacks 01F1 "part (2)"]
noncomputable def rightDerived_modulePushforward_forget_iso (n : ℕ) :
    (modulePushforward f).rightDerived n ⋙ SheafOfModules.toSheaf (structureSheafRing Y) ≅
      SheafOfModules.toSheaf (structureSheafRing X) ⋙
        ((opensMap f).sheafPushforwardContinuous AddCommGrpCat.{u}
          (Opens.grothendieckTopology Y.carrier)
          (Opens.grothendieckTopology X.carrier)).rightDerived n :=
  match n with
  | 0 => rightDerivedModulePushforwardForgetIsoZero f
  | m + 1 =>
      rightDerivedModulePushforwardCompIso f (m + 1) ≪≫
        rightDerivedToSheafAbelianPushforwardIso f (m + 1)

/-- **Stacks 01F1, part (2), degree-zero normalization.**  In degree zero the comparison
intertwines the canonical maps from the ordinary pushforwards to the zeroth right derived
functors. -/
@[stacks 01F1 "part (2), degree-zero normalization"]
theorem rightDerived_modulePushforward_forget_iso_zero :
    Functor.whiskerRight (modulePushforward f).toRightDerivedZero
          (SheafOfModules.toSheaf (structureSheafRing Y)) ≫
        (rightDerived_modulePushforward_forget_iso f 0).hom =
      Functor.whiskerLeft (SheafOfModules.toSheaf (structureSheafRing X))
        ((opensMap f).sheafPushforwardContinuous AddCommGrpCat.{u}
          (Opens.grothendieckTopology Y.carrier)
          (Opens.grothendieckTopology X.carrier)).toRightDerivedZero := by
  dsimp only [rightDerived_modulePushforward_forget_iso,
    rightDerivedModulePushforwardForgetIsoZero]
  rw [Iso.trans_hom, Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Iso.symm_hom, Functor.rightDerivedZeroIsoSelf_inv, ← Category.assoc,
    ← Functor.whiskerRight_comp, Functor.rightDerivedZeroIsoSelf_inv_hom_id,
    Functor.whiskerRight_id', Category.id_comp]
  exact Category.id_comp _

end Acyclicity

end Stacks.Cohomology.ModulePushforwardComparison

end
