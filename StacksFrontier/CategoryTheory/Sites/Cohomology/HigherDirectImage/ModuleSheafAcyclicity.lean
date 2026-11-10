module

public import Mathlib.CategoryTheory.Abelian.ShortExact
public import Mathlib.CategoryTheory.Sites.Adjunction
public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsFromInt
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicObjects
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowExactEquivalence
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.PushforwardVanishingOnACover
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
public import StacksFrontier.Homology.DerivedIndexing.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Higher direct images of sheaves of modules and of their underlying abelian sheaves

Let `R` be a ring and let `(C, J)` be a site. The underlying abelian sheaf of an injective sheaf
of `R`-modules is not injective in general, but it is acyclic for everything cohomology sees: it
has vanishing higher `Ext` out of every sectionwise torsion-free abelian sheaf, because
`R ⊗_ℤ -` is left adjoint to the forgetful functor and preserves the monomorphism of a short
exact sequence with torsion-free quotient. The free abelian sheaves on representable presheaves
are torsion free, so the underlying abelian sheaf of an injective sheaf of modules has vanishing
higher cohomology over every object, and hence vanishing higher direct images along every
continuous functor of sites (the acyclicity input of [Stacks, Tag 03FD]).

Consequently the higher direct images of a sheaf of `R`-modules along a continuous functor are
computed on the underlying abelian sheaves: if the underlying abelian sheaf of `A` is acyclic for
the direct image of abelian sheaves, then `A` is acyclic for the direct image of sheaves of
modules.

## Main definitions

* `Stacks.Cohomology.ModuleSheaf.sheafExtendScalarsFromIntAdj`: the sheafified extension of
  scalars `R ⊗_ℤ -` is left adjoint to the forgetful functor from sheaves of `R`-modules to
  abelian sheaves.

## Main results

* `Stacks.Cohomology.ModuleSheaf.preservesFiniteLimits_sheafCompose_forget₂` and
  `Stacks.Cohomology.ModuleSheaf.preservesFiniteColimits_sheafCompose_forget₂`: the forgetful
  functor from sheaves of `R`-modules to abelian sheaves is exact.
* `Stacks.Cohomology.ModuleSheaf.ext_eq_zero_of_isTorsionFree`: the underlying abelian sheaf of an
  injective sheaf of `R`-modules has vanishing higher `Ext` out of a sectionwise torsion-free
  abelian sheaf.
* `Stacks.Cohomology.ModuleSheaf.rightAcyclic_sheafPushforwardContinuous_of_injective`: it is
  right acyclic for the direct image of abelian sheaves along any continuous functor.
* `Stacks.Cohomology.ModuleSheaf.rightAcyclic_sheafPushforwardContinuous_of_forget₂`: a sheaf of
  `R`-modules whose underlying abelian sheaf is acyclic for the direct image of abelian sheaves is
  acyclic for the direct image of sheaves of `R`-modules.

## Implementation notes

Sheaves of `R`-modules are sheaves with values in `ModuleCat R`, and the coefficient universe is
`max v t r` for a site with morphisms in `Type v` and a ring in `Type r`, so that the free abelian
sheaves on representables live in the same universe as the underlying abelian sheaves. The
`Ext`-vanishing statement holds on any site; the comparison with the right derived functors of
sections over an object is `Stacks.Cohomology.FreeYonedaUnivLE`.

`Stacks.Cohomology.InjectiveModuleSheafAcyclicity` proves the same acyclicity for sheaves of
modules over a sheaf of rings, `SheafOfModules R`; the statements here are for sheaves with values
in `ModuleCat R` over a fixed ring, the coefficients of the étale and pro-étale comparison, and
use extension of scalars from `ℤ` in place of the tensor product with the sheaf of rings.

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe w t r v u v' u'

namespace Stacks.Cohomology.ModuleSheaf

section Exactness

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (R : Type r) [Ring R]
  [HasWeakSheafify J (ModuleCat.{max r t} R)]
  [J.HasSheafCompose (forget₂ (ModuleCat.{max r t} R) AddCommGrpCat.{max r t})]

/-- **The sheafified extension of scalars `R ⊗_ℤ -` is left adjoint to the forgetful functor**
from sheaves of `R`-modules to abelian sheaves. -/
def sheafExtendScalarsFromIntAdj :
    Sheaf.composeAndSheafify J (ModuleCat.extendScalarsFromInt.{t} R) ⊣
      sheafCompose J (forget₂ (ModuleCat.{max r t} R) AddCommGrpCat.{max r t}) :=
  Sheaf.adjunction J (ModuleCat.extendScalarsFromIntAdj.{t} R)

/-- The forgetful functor from sheaves of `R`-modules to abelian sheaves preserves finite limits,
being a right adjoint. -/
theorem preservesFiniteLimits_sheafCompose_forget₂ :
    PreservesFiniteLimits
      (sheafCompose J (forget₂ (ModuleCat.{max r t} R) AddCommGrpCat.{max r t})) :=
  have := (sheafExtendScalarsFromIntAdj J R).isRightAdjoint
  inferInstance

omit [HasWeakSheafify J (ModuleCat.{max r t} R)] in
/-- The forgetful functor from sheaves of `R`-modules to abelian sheaves preserves finite
colimits: it is induced by the forgetful functor of coefficient categories, which is left adjoint
to coextension of scalars from `ℤ` to `R`. -/
theorem preservesFiniteColimits_sheafCompose_forget₂ [HasWeakSheafify J AddCommGrpCat.{max r t}] :
    PreservesFiniteColimits
      (sheafCompose J (forget₂ (ModuleCat.{max r t} R) AddCommGrpCat.{max r t})) := by
  let U := forget₂ (ModuleCat.{max r t} R) AddCommGrpCat.{max r t}
  let adj := (ModuleCat.restrictCoextendScalarsAdj (Int.castRingHom R)).comp
    (Adjunction.ofIsLeftAdjoint (forget₂ (ModuleCat.{max r t} ℤ) AddCommGrpCat.{max r t}))
  let e : Sheaf.composeAndSheafify J U ≅ sheafCompose J U :=
    Functor.isoWhiskerLeft (sheafCompose J U)
      (asIso (sheafificationAdjunction J AddCommGrpCat.{max r t}).counit)
  have := ((Sheaf.adjunction J adj).ofNatIsoLeft e).isLeftAdjoint
  infer_instance

end Exactness

section Ext

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (R : Type r) [Ring R]
  [HasSheafify J (ModuleCat.{max r t} R)] [HasSheafify J AddCommGrpCat.{max r t}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{max r t} R) AddCommGrpCat.{max r t})]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{max r t})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{max r t})]

/-- **The acyclicity input of Stacks 03FD for sheaves of `R`-modules.** The underlying abelian
sheaf of an injective sheaf of `R`-modules has vanishing higher `Ext` out of every sectionwise
torsion-free abelian sheaf: an extension class of degree one with torsion-free first argument
splits after applying the left adjoint `R ⊗_ℤ -`, which preserves the relevant monomorphism. -/
theorem ext_eq_zero_of_isTorsionFree (I : Sheaf J (ModuleCat.{max r t} R)) [Injective I]
    (X : Sheaf J AddCommGrpCat.{max r t}) (hX : ∀ U, Module.IsTorsionFree ℤ (X.obj.obj U))
    (n : ℕ) (e : Ext.{w} X
      ((sheafCompose J (forget₂ (ModuleCat.{max r t} R) AddCommGrpCat.{max r t})).obj I)
        (n + 1)) : e = 0 := by
  apply ModuleSheafCohomology.ext_eq_zero_of_adjunction _ _ (sheafExtendScalarsFromIntAdj J R)
    (fun F : Sheaf J AddCommGrpCat.{max r t} ↦ ∀ U, Module.IsTorsionFree ℤ (F.obj.obj U))
    (fun f _ hG ↦ ModuleSheafCohomology.isTorsionFree_of_mono J f hG)
    (ModuleSheafCohomology.exists_isTorsionFree_epi J) ?_ I n X hX e
  intro S hS hP
  have := hS.mono_f
  change Mono ((presheafToSheaf J (ModuleCat.{max r t} R)).map _)
  have (U : Cᵒᵖ) : Mono ((Functor.whiskerRight S.f.hom
      (ModuleCat.extendScalarsFromInt.{t} R)).app U) := by
    let E := sheafToPresheaf J AddCommGrpCat.{max r t} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{max r t}).obj U
    obtain ⟨hE, hE'⟩ := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono E).mp
      inferInstance S hS
    have : Module.IsTorsionFree ℤ (S.map E).X₃ := hP U
    have : Mono (S.map E).f := hE'
    exact ModuleCat.mono_extendScalarsFromInt_map R (S.map E) hE
  have : Mono (Functor.whiskerRight S.f.hom (ModuleCat.extendScalarsFromInt.{t} R)) :=
    NatTrans.mono_of_mono_app _
  exact Functor.map_mono (presheafToSheaf J (ModuleCat.{max r t} R))
    (Functor.whiskerRight S.f.hom (ModuleCat.extendScalarsFromInt.{t} R))

end Ext

section DirectImage

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} (F : C ⥤ D) [F.IsContinuous J K]
  (R : Type r) [Ring R]
  [HasSheafify J AddCommGrpCat.{max v' t r}] [HasSheafify K AddCommGrpCat.{max v' t r}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max v' t r})]
  [EnoughInjectives (Sheaf K AddCommGrpCat.{max v' t r})]
  [HasExt.{max v' t r} (Sheaf K AddCommGrpCat.{max v' t r})]
  [HasSheafify K (ModuleCat.{max v' t r} R)]
  [K.HasSheafCompose (forget₂ (ModuleCat.{max v' t r} R) AddCommGrpCat.{max v' t r})]

/-- **Higher derived sections of the underlying abelian sheaf of an injective sheaf of modules
vanish** over every object: they are `Ext` groups out of the free abelian sheaf on the
representable, which is sectionwise torsion free. -/
theorem isZero_rightDerived_sheafSections_of_injective
    (I : Sheaf K (ModuleCat.{max v' t r} R)) [Injective I] (U : D) (p : ℕ) (hp : 0 < p) :
    IsZero ((((sheafSections K AddCommGrpCat.{max v' t r}).obj (op U)).rightDerived p).obj
      ((sheafCompose K (forget₂ (ModuleCat.{max v' t r} R)
        AddCommGrpCat.{max v' t r})).obj I)) := by
  obtain ⟨e⟩ :=
    FreeYonedaUnivLE.nonempty_extFunctorObj_iso_rightDerived_sections_of_enoughInjectives.{max t r}
      K U p
  refine IsZero.of_iso ?_ (e.app _).symm
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hp.ne'
  have hX : ∀ V, Module.IsTorsionFree ℤ
      (((Stacks.Cohomology.FreeYonedaUnivLE.freeYoneda.{max t r} K).obj U).obj.obj V) :=
    ModuleSheafCohomology.isTorsionFree_sheafify K _ fun V ↦ by
      change Module.IsTorsionFree ℤ (FreeAbelianGroup (ULift.{max t r} (V.unop ⟶ U)))
      exact Module.Flat.isTorsionFree
  have : Subsingleton (Ext.{max v' t r}
      ((Stacks.Cohomology.FreeYonedaUnivLE.freeYoneda.{max t r} K).obj U)
      ((sheafCompose K (forget₂ (ModuleCat.{max v' t r} R)
        AddCommGrpCat.{max v' t r})).obj I) (n + 1)) :=
    subsingleton_of_forall_eq 0
      (ext_eq_zero_of_isTorsionFree.{max v' t r, max v' t, r, v', u'} K R I _ hX n)
  exact AddCommGrpCat.isZero_of_subsingleton (AddCommGrpCat.of (Ext.{max v' t r}
    ((Stacks.Cohomology.FreeYonedaUnivLE.freeYoneda.{max t r} K).obj U)
    ((sheafCompose K (forget₂ (ModuleCat.{max v' t r} R)
      AddCommGrpCat.{max v' t r})).obj I) (n + 1)))

variable [HasDerivedCategory (Sheaf J AddCommGrpCat.{max v' t r})]
  [HasDerivedCategory (Sheaf K AddCommGrpCat.{max v' t r})]

attribute [local instance]
  Functor.hasRightDerivedFunctor_mapHomotopyCategoryPlus_of_enoughInjectives

/-- **The underlying abelian sheaf of an injective sheaf of modules is acyclic for the direct
image** of abelian sheaves along any continuous functor: the higher direct images are the
sheafifications of higher derived sections, which vanish. -/
@[sga "4 XVII 4.1.2" "special case"]
theorem rightAcyclic_sheafPushforwardContinuous_of_injective
    [PreservesFiniteLimits (F.sheafPushforwardContinuous AddCommGrpCat.{max v' t r} J K)]
    (I : Sheaf K (ModuleCat.{max v' t r} R)) [Injective I] :
    (F.sheafPushforwardContinuous AddCommGrpCat.{max v' t r} J K).rightAcyclic
      ((sheafCompose K (forget₂ (ModuleCat.{max v' t r} R)
        AddCommGrpCat.{max v' t r})).obj I) := by
  rw [((F.sheafPushforwardContinuous AddCommGrpCat.{max v' t r} J K)
    |>.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus _).2 inferInstance]
  intro i hi
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hi.le
  refine IsZero.of_iso ?_ ((Stacks.DerivedIndexing.rightDerivedIso _ q).app _).symm
  exact Stacks.Cohomology.HigherDirectImageOnACover.isZero_rightDerived_pushforward_of_cover F q _
    fun V ↦ ⟨⊤, J.top_mem V, fun W g _ ↦
      isZero_rightDerived_sheafSections_of_injective.{t, r, v', u'} R I (F.obj W) q
        (by exact_mod_cast hi)⟩

variable [HasSheafify J (ModuleCat.{max v' t r} R)]
  [J.HasSheafCompose (forget₂ (ModuleCat.{max v' t r} R) AddCommGrpCat.{max v' t r})]
  [EnoughInjectives (Sheaf K (ModuleCat.{max v' t r} R))]
  [HasDerivedCategory (Sheaf J (ModuleCat.{max v' t r} R))]
  [HasDerivedCategory (Sheaf K (ModuleCat.{max v' t r} R))]

/-- **Higher direct images of sheaves of modules are computed on underlying abelian sheaves.** A
sheaf of `R`-modules whose underlying abelian sheaf is acyclic for the direct image of abelian
sheaves along a continuous functor is acyclic for the direct image of sheaves of `R`-modules.
The sheaves of modules with this property contain the injective ones and satisfy the two out of
three property of Stacks 05T8, the forgetful functor being exact and faithful. -/
theorem rightAcyclic_sheafPushforwardContinuous_of_forget₂
    [PreservesFiniteLimits (F.sheafPushforwardContinuous AddCommGrpCat.{max v' t r} J K)]
    (A : Sheaf K (ModuleCat.{max v' t r} R))
    (hA : (F.sheafPushforwardContinuous AddCommGrpCat.{max v' t r} J K).rightAcyclic
      ((sheafCompose K (forget₂ (ModuleCat.{max v' t r} R)
        AddCommGrpCat.{max v' t r})).obj A)) :
    (F.sheafPushforwardContinuous (ModuleCat.{max v' t r} R) J K).rightAcyclic A := by
  let G := F.sheafPushforwardContinuous AddCommGrpCat.{max v' t r} J K
  let V := sheafCompose K (forget₂ (ModuleCat.{max v' t r} R) AddCommGrpCat.{max v' t r})
  let W := sheafCompose J (forget₂ (ModuleCat.{max v' t r} R) AddCommGrpCat.{max v' t r})
  have := preservesFiniteLimits_sheafCompose_forget₂.{max v' t, r, v', u'} K R
  have := preservesFiniteColimits_sheafCompose_forget₂.{max v' t, r, v', u'} K R
  have := preservesFiniteLimits_sheafCompose_forget₂.{max v' t, r, v, u} J R
  have := preservesFiniteColimits_sheafCompose_forget₂.{max v' t, r, v, u} J R
  refine (F.sheafPushforwardContinuous (ModuleCat.{max v' t r} R) J K).le_rightAcyclic
    (fun M ↦ G.rightAcyclic (V.obj M)) (fun M ↦ ⟨Injective.under M,
      rightAcyclic_sheafPushforwardContinuous_of_injective.{t, r, v, u, v', u'} F R _,
      Injective.ι M,
      inferInstance⟩) (fun S hS h₁ h₂ ↦ ?_) A hA
  obtain ⟨h₃, hmap⟩ := (G.rightAcyclic_and_shortExact_map_of_shortExact (S.map V)
    (hS.map_of_exact V)).2.1 h₁ h₂
  exact ⟨h₃, CategoryTheory.ShortExact.reflects_shortExact_of_faithful W hmap⟩

end DirectImage

end Stacks.Cohomology.ModuleSheaf

end
