module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.EventualExtVanishing
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.SupportedDevissage
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.DerivedRestrictCounit
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffineDerivedPushforward
public import StacksFrontier.Homology.Injectives.DerivedCategory.ArbitraryModel
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSections

/-!
# Derived direct image along an open immersion, on all modules and on the quasi-coherent ones

[Stacks, Tag 09T6] takes as input, for each affine open `U ⊆ X`, a total right derived functor
`Rj_*` of direct image of all modules and a total right derived functor `Φ` of direct image of
quasi-coherent modules, each presented by a derivation unit along the localization
`CategoryTheory.DerivedCategory.Q` of the *cochain* complexes. The open-immersion substrate of
`StacksFrontier/AlgebraicGeometry/Duality/OpenImmersion/` instead fixes a model of `Rj_*` and
presents it along the localization `CategoryTheory.DerivedCategory.Qh` of the *homotopy*
category, where its adjunction with restriction and its full faithfulness are available.

This file bridges the two presentations and transports what the substrate proves to an arbitrary
model. `Stacks.DerivedQCoh.cochainUnitOfHomotopyUnit` turns a homotopy-category derivation unit
into a cochain-level one, `Stacks.DerivedQCoh.isRightDerivedFunctor_cochainUnitOfHomotopyUnit`
checks that the result still exhibits the same functor as a total right derived functor — the two
units agree at the K-injective complexes, where both are invertible — and
`Stacks.DerivedQCoh.derivedFunctorIsoOfHomotopyUnit` then identifies any cochain-level model with
the chosen one by uniqueness of right derived functors.

The consequences used by [Stacks, Tag 09T6] are: derived direct image along an open immersion is
fully faithful, the unit of the derived adjunction `j^* ⊣ Rj_*` becomes invertible after
restriction to `U`, and hence the dévissage triangle `E ⟶ Rj_*(E|_U) ⟶ G` has its third vertex
supported on `T ∖ U` whenever `E` and `Rj_*(E|_U)` are supported on the closed set `T`.

## Main definitions

* `Stacks.DerivedQCoh.cochainUnitOfHomotopyUnit` — a homotopy-category derivation unit read on
  cochain complexes.
* `Stacks.DerivedQCoh.derivedFunctorIsoOfHomotopyUnit` — the comparison of a cochain-level model
  of a right derived functor with a homotopy-category one.
* `Stacks.DerivedQCoh.derivedQuasicoherentPushforward` — the chosen total right derived functor
  of `j_* : QCoh(𝒪_U) ⥤ QCoh(𝒪_X)`.
* `Stacks.DerivedQCoh.derivedQuasicoherentRestrictPushforwardAdjunction` — the derived adjunction
  `j^* ⊣ Φ` on quasi-coherent modules.

## Main results

* `Stacks.DerivedQCoh.exists_derivedRestriction_triangle` — the dévissage triangle of
  [Stacks, Tag 09T6].
* `Stacks.DerivedQCoh.fullyFaithful_derivedQuasicoherentPushforward` — `Φ` is fully faithful.
* `Stacks.DerivedQCoh.derivedQuasicoherentRestrictCompι` — the square identifying restriction of
  quasi-coherent modules, after the derived inclusions, with restriction of all modules.
* `Stacks.DerivedQCoh.quasicoherentRestrictPushforwardAdjunction` — restriction is left adjoint
  to direct image on quasi-coherent modules.

## Implementation notes

The derived categories are the locally small ones; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/SupportedDevissage.lean`.

Full faithfulness of `Φ` is obtained from the underived statement rather than by hand: direct
image on quasi-coherent modules is fully faithful because direct image of all modules is and
`AlgebraicGeometry.quasicoherentPushforwardCompιIso` identifies the two after the fully faithful
inclusions, and `Stacks.SmallDerivedCategory.isIso_derivedAdjunction_counit` then makes the counit
of the derived adjunction invertible. This is why the chosen model of `Φ` is the one presented
along the homotopy category: that theorem is stated for it.

## References

* [Stacks Project, Tag 09T6](https://stacks.math.columbia.edu/tag/09T6)
* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
* [Stacks Project, Tag 08DF](https://stacks.math.columbia.edu/tag/08DF)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated ExtensionByZeroModules TopologicalSpace

universe w u

namespace Stacks.DerivedQCoh

attribute [local instance] preservesFiniteLimits_restrictFunctor

/-! ### Restriction of modules to an open subscheme in the `SheafOfModules` spelling -/

/-- Restriction of modules to an open subscheme, with domain and codomain spelled
`SheafOfModules.{u} X.ringCatSheaf` rather than `AlgebraicGeometry.Scheme.Modules X`.

The two spellings of the module category are definitionally equal but carry separately declared
`Category` and `Preadditive` instances, so an exactness instance found for one is not found for
the other; this ascription moves restriction to the spelling in which the closed-support
substrate and the comparison functor of [Stacks, Tag 06VT] are stated. This is the same device as
`Stacks.DerivedQCoh.modulesPushforward`. -/
def modulesRestrict {X : Scheme.{u}} (U : X.Opens) :
    SheafOfModules.{u} X.ringCatSheaf ⥤ SheafOfModules.{u} U.toScheme.ringCatSheaf :=
  Scheme.Modules.restrictFunctor U.ι

/-- `Stacks.DerivedQCoh.modulesRestrict` is additive. -/
instance modulesRestrict_additive {X : Scheme.{u}} (U : X.Opens) :
    (modulesRestrict U).Additive :=
  inferInstanceAs ((Scheme.Modules.restrictFunctor U.ι).Additive)

/-- `Stacks.DerivedQCoh.modulesRestrict` is left exact. -/
instance modulesRestrict_preservesFiniteLimits {X : Scheme.{u}} (U : X.Opens) :
    PreservesFiniteLimits (modulesRestrict U) :=
  preservesFiniteLimits_restrictFunctor U.ι

/-- `Stacks.DerivedQCoh.modulesRestrict` is right exact. -/
instance modulesRestrict_preservesFiniteColimits {X : Scheme.{u}} (U : X.Opens) :
    PreservesFiniteColimits (modulesRestrict U) :=
  inferInstanceAs (PreservesFiniteColimits (Scheme.Modules.restrictFunctor U.ι))

/-- `Stacks.DerivedQCoh.modulesRestrict` is additive, with its codomain read in the spelling
`ExtensionByZeroModules.resRing` of the restricted sheaf of rings that the closed-support
substrate uses. The two spellings of that sheaf are definitionally equal but carry separately
declared `Preadditive` instances, so both readings have to be registered. -/
instance modulesRestrict_additive_resRing {X : Scheme.{u}} (U : X.Opens) :
    (modulesRestrict U : SheafOfModules.{u} X.ringCatSheaf ⥤
      SheafOfModules.{u} (resRing U X.ringCatSheaf)).Additive :=
  inferInstanceAs ((Scheme.Modules.restrictFunctor U.ι).Additive)

/-- `Stacks.DerivedQCoh.modulesRestrict` is left exact, read in the `resRing` spelling; see
`Stacks.DerivedQCoh.modulesRestrict_additive_resRing`. -/
instance modulesRestrict_preservesFiniteLimits_resRing {X : Scheme.{u}} (U : X.Opens) :
    PreservesFiniteLimits (modulesRestrict U : SheafOfModules.{u} X.ringCatSheaf ⥤
      SheafOfModules.{u} (resRing U X.ringCatSheaf)) :=
  preservesFiniteLimits_restrictFunctor U.ι

/-- `Stacks.DerivedQCoh.modulesRestrict` is right exact, read in the `resRing` spelling; see
`Stacks.DerivedQCoh.modulesRestrict_additive_resRing`. -/
instance modulesRestrict_preservesFiniteColimits_resRing {X : Scheme.{u}} (U : X.Opens) :
    PreservesFiniteColimits (modulesRestrict U : SheafOfModules.{u} X.ringCatSheaf ⥤
      SheafOfModules.{u} (resRing U X.ringCatSheaf)) :=
  inferInstanceAs (PreservesFiniteColimits (Scheme.Modules.restrictFunctor U.ι))

/-- `Stacks.DerivedQCoh.modulesRestrict` is `ExtensionByZeroModules.jStar`, the restriction used
by the closed-support substrate. -/
theorem modulesRestrict_eq_jStar {X : Scheme.{u}} (U : X.Opens) :
    (modulesRestrict U : SheafOfModules.{u} X.ringCatSheaf ⥤
      SheafOfModules.{u} (resRing U X.ringCatSheaf)) = jStar U X.ringCatSheaf :=
  (Stacks.Duality.OpenImmersion.jStar_eq_restrictFunctor X U).symm

/-! ### A homotopy-category derivation unit read on cochain complexes -/

section Bridge

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
  (G : A ⥤ B) [G.Additive] (R : DerivedCategory A ⥤ DerivedCategory B)
  (β : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ R)

/-- **A derivation unit along the homotopy category, read on cochain complexes.** Restricting
`β : G_K ⋙ Qh ⟶ Qh ⋙ R` along the quotient `C(𝒜) ⥤ K(𝒜)` and rewriting both ends with
`Stacks.DerivedModel.mapHomotopyCategoryCompQhIso` and
`CategoryTheory.DerivedCategory.quotientCompQhIso` presents it as a natural transformation
`G_* ⋙ Q ⟶ Q ⋙ R` out of the cochain complexes. -/
def cochainUnitOfHomotopyUnit :
    G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ R :=
  (Stacks.DerivedModel.mapHomotopyCategoryCompQhIso G).inv ≫
    Functor.whiskerLeft (HomotopyCategory.quotient A (ComplexShape.up ℤ)) β ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso A).hom R

/-- At a cochain complex, `Stacks.DerivedQCoh.cochainUnitOfHomotopyUnit` is the homotopy-category
unit conjugated by the two comparison isomorphisms. -/
lemma cochainUnitOfHomotopyUnit_app (K : CochainComplex A ℤ) :
    (cochainUnitOfHomotopyUnit G R β).app K =
      (Stacks.DerivedModel.mapHomotopyCategoryCompQhIso G).inv.app K ≫
        β.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ≫
        R.map ((DerivedCategory.quotientCompQhIso A).hom.app K) := by
  simp [cochainUnitOfHomotopyUnit]

variable [IsGrothendieckAbelian.{w} A]
  (hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
    I.IsKInjective ∧ QuasiIso f)
  [R.IsRightDerivedFunctor β (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]

include hA in
/-- **A total right derived functor along the homotopy category is one along the cochain
complexes.** Both units are invertible at a K-injective complex — the homotopy-category one
because K-injective complexes compute right derived functors, the cochain-level one because it is
the former conjugated by isomorphisms — and Spaltenstein's criterion
`Stacks.Injectives.KInjectiveResolution.isRightDerivedFunctor_iff_isIso_app_of_isKInjective`
needs nothing else. -/
theorem isRightDerivedFunctor_cochainUnitOfHomotopyUnit :
    R.IsRightDerivedFunctor (cochainUnitOfHomotopyUnit G R β)
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) := by
  have hInv : Stacks.Injectives.KInjectiveResolution.InvertsQuasiIsoOfIsKInjective
      (G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) := by
    intro K L s hK hL hs
    exact Localization.inverts DerivedCategory.Q
      (HomologicalComplex.quasiIso B (ComplexShape.up ℤ)) _
      ((HomologicalComplex.mem_quasiIso_iff _).2
        (Stacks.Injectives.KInjectiveResolution.quasiIso_mapHomologicalComplex_map_of_isKInjective
          G s hK hL hs))
  refine (Stacks.Injectives.KInjectiveResolution.isRightDerivedFunctor_iff_isIso_app_of_isKInjective
    DerivedCategory.Q R _ hInv).2 fun K hK => ?_
  have := (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) hA).2
    DerivedCategory.Qh R β K hK
  rw [cochainUnitOfHomotopyUnit_app]
  infer_instance

include hA in
/-- **Uniqueness of the total right derived functor across the two presentations.** A functor
presented as a total right derived functor of `G` along the localization of the cochain complexes
is canonically isomorphic to one presented along the localization of the homotopy category. -/
def derivedFunctorIsoOfHomotopyUnit (R' : DerivedCategory A ⥤ DerivedCategory B)
    (α : G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ R')
    [R'.IsRightDerivedFunctor α (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))] :
    R' ≅ R :=
  haveI := isRightDerivedFunctor_cochainUnitOfHomotopyUnit G R β hA
  Functor.rightDerivedNatIso R' R α (cochainUnitOfHomotopyUnit G R β)
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) (Iso.refl _)

end Bridge

/-! ### Derived direct image of all modules -/

/-- **Any cochain-level model of derived direct image is the chosen one.** A total right derived
functor of `f_* : Mod(𝒪_X) ⥤ Mod(𝒪_Y)` presented by a derivation unit along the localization of
the cochain complexes is canonically isomorphic to `Stacks.Duality.derivedPushforward f`. -/
def derivedPushforwardIsoOfCochainUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Rf : DerivedCategory X.Modules ⥤ DerivedCategory Y.Modules)
    (ηf : (Scheme.Modules.pushforward f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ Rf)
    [Rf.IsRightDerivedFunctor ηf (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ))] :
    Rf ≅ Stacks.Duality.derivedPushforward f :=
  derivedFunctorIsoOfHomotopyUnit (Scheme.Modules.pushforward f)
    (Stacks.Duality.derivedPushforward f)
    ((Stacks.Duality.homotopyPushforward f).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)))
    (AlgebraicGeometry.Scheme.Modules.exists_quasiIso_isKInjective X) Rf ηf

/-- **Derived direct image along an open immersion of schemes is fully faithful.** The counit of
the derived adjunction `j^* ⊣ Rj_*` is invertible, by
`Stacks.Duality.OpenImmersion.isIso_derivedRestrictPushforwardAdjunction_counit`. -/
theorem fullyFaithful_derivedPushforward {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    Nonempty (Stacks.Duality.derivedPushforward j).FullyFaithful :=
  ⟨(Stacks.Duality.OpenImmersion.derivedRestrictPushforwardAdjunction
    j).fullyFaithfulROfIsIsoCounit⟩

/-- **The dévissage triangle of [Stacks, Tag 09T6].** Let `U ⊆ X` be open and let `E` be an
object of `D(𝒪_X)` whose cohomology is supported on a closed set `T`, and suppose the derived
direct image of its restriction to `U` is also supported on `T`. Then the unit
`E ⟶ Rj_*(E|_U)` of the derived adjunction fits into a distinguished triangle whose third vertex
is supported on `T ∖ U`.

Restriction to `U` carries the unit to an isomorphism, derived direct image along an open
immersion being fully faithful, so
`Stacks.DerivedQCoh.exists_cocone_supportedOn_inter_compl` applies. -/
theorem exists_derivedRestriction_triangle (X : Scheme.{u}) (U : X.Opens) (T : Set X)
    (hT : IsClosed T) (E : DerivedCategory X.Modules)
    (hE : Cohomology.PushforwardRestriction.CohomologySupportedOn X.ringCatSheaf T E)
    (hPush : Cohomology.PushforwardRestriction.CohomologySupportedOn X.ringCatSheaf T
      ((Stacks.Duality.derivedPushforward U.ι).obj
        ((Stacks.Duality.OpenImmersion.derivedRestrict U.ι).obj E))) :
    ∃ S : Triangle (DerivedCategory X.Modules),
      S.obj₁ = E ∧
        S.obj₂ = (Stacks.Duality.derivedPushforward U.ι).obj
          ((Stacks.Duality.OpenImmersion.derivedRestrict U.ι).obj E) ∧
        S ∈ distTriang _ ∧
        Cohomology.PushforwardRestriction.CohomologySupportedOn X.ringCatSheaf (T \ U)
          S.obj₃ := by
  let a := Stacks.Duality.OpenImmersion.derivedRestrictPushforwardAdjunction U.ι
  have hres : IsIso ((Stacks.Duality.OpenImmersion.derivedRestrict U.ι).map (a.unit.app E)) :=
    isIso_of_comp_hom_eq_id _ (a.left_triangle_components E)
  obtain ⟨G, g, δ, hDist, hG⟩ :=
    @exists_cocone_supportedOn_inter_compl _ X.ringCatSheaf T hT U (modulesRestrict U)
      (modulesRestrict_eq_jStar U) (modulesRestrict_additive_resRing U)
      (modulesRestrict_preservesFiniteLimits_resRing U)
      (modulesRestrict_preservesFiniteColimits_resRing U) _ _ (a.unit.app E) hE hPush hres
  exact ⟨Triangle.mk (a.unit.app E) g δ, rfl, rfl, hDist,
    fun i x hx => hG i x fun h => hx ⟨h.1, h.2⟩⟩

/-! ### Derived direct image of quasi-coherent modules -/

section QuasiCoherent

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

/-- Every cochain complex of quasi-coherent `𝒪_X`-modules admits a quasi-isomorphism into a
K-injective one: the quasi-coherent modules on a scheme form a Grothendieck abelian category, so
[Stacks, Tag 079P] applies. -/
theorem exists_quasiIso_isKInjective_quasicoherentModules (Z : Scheme.{u})
    (K : CochainComplex (Scheme.QuasicoherentModules Z) ℤ) :
    ∃ (I : CochainComplex (Scheme.QuasicoherentModules Z) ℤ) (g : K ⟶ I),
      I.IsKInjective ∧ QuasiIso g :=
  ⟨_, (Stacks.Injectives.kInjectiveResolutionInclusion
    (Scheme.QuasicoherentModules Z)).app K, inferInstance, inferInstance⟩

/-- **Direct image on quasi-coherent modules is fully faithful when direct image of all modules
is.** `AlgebraicGeometry.quasicoherentPushforwardCompιIso` identifies the two after the fully
faithful inclusions of the quasi-coherent modules. -/
theorem fullyFaithful_quasicoherentPushforward [(Scheme.Modules.pushforward f).Full]
    [(Scheme.Modules.pushforward f).Faithful] :
    Nonempty (quasicoherentPushforward f).FullyFaithful :=
  have : (pushforwardSheafOfModules f).Full :=
    inferInstanceAs ((Scheme.Modules.pushforward f).Full)
  have : (pushforwardSheafOfModules f).Faithful :=
    inferInstanceAs ((Scheme.Modules.pushforward f).Faithful)
  ⟨Functor.FullyFaithful.ofCompFaithful
    ((Functor.FullyFaithful.ofFullyFaithful
      ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙
        pushforwardSheafOfModules f)).ofIso (quasicoherentPushforwardCompιIso f).symm)⟩

/-- **The chosen total right derived functor of direct image on quasi-coherent modules**, along
the localization `CategoryTheory.DerivedCategory.Qh` of the homotopy category. It exists because
the quasi-coherent modules form a Grothendieck abelian category. -/
abbrev derivedQuasicoherentPushforward :
    DerivedCategory (Scheme.QuasicoherentModules X) ⥤
      DerivedCategory (Scheme.QuasicoherentModules Y) :=
  haveI := Stacks.Duality.hasRightDerivedFunctor_of_isGrothendieckAbelian
    ((quasicoherentPushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
  ((quasicoherentPushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Scheme.QuasicoherentModules X) (ComplexShape.up ℤ))

/-- The derivation unit of `Stacks.DerivedQCoh.derivedQuasicoherentPushforward`. -/
abbrev derivedQuasicoherentPushforwardUnit :
    (quasicoherentPushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ derivedQuasicoherentPushforward f :=
  haveI := Stacks.Duality.hasRightDerivedFunctor_of_isGrothendieckAbelian
    ((quasicoherentPushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
  ((quasicoherentPushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Scheme.QuasicoherentModules X) (ComplexShape.up ℤ))

/-- `Stacks.DerivedQCoh.derivedQuasicoherentPushforward` is a total right derived functor of
direct image on quasi-coherent modules, which is the universal property characterising it. -/
instance derivedQuasicoherentPushforward_isRightDerivedFunctor :
    (derivedQuasicoherentPushforward f).IsRightDerivedFunctor
      (derivedQuasicoherentPushforwardUnit f)
      (HomotopyCategory.quasiIso (Scheme.QuasicoherentModules X) (ComplexShape.up ℤ)) :=
  haveI := Stacks.Duality.hasRightDerivedFunctor_of_isGrothendieckAbelian
    ((quasicoherentPushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
  inferInstance

/-- **Any cochain-level model of `Φ` is the chosen one.** A total right derived functor of
`j_* : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` presented by a derivation unit along the localization of the
cochain complexes is canonically isomorphic to
`Stacks.DerivedQCoh.derivedQuasicoherentPushforward`. -/
def derivedQuasicoherentPushforwardIsoOfCochainUnit
    (Φ : DerivedCategory (Scheme.QuasicoherentModules X) ⥤
      DerivedCategory (Scheme.QuasicoherentModules Y))
    (ηΦ : (quasicoherentPushforward f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ Φ)
    [Φ.IsRightDerivedFunctor ηΦ
      (HomologicalComplex.quasiIso (Scheme.QuasicoherentModules X) (ComplexShape.up ℤ))] :
    Φ ≅ derivedQuasicoherentPushforward f :=
  derivedFunctorIsoOfHomotopyUnit (quasicoherentPushforward f)
    (derivedQuasicoherentPushforward f) (derivedQuasicoherentPushforwardUnit f)
    (exists_quasiIso_isKInjective_quasicoherentModules X) Φ ηΦ

end QuasiCoherent

/-! ### Restriction of quasi-coherent modules to an open subscheme -/

section QuasicoherentRestrict

variable {X : Scheme.{u}} (U : X.Opens)

/-- **Restriction of quasi-coherent modules to an open subscheme.** It is the restriction of
`Stacks.DerivedQCoh.modulesRestrict` to the quasi-coherent modules, which is legitimate because
restriction to an open subscheme carries a quasi-coherent module to a quasi-coherent module. -/
def quasicoherentRestrict :
    Scheme.QuasicoherentModules X ⥤ Scheme.QuasicoherentModules U.toScheme :=
  (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).lift
    ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙ modulesRestrict U) fun M =>
      have : M.obj.IsQuasicoherent := M.property
      Scheme.Modules.isQuasicoherent_restrictFunctor U.ι M.obj

/-- Forgetting quasi-coherence after restricting to an open subscheme is restricting after
forgetting quasi-coherence; this is the defining property of
`Stacks.DerivedQCoh.quasicoherentRestrict`. -/
def quasicoherentRestrictCompι :
    quasicoherentRestrict U ⋙ (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).ι ≅
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙ modulesRestrict U :=
  ObjectProperty.liftCompιIso _ _ _

/-- `Stacks.DerivedQCoh.quasicoherentRestrict` is additive, the inclusion of the quasi-coherent
modules being faithful and additive. -/
instance quasicoherentRestrict_additive : (quasicoherentRestrict U).Additive :=
  haveI : (quasicoherentRestrict U ⋙
      (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).ι).Additive :=
    Functor.additive_of_iso (quasicoherentRestrictCompι U).symm
  Functor.additive_of_comp_faithful _
    (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).ι

/-- `Stacks.DerivedQCoh.quasicoherentRestrict` is left exact: its composite with the exact,
isomorphism-reflecting inclusion of the quasi-coherent modules is. -/
instance quasicoherentRestrict_preservesFiniteLimits :
    PreservesFiniteLimits (quasicoherentRestrict U) :=
  haveI : PreservesFiniteLimits (quasicoherentRestrict U ⋙
      (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).ι) :=
    preservesFiniteLimits_of_natIso (quasicoherentRestrictCompι U).symm
  preservesFiniteLimits_of_reflects_of_preserves _
    (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).ι

/-- `Stacks.DerivedQCoh.quasicoherentRestrict` is right exact; see
`Stacks.DerivedQCoh.quasicoherentRestrict_preservesFiniteLimits`. -/
instance quasicoherentRestrict_preservesFiniteColimits :
    PreservesFiniteColimits (quasicoherentRestrict U) :=
  haveI : PreservesFiniteColimits (quasicoherentRestrict U ⋙
      (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).ι) :=
    preservesFiniteColimits_of_natIso (quasicoherentRestrictCompι U).symm
  preservesFiniteColimits_of_reflects_of_preserves _
    (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).ι

variable [QuasiCompact U.ι] [QuasiSeparated U.ι]

/-- **Restriction is left adjoint to direct image on quasi-coherent modules.** The adjunction
`j^* ⊣ j_*` of all modules restricts along the fully faithful inclusions of the quasi-coherent
modules, the two compatibility isomorphisms being the defining properties of the restricted
functors. -/
def quasicoherentRestrictPushforwardAdjunction :
    quasicoherentRestrict U ⊣ quasicoherentPushforward U.ι :=
  (Scheme.Modules.restrictAdjunction U.ι).restrictFullyFaithful
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).fullyFaithfulι
    (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).fullyFaithfulι
    (quasicoherentRestrictCompι U).symm (quasicoherentPushforwardCompιIso U.ι).symm

/-- **The derived adjunction `j^* ⊣ Φ` on quasi-coherent modules**, [Stacks, Tag 09T5] for the
adjunction `Stacks.DerivedQCoh.quasicoherentRestrictPushforwardAdjunction`: restriction is exact,
so the functor it induces on derived categories is left adjoint to the total right derived functor
of direct image. -/
def derivedQuasicoherentRestrictPushforwardAdjunction :
    (quasicoherentRestrict U).mapDerivedCategory ⊣ derivedQuasicoherentPushforward U.ι :=
  Stacks.SmallDerivedCategory.derivedAdjunction (quasicoherentRestrictPushforwardAdjunction U)
    (Iso.refl _) (derivedQuasicoherentPushforwardUnit U.ι)
    (exists_quasiIso_isKInjective_quasicoherentModules U.toScheme)

/-- **`Φ` is fully faithful.** Direct image on quasi-coherent modules is fully faithful along an
open immersion, so the counit of
`Stacks.DerivedQCoh.quasicoherentRestrictPushforwardAdjunction` is invertible and
`Stacks.SmallDerivedCategory.isIso_derivedAdjunction_counit` passes that to the derived
adjunction. -/
theorem fullyFaithful_derivedQuasicoherentPushforward :
    Nonempty (derivedQuasicoherentPushforward U.ι).FullyFaithful := by
  obtain ⟨ff⟩ := fullyFaithful_quasicoherentPushforward U.ι
  have := ff.full
  have := ff.faithful
  have : IsIso (derivedQuasicoherentRestrictPushforwardAdjunction U).counit :=
    Stacks.SmallDerivedCategory.isIso_derivedAdjunction_counit
      (quasicoherentRestrictPushforwardAdjunction U) (Iso.refl _)
      (derivedQuasicoherentPushforwardUnit U.ι)
      (exists_quasiIso_isKInjective_quasicoherentModules U.toScheme)
  exact ⟨(derivedQuasicoherentRestrictPushforwardAdjunction U).fullyFaithfulROfIsIsoCounit⟩

/-- **Restriction of quasi-coherent modules, after the derived inclusions, is restriction of all
modules.** For an open subscheme `U ⊆ X` the square

```
D(QCoh(𝒪_X)) --j^*--> D(QCoh(𝒪_U))
     | ι                   | ι
     v                     v
   D(𝒪_X)   --j^*-->     D(𝒪_U)
```

commutes, because `Stacks.DerivedQCoh.quasicoherentRestrictCompι` commutes already before
deriving and deriving an exact functor commutes with composition. -/
def derivedQuasicoherentRestrictCompι :
    (quasicoherentRestrict U).mapDerivedCategory ⋙
        (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).ι.mapDerivedCategory ≅
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapDerivedCategory ⋙
        (modulesRestrict U).mapDerivedCategory :=
  (Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso (quasicoherentRestrict U)
    (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).ι).symm ≪≫
    Cohomology.PerfectComplexTriangles.mapDerivedCategoryIsoOfNatIso _ _
      (quasicoherentRestrictCompι U) ≪≫
    Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι (modulesRestrict U)

end QuasicoherentRestrict

end Stacks.DerivedQCoh

end
