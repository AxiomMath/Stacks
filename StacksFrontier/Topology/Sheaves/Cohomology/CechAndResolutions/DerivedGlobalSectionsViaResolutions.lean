module

public import StacksFrontier.Algebra.Homology.Resolution.InjectiveResolution
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAndResolutions.FunctorialDerivedGlobalSections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Computing the functorial map on derived global sections with injective resolutions

Let `f : X ⟶ Y` be a morphism of ringed spaces and let `φ : f^* G ⟶ F` be an `f`-map of sheaves
of modules. Choose an injective resolution `F[0] ⟶ I⁼` on `X`, an injective resolution
`G[0] ⟶ J⁼` on `Y`, and an injective resolution `f_* I⁼ ⟶ J'⁼` of the pushforward of the first
one. The adjoint `G ⟶ f_* F` of `φ` lifts to a morphism `β : J⁼ ⟶ J'⁼` of resolutions, and after
taking global sections on `Y` the map `Γ(Y, f_* I⁼) ⟶ Γ(Y, J'⁼)` becomes invertible in the
derived category. The roof formed by `Γ(Y, β)` and the inverse of that map is the functorial
morphism `RΓ(Y, G) ⟶ RΓ(X, F)` of [Stacks, Tag 01F9].

## Main definitions

* `Stacks.Cohomology.modulePushforwardComplex` and
  `Stacks.Cohomology.moduleGlobalSectionsComplex`: pushforward and global sections applied
  termwise to a complex of sheaves of modules.
* `Stacks.Cohomology.injectiveResolutionGlobalSectionsMap`: the morphism represented by the
  roof.
* `Stacks.Cohomology.derivedModuleGlobalSectionsAlongResolutionIso`: the identification of
  `RΓ(X, F)`, regarded over `Γ(Y, 𝒪_Y)`, with `Γ(Y, f_* I⁼)`.

## Main results

* `Stacks.Cohomology.exists_pushforwardInjectiveResolutionLift`: the lift `β` between the
  chosen resolutions exists.
* `Stacks.Cohomology.quasiIso_moduleGlobalSections_map_pushforwardResolution`: the right leg
  of the roof is a quasi-isomorphism, so the roof defines a morphism in the derived category.
* `Stacks.Cohomology.rightDerivedFunctorPlusUnit_comp_compIso_trans_squareIso_hom_app` and
  `Stacks.Cohomology.rightDerivedFunctorPlusUnit_comp_derivedModuleGlobalSectionsAlongIso_hom`:
  the comparison of [Stacks, Tag 01EZ] at `⊤`, composed with the canonical comparison of
  [Stacks, Tag 015M], is the one induced by the derived-functor units.
* `Stacks.Cohomology.mapHomologicalComplexDerivedUnit_comp_alongIso_hom`: the same statement
  read on a bounded-below complex of sheaves of modules rather than on its image in the
  homotopy category. This is the form in which [Stacks, Tag 01EZ] enters the identification of
  the roof with the canonical functorial map.
* `Stacks.Cohomology.mapSingleFunctorPlusCompQhIso_inv_app_comp_map_qhHom`: for an additive
  functor, the canonical comparison of its value on a sheaf, placed in degree zero, with its
  right derived functor on that sheaf, computed on an injective resolution.
* `Stacks.Cohomology.derivedModuleGlobalSectionsMap_eq_injectiveResolutionGlobalSectionsMap`:
  the roof is the canonical functorial map of [Stacks, Tag 01F9], read through the two
  resolution comparisons.

## Implementation notes

The source works with bounded-below complexes. Their images are displayed in the unbounded
derived category; since every complex involved is bounded below, this is the image of the same
roof from the bounded-below derived category. An injective resolution of a sheaf of modules is
expressed as an injective resolution of the complex concentrated in degree zero. The resolution
map of `J⁼` is assumed to be a monomorphism in every degree, which makes the lifting square
commute strictly rather than merely up to homotopy.

The right leg of the roof is a quasi-isomorphism because both of its ends are termwise right
acyclic for global sections on `Y`: the terms of `f_* I⁼` are pushforwards of injective
modules, which is part (2) of [Stacks, Tag 01EX], and the terms of `J'⁼` are injective.

The structure sheaf of a ringed space has two definitionally equal spellings in the library,
and instance search unfolds neither to the other. The additivity instances that the derived
functors of this file need are therefore restated in both spellings as local instances;
`Stacks.Cohomology.plus_modulePushforwardComplex` plays the same role for the boundedness
witness of a pushed-forward complex.

The statement that pins the comparison of [Stacks, Tag 01EZ] is proved from a general
statement about a commutative square of additive functors, recorded in the section
`DerivedSquare`: that makes the only spelling-sensitive step the instantiation, and the proof
of the general statement itself needs no compiler options. The section `SingleResolution`
plays the same role for the first step of the identification of the roof.

The bounded-below homotopy and derived categories are full subcategories, so their morphisms
can be spelled through either of two definitionally equal category instances, and `rw` and
`simp` match only one of them. The proofs of the identification therefore pass through
explicitly stated intermediate equalities, combined with `CategoryTheory.Category.assoc`,
`congrArg` and `Eq.trans`, all checked at default transparency. For the same reason the
complex underlying a morphism built by `DerivedCategory.Plus.qhHomMk` is supplied explicitly
rather than left to unification.

## References

* [Stacks Project, Tag 01FB](https://stacks.math.columbia.edu/tag/01FB)
* [Stacks Project, Tag 01F9](https://stacks.math.columbia.edu/tag/01F9)
* [Stacks Project, Tag 01EX](https://stacks.math.columbia.edu/tag/01EX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Cohomology

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- Global sections of sheaves of modules, in the spelling of the structure sheaf used by
[Stacks, Tag 01EZ], is additive. The two spellings of the structure sheaf agree definitionally
but not at reducible transparency, so instance search needs both. -/
local instance evaluationTopAdditive (Z : RingedSpace.{u, u}) :
    (SheafOfModules.evaluation.{u} (structureSheafRing Z) (op ⊤)).Additive :=
  moduleGlobalSections_additive Z

/-- Sections over an open subset, in the spelling of the structure sheaf used by
[Stacks, Tag 01EZ], is additive. The instance for the top open is recorded separately above,
since the two statements are keyed differently by instance search. -/
local instance evaluationAdditive (Z : RingedSpace.{u, u}) (V : Opens Z.carrier) :
    (SheafOfModules.evaluation.{u} (structureSheafRing Z) (op V)).Additive := by
  unfold SheafOfModules.evaluation
  infer_instance

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

-- Restriction of scalars along the component of `f^♯` is additive, in the spelling of
-- restriction of scalars used by [Stacks, Tag 01EZ]; `Mathlib`'s instance is stated for the
-- source category spelled through the pushforward of the structure sheaf, which instance search
-- does not unfold to this one. Seated from `DerivedSectionsOfAPushforward`, not restated: the
-- statement is the same one, and only the attribute there is file-local.
attribute [local instance]
  Stacks.Cohomology.DerivedPushforwardSections.restrictScalarsSectionsAdditive

/-- **Pushforward applied termwise to a complex of sheaves of modules.** -/
noncomputable abbrev modulePushforwardComplex (K : CochainComplex (Modules X) ℤ) :
    CochainComplex (Modules Y) ℤ :=
  ((RingedSpaceModuleAdjunction.modulePushforward f).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K

/-- **Global sections applied termwise to a complex of sheaves of modules.** -/
noncomputable abbrev moduleGlobalSectionsComplex (X : RingedSpace.{u, u})
    (K : CochainComplex (Modules X) ℤ) :
    CochainComplex (ModuleCat ((ringCatSheaf X).obj.obj (op ⊤))) ℤ :=
  ((moduleGlobalSections X).mapHomologicalComplex (ComplexShape.up ℤ)).obj K

/-- **The pushforward of a bounded-below complex of sheaves of modules is bounded below.**
This is `CochainComplex.plus_mapHomologicalComplex_obj` for the pushforward, with the target
category spelled as `Stacks.Cohomology.Modules`. -/
lemma plus_modulePushforwardComplex {K : CochainComplex (Modules X) ℤ}
    (hK : CochainComplex.plus (Modules X) K) :
    CochainComplex.plus (Modules Y) (modulePushforwardComplex f K) :=
  CochainComplex.plus_mapHomologicalComplex_obj
    (RingedSpaceModuleAdjunction.modulePushforward f) hK

/-- **The commutative square labelled `(choice)` in [Stacks, Tag 01FB].** Given injective
resolutions of `F[0]`, of `G[0]` and of the pushforward of the resolution of `F[0]`, the adjoint
of an `f`-map lifts to a morphism between the latter two resolutions. -/
@[stacks 01FB "the lift between injective resolutions"]
theorem exists_pushforwardInjectiveResolutionLift {G : Modules Y} {F : Modules X}
    (φ : (RingedSpaceModuleAdjunction.modulePullback f).obj G ⟶ F)
    (I : CochainComplex.InjectiveResolution
      ((CochainComplex.singleFunctor (Modules X) 0).obj F))
    (J : CochainComplex.InjectiveResolution
      ((CochainComplex.singleFunctor (Modules Y) 0).obj G))
    (J' : CochainComplex.InjectiveResolution (modulePushforwardComplex f I.cocomplex))
    [∀ n, Mono (J.ι.f n)] :
    ∃ β : J.cocomplex ⟶ J'.cocomplex,
      J.ι ≫ β =
        (CochainComplex.singleFunctor (Modules Y) 0).map
            (RingedSpaceModuleAdjunction.homEquiv f F G φ) ≫
          (HomologicalComplex.singleMapHomologicalComplex
              (RingedSpaceModuleAdjunction.modulePushforward f)
              (ComplexShape.up ℤ) 0).inv.app F ≫
          ((RingedSpaceModuleAdjunction.modulePushforward f).mapHomologicalComplex
              (ComplexShape.up ℤ)).map I.ι ≫ J'.ι := by
  have hK : J'.cocomplex.IsKInjective := by
    obtain ⟨a, _⟩ := (CochainComplex.plus_iff (Modules Y) _).1 J'.boundedBelow
    exact CochainComplex.isKInjective_of_injective _ a
  exact (CochainComplex.IsKInjective.exists_factorization_of_quasiIso J.ι _).2

/-- **The right leg of the roof of [Stacks, Tag 01FB] is a quasi-isomorphism.** If `I⁼` is a
complex of injective sheaves of modules on `X` and `J'⁼` is an injective resolution of its
pushforward, then global sections on `Y` carry the resolution map to a quasi-isomorphism, hence
to an isomorphism in the derived category. -/
@[stacks 01FB "the quasi-isomorphism after taking sections"]
theorem quasiIso_moduleGlobalSections_map_pushforwardResolution {F : Modules X}
    (I : CochainComplex.InjectiveResolution
      ((CochainComplex.singleFunctor (Modules X) 0).obj F))
    (J' : CochainComplex.InjectiveResolution (modulePushforwardComplex f I.cocomplex)) :
    QuasiIso (((moduleGlobalSections Y).mapHomologicalComplex (ComplexShape.up ℤ)).map J'.ι) := by
  have hinj : EnoughInjectives (Modules Y) := IsGrothendieckAbelian.enoughInjectives
  have hplus : (((moduleGlobalSections Y).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh).HasRightDerivedFunctor
        (HomotopyCategory.Plus.quasiIso (Modules Y))) := by
    have : ((moduleGlobalSections Y).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh).HasPointwiseRightDerivedFunctor
          (HomotopyCategory.Plus.quasiIso (Modules Y)) :=
      (HomotopyCategory.Plus.localizerMorphism_derives _).hasPointwiseRightDerivedFunctor
    exact Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _
  refine (moduleGlobalSections Y).quasiIso_mapHomologicalComplex_of_rightAcyclic J'.ι
    (CochainComplex.plus_mapHomologicalComplex_obj
      (RingedSpaceModuleAdjunction.modulePushforward f) I.boundedBelow) J'.boundedBelow
    (fun n => ?_) (fun n => ?_)
  · exact DerivedPushforwardSections.rightAcyclic_modulePushforward_obj f ⊤
      (I.cocomplex.X n) (I.injective n)
  · have : Injective (J'.cocomplex.X n) := J'.injective n
    exact (moduleGlobalSections Y).rightAcyclic_of_injective (J'.cocomplex.X n)

variable [EnoughInjectives (Modules X)] [EnoughInjectives (Modules Y)]
  [HasSheafify (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat]
  [(Opens.grothendieckTopology (X : TopCat)).WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify (Opens.grothendieckTopology (Y : TopCat)) AddCommGrpCat]
  [(Opens.grothendieckTopology (Y : TopCat)).WEqualsLocallyBijective AddCommGrpCat]

/-- **The representative of the functorial map on derived global sections afforded by choices
of injective resolutions and a lift `β`**: it is the lower horizontal map of [Stacks, Tag 01FB]
followed by the inverse of the vertical quasi-isomorphism. -/
@[stacks 01FB "the roof representing the functorial map", ega "0 12.1.4" "inj. resolution constr."]
noncomputable def injectiveResolutionGlobalSectionsMap {G : Modules Y} {F : Modules X}
    (φ : (RingedSpaceModuleAdjunction.modulePullback f).obj G ⟶ F)
    (I : CochainComplex.InjectiveResolution
      ((CochainComplex.singleFunctor (Modules X) 0).obj F))
    (J : CochainComplex.InjectiveResolution
      ((CochainComplex.singleFunctor (Modules Y) 0).obj G))
    (J' : CochainComplex.InjectiveResolution (modulePushforwardComplex f I.cocomplex))
    (β : J.cocomplex ⟶ J'.cocomplex)
    (_hβ : J.ι ≫ β =
      (CochainComplex.singleFunctor (Modules Y) 0).map
          (RingedSpaceModuleAdjunction.homEquiv f F G φ) ≫
        (HomologicalComplex.singleMapHomologicalComplex
            (RingedSpaceModuleAdjunction.modulePushforward f)
            (ComplexShape.up ℤ) 0).inv.app F ≫
        ((RingedSpaceModuleAdjunction.modulePushforward f).mapHomologicalComplex
            (ComplexShape.up ℤ)).map I.ι ≫ J'.ι) :
    DerivedCategory.Q.obj (moduleGlobalSectionsComplex Y J.cocomplex) ⟶
      DerivedCategory.Q.obj
        (moduleGlobalSectionsComplex Y (modulePushforwardComplex f I.cocomplex)) :=
  have : QuasiIso (((moduleGlobalSections Y).mapHomologicalComplex
      (ComplexShape.up ℤ)).map J'.ι) :=
    quasiIso_moduleGlobalSections_map_pushforwardResolution f I J'
  DerivedCategory.Q.map
      (((moduleGlobalSections Y).mapHomologicalComplex (ComplexShape.up ℤ)).map β) ≫
    inv (DerivedCategory.Q.map
      (((moduleGlobalSections Y).mapHomologicalComplex (ComplexShape.up ℤ)).map J'.ι))

section DerivedSquare

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory D]
  [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C]
  (F₁ : A ⥤ B) (G₁ : B ⥤ D) (F₂ : A ⥤ C) (G₂ : C ⥤ D)
  [F₁.Additive] [G₁.Additive] [F₂.Additive] [G₂.Additive]
  (e : F₁ ⋙ G₁ ≅ F₂ ⋙ G₂)
  (h₁ : ∀ I : A, Injective I → G₁.rightAcyclic (F₁.obj I))
  (h₂ : ∀ I : A, Injective I → G₂.rightAcyclic (F₂.obj I))

/-- **The composite of the canonical comparison of [Stacks, Tag 015M] with the derived square
of a commutative square of additive functors is pinned down by the derived-functor units.**
Composed with the unit of `R(G₁ ∘ F₁)`, it is the coherence comparison of the induced functors
on bounded-below homotopy categories, followed by the unit of `RG₂` and the image of the unit
of `RF₂`. Since those units determine both the canonical comparison and the derived square,
this equation determines the composite. -/
theorem rightDerivedFunctorPlusUnit_comp_compIso_trans_squareIso_hom_app
    (K : HomotopyCategory.Plus A)
    {w : DerivedCategory.Plus.Qh.obj ((F₁ ⋙ G₁).mapHomotopyCategoryPlus.obj K) ⟶
      DerivedCategory.Plus.Qh.obj
        ((F₂.mapHomotopyCategoryPlus ⋙ G₂.mapHomotopyCategoryPlus).obj K)}
    (hw : DerivedCategory.Plus.Qh.map
        ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F₁ ⋙ G₁))).inv.app K ≫
          (Functor.mapHomotopyCategoryPlusCompIso (F := F₁) (G := G₁) e).hom.app K ≫
          (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F₂ ⋙ G₂))).inv.app K) = w) :
    (F₁ ⋙ G₁).rightDerivedFunctorPlusUnith.app K ≫
        (DerivedPushforwardSections.compIso F₁ G₁ h₁ ≪≫
            DerivedPushforwardSections.squareIso F₁ G₁ F₂ G₂ e h₁ h₂).hom.app
          (DerivedCategory.Plus.Qh.obj K) =
      w ≫ G₂.rightDerivedFunctorPlusUnith.app (F₂.mapHomotopyCategoryPlus.obj K) ≫
        G₂.rightDerivedFunctorPlus.map (F₂.rightDerivedFunctorPlusUnith.app K) := by
  subst hw
  rw [Iso.trans_hom, NatTrans.comp_app, ← Category.assoc,
    DerivedPushforwardSections.compIso_hom,
    Functor.rightDerivedFunctorPlusComp_fac_app]
  simp only [Category.assoc]
  rw [DerivedPushforwardSections.squareIso_hom_app, ← Category.assoc, ← Functor.map_comp]

end DerivedSquare

/-- **The derived-sections comparison of [Stacks, Tag 01EZ] at `⊤` is the one induced by the
derived-functor units.** Composed with the unit of the right derived functor of global sections
on `X` followed by restriction of scalars, the comparison
`Stacks.Cohomology.derivedModuleGlobalSectionsAlongIso` is the unit of the right derived
functor of global sections on `Y` followed by the image of the unit of the derived pushforward.
This is the equation that pins the comparison down, and it is what identifies the roof of
[Stacks, Tag 01FB] with the canonical map of [Stacks, Tag 01F9]. -/
theorem rightDerivedFunctorPlusUnit_comp_derivedModuleGlobalSectionsAlongIso_hom
    (K : HomotopyCategory.Plus (Modules X)) :
    (moduleGlobalSections X ⋙ restrictGlobalScalars f).rightDerivedFunctorPlusUnith.app K ≫
        (derivedModuleGlobalSectionsAlongIso f).hom.app (DerivedCategory.Plus.Qh.obj K) =
      (moduleGlobalSections Y).rightDerivedFunctorPlusUnith.app
          ((RingedSpaceModuleAdjunction.modulePushforward f).mapHomotopyCategoryPlus.obj K) ≫
        (moduleGlobalSections Y).rightDerivedFunctorPlus.map
          ((RingedSpaceModuleAdjunction.modulePushforward f).rightDerivedFunctorPlusUnith.app
            K) := by
  have hid : (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl
            (SheafOfModules.evaluation.{u} (structureSheafRing X)
                (op ((RingedSpaceModuleAdjunction.opensMap f).obj ⊤)) ⋙
              ModuleCat.restrictScalars.{u}
                ((RingedSpaceModuleAdjunction.structureSheafHom f).hom.app
                  (op ⊤)).hom))).inv.app K ≫
        (Functor.mapHomotopyCategoryPlusCompIso
          (DerivedPushforwardSections.sectionsRestrictionIso f ⊤)).hom.app K ≫
        (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl
          (RingedSpaceModuleAdjunction.modulePushforward f ⋙
            SheafOfModules.evaluation.{u} (structureSheafRing Y)
              (op ⊤)))).inv.app K = 𝟙 _ := by
    apply ObjectProperty.hom_ext
    rfl
  have hzero := (congrArg (fun m => DerivedCategory.Plus.Qh.map m) hid).trans
    (DerivedCategory.Plus.Qh.map_id _)
  have h := rightDerivedFunctorPlusUnit_comp_compIso_trans_squareIso_hom_app
    (SheafOfModules.evaluation.{u} (structureSheafRing X)
      (op ((RingedSpaceModuleAdjunction.opensMap f).obj ⊤)))
    (ModuleCat.restrictScalars.{u}
      ((RingedSpaceModuleAdjunction.structureSheafHom f).hom.app (op ⊤)).hom)
    (RingedSpaceModuleAdjunction.modulePushforward f)
    (SheafOfModules.evaluation.{u} (structureSheafRing Y) (op ⊤))
    (DerivedPushforwardSections.sectionsRestrictionIso f ⊤)
    (fun _ _ => DerivedPushforwardSections.rightAcyclic_restrictScalars _ _)
    (DerivedPushforwardSections.rightAcyclic_modulePushforward_obj f ⊤) K hzero
  exact h.trans (Category.id_comp _)

/-- **The canonical resolution comparison for `RΓ(X, F)`, regarded over `Γ(Y, 𝒪_Y)`.** It
identifies the derived global sections of `F` on `X`, with scalars restricted along
`Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)`, with the global sections on `Y` of the pushforward of a chosen
injective resolution of `F[0]`. Global sections of a pushforward and global sections on the
source with restricted scalars agree degree by degree, so this is the comparison of
`CategoryTheory.Functor.rightDerivedFunctorPlusInjectiveResolutionIso` for the composite
functor. It is built from `I.ι` and the derived-functor unit, so it cannot be replaced by an
arbitrary isomorphism. -/
noncomputable def derivedModuleGlobalSectionsAlongResolutionIso {F : Modules X}
    (I : CochainComplex.InjectiveResolution
      ((CochainComplex.singleFunctor (Modules X) 0).obj F)) :
    DerivedCategory.Plus.ι.obj ((derivedModuleGlobalSectionsAlong f).obj
        ((DerivedCategory.Plus.singleFunctor (Modules X) 0).obj F)) ≅
      DerivedCategory.Q.obj
        (moduleGlobalSectionsComplex Y (modulePushforwardComplex f I.cocomplex)) :=
  (moduleGlobalSections X ⋙
    restrictGlobalScalars f).rightDerivedFunctorPlusInjectiveResolutionIso F I

/-- **The comparison of the global sections of a pushed-forward bounded-below complex with the
right derived functor factors through the derived pushforward.** This is the form in which the
comparison of [Stacks, Tag 01EZ] enters the identification of [Stacks, Tag 01FB]. -/
theorem mapHomologicalComplexDerivedUnit_comp_alongIso_hom
    {K : CochainComplex (Modules X) ℤ} (hK : CochainComplex.plus (Modules X) K) :
    (moduleGlobalSections X ⋙ restrictGlobalScalars f).mapHomologicalComplexDerivedUnit hK ≫
        DerivedCategory.Plus.ι.map ((derivedModuleGlobalSectionsAlongIso f).hom.app
          (DerivedCategory.Plus.Qh.obj
            ((HomotopyCategory.Plus.quotient (Modules X)).obj ⟨K, hK⟩))) =
      (moduleGlobalSections Y).mapHomologicalComplexDerivedUnit
          (CochainComplex.plus_mapHomologicalComplex_obj
            (RingedSpaceModuleAdjunction.modulePushforward f) hK) ≫
        DerivedCategory.Plus.ι.map ((moduleGlobalSections Y).rightDerivedFunctorPlus.map
          ((RingedSpaceModuleAdjunction.modulePushforward f).rightDerivedFunctorPlusUnith.app
            ((HomotopyCategory.Plus.quotient (Modules X)).obj ⟨K, hK⟩))) := by
  have hQ : ((moduleGlobalSections X ⋙
        restrictGlobalScalars f).mapHomologicalComplexQhIso hK).inv =
      ((moduleGlobalSections Y).mapHomologicalComplexQhIso
        (CochainComplex.plus_mapHomologicalComplex_obj
          (RingedSpaceModuleAdjunction.modulePushforward f) hK)).inv :=
    rfl
  have hiota : DerivedCategory.Plus.ι.map
          ((moduleGlobalSections X ⋙ restrictGlobalScalars f).rightDerivedFunctorPlusUnith.app
            ((HomotopyCategory.Plus.quotient (Modules X)).obj ⟨K, hK⟩)) ≫
        DerivedCategory.Plus.ι.map ((derivedModuleGlobalSectionsAlongIso f).hom.app
          (DerivedCategory.Plus.Qh.obj
            ((HomotopyCategory.Plus.quotient (Modules X)).obj ⟨K, hK⟩))) =
      DerivedCategory.Plus.ι.map ((moduleGlobalSections Y).rightDerivedFunctorPlusUnith.app
          ((RingedSpaceModuleAdjunction.modulePushforward f).mapHomotopyCategoryPlus.obj
            ((HomotopyCategory.Plus.quotient (Modules X)).obj ⟨K, hK⟩))) ≫
        DerivedCategory.Plus.ι.map ((moduleGlobalSections Y).rightDerivedFunctorPlus.map
          ((RingedSpaceModuleAdjunction.modulePushforward f).rightDerivedFunctorPlusUnith.app
            ((HomotopyCategory.Plus.quotient (Modules X)).obj ⟨K, hK⟩))) :=
    ((DerivedCategory.Plus.ι.map_comp _ _).symm.trans
        (congrArg (fun m => DerivedCategory.Plus.ι.map m)
          (rightDerivedFunctorPlusUnit_comp_derivedModuleGlobalSectionsAlongIso_hom f
            ((HomotopyCategory.Plus.quotient (Modules X)).obj ⟨K, hK⟩)))).trans
      (DerivedCategory.Plus.ι.map_comp _ _)
  dsimp only [Functor.mapHomologicalComplexDerivedUnit]
  rw [hQ]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => ((moduleGlobalSections Y).mapHomologicalComplexQhIso
        (CochainComplex.plus_mapHomologicalComplex_obj
          (RingedSpaceModuleAdjunction.modulePushforward f) hK)).inv ≫ z) hiota).trans
      (Category.assoc _ _ _).symm)

section SingleResolution

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A] (T : A ⥤ B) [T.Additive]

/-- **The canonical comparison `T(Z)[0] ⟶ RT(Z[0])`, read on an injective resolution.**
Composed with the right derived functor of the localized resolution map, it is the morphism out
of `T(Z)[0]` attached to the termwise image of the resolution map, followed by the unit of the
right derived functor. The displayed left-hand side is the component at `Z` of the natural
transformation assembled from the comparison of `T` with `Z ↦ Z[0]` and the derived-functor
unit; `Stacks.Cohomology.derivedPushforwardSingleNatTrans` is that transformation for the
pushforward of sheaves of modules. -/
theorem mapSingleFunctorPlusCompQhIso_inv_app_comp_map_qhHom (Z : A)
    (I : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor A 0).obj Z)) :
    (T.mapSingleFunctorPlusCompQhIso.inv.app Z ≫
          T.rightDerivedFunctorPlusUnith.app
            ((HomotopyCategory.Plus.singleFunctor A 0).obj Z) ≫
          T.rightDerivedFunctorPlus.map
            ((DerivedCategory.Plus.singleFunctorIsoCompQh A 0).inv.app Z)) ≫
        T.rightDerivedFunctorPlus.map (CochainComplex.InjectiveResolution.qhHom Z I) =
      DerivedCategory.Plus.qhHomMk
          (K := (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cocomplex) (T.obj Z)
          (CochainComplex.plus_mapHomologicalComplex_obj T I.boundedBelow)
          ((HomologicalComplex.singleMapHomologicalComplex T (ComplexShape.up ℤ) 0).inv.app Z ≫
            (T.mapHomologicalComplex (ComplexShape.up ℤ)).map I.ι) ≫
        T.rightDerivedFunctorPlusUnith.app
          ((HomotopyCategory.Plus.quotient A).obj ⟨I.cocomplex, I.boundedBelow⟩) := by
  have hq : CochainComplex.InjectiveResolution.qhHom Z I =
      (DerivedCategory.Plus.singleFunctorIsoCompQh A 0).hom.app Z ≫
        DerivedCategory.Plus.Qh.map (HomotopyCategory.Plus.quotientHomMk
          (CochainComplex.plus_singleFunctor_obj Z) I.boundedBelow I.ι) :=
    rfl
  have hcancel : T.rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctorIsoCompQh A 0).inv.app Z) ≫
      T.rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctorIsoCompQh A 0).hom.app Z) = 𝟙 _ :=
    ((T.rightDerivedFunctorPlus.map_comp _ _).symm.trans
      (congrArg T.rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctorIsoCompQh A 0).inv_hom_id_app Z))).trans
      (T.rightDerivedFunctorPlus.map_id _)
  have hnat : DerivedCategory.Plus.Qh.map (T.mapHomotopyCategoryPlus.map
          (HomotopyCategory.Plus.quotientHomMk
            (CochainComplex.plus_singleFunctor_obj Z) I.boundedBelow I.ι)) ≫
        T.rightDerivedFunctorPlusUnith.app
          ((HomotopyCategory.Plus.quotient A).obj ⟨I.cocomplex, I.boundedBelow⟩) =
      T.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.singleFunctor A 0).obj Z) ≫
        T.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map
          (HomotopyCategory.Plus.quotientHomMk
            (CochainComplex.plus_singleFunctor_obj Z) I.boundedBelow I.ι)) :=
    T.rightDerivedFunctorPlusUnith.naturality _
  have hmhc := T.mapHomotopyCategoryPlus_map_quotientHomMk
    (CochainComplex.plus_singleFunctor_obj Z) I.boundedBelow I.ι
  have hmS := T.mapSingleFunctorPlusCompQhIso_inv_app_eq_qhHomMk Z
  have hqc := DerivedCategory.Plus.qhHomMk_comp (T.obj Z)
    (CochainComplex.plus_mapHomologicalComplex_obj T (CochainComplex.plus_singleFunctor_obj Z))
    (CochainComplex.plus_mapHomologicalComplex_obj T I.boundedBelow)
    ((HomologicalComplex.singleMapHomologicalComplex T (ComplexShape.up ℤ) 0).inv.app Z)
    ((T.mapHomologicalComplex (ComplexShape.up ℤ)).map I.ι)
  rw [hq, Functor.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (T.rightDerivedFunctorPlus.map
      ((DerivedCategory.Plus.singleFunctorIsoCompQh A 0).inv.app Z)), hcancel, Category.id_comp,
    ← hnat, hmhc, hmS]
  exact (Category.assoc _ _ _).symm.trans (congrArg
    (fun z => z ≫ T.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient A).obj ⟨I.cocomplex, I.boundedBelow⟩)) hqc)

end SingleResolution

/-- The morphism `G[0] ⟶ Q(f_* I⁼)` out of which the roof of [Stacks, Tag 01FB] is built: the
`f`-map in its adjoint form, followed by the comparison of `(f_* F)[0]` with `f_*(F[0])` and the
termwise pushforward of the resolution map. -/
private noncomputable abbrev pushforwardResolutionHom {G : Modules Y} {F : Modules X}
    (ψ : G ⟶ (RingedSpaceModuleAdjunction.modulePushforward f).obj F)
    (I : CochainComplex.InjectiveResolution
      ((CochainComplex.singleFunctor (Modules X) 0).obj F)) :
    (DerivedCategory.Plus.singleFunctor (Modules Y) 0).obj G ⟶
      DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient (Modules Y)).obj
        ⟨modulePushforwardComplex f I.cocomplex,
          plus_modulePushforwardComplex f I.boundedBelow⟩) :=
  DerivedCategory.Plus.qhHomMk (K := modulePushforwardComplex f I.cocomplex) G
    (plus_modulePushforwardComplex f I.boundedBelow)
    ((CochainComplex.singleFunctor (Modules Y) 0).map ψ ≫
      (HomologicalComplex.singleMapHomologicalComplex
          (RingedSpaceModuleAdjunction.modulePushforward f) (ComplexShape.up ℤ) 0).inv.app F ≫
        ((RingedSpaceModuleAdjunction.modulePushforward f).mapHomologicalComplex
          (ComplexShape.up ℤ)).map I.ι)

omit [EnoughInjectives (Modules Y)] in
/-- **The morphism `G[0] ⟶ Rf_*(F[0])` of [Stacks, Tag 01F8], read on an injective
resolution.** Composed with the derived pushforward of the localized resolution map, it is
`Stacks.Cohomology.pushforwardResolutionHom` followed by the unit of the derived pushforward.
This is the second step of the identification asserted by [Stacks, Tag 01FB]. -/
private lemma derivedPushforwardSingleNatTrans_app_comp_map_qhHom {G : Modules Y}
    {F : Modules X} (ψ : G ⟶ (RingedSpaceModuleAdjunction.modulePushforward f).obj F)
    (I : CochainComplex.InjectiveResolution
      ((CochainComplex.singleFunctor (Modules X) 0).obj F)) :
    ((DerivedCategory.Plus.singleFunctor (Modules Y) 0).map ψ ≫
          (derivedPushforwardSingleNatTrans f).app F) ≫
        (RingedSpaceModuleAdjunction.modulePushforward f).rightDerivedFunctorPlus.map
          (CochainComplex.InjectiveResolution.qhHom F I) =
      pushforwardResolutionHom f ψ I ≫
        (RingedSpaceModuleAdjunction.modulePushforward f).rightDerivedFunctorPlusUnith.app
          ((HomotopyCategory.Plus.quotient (Modules X)).obj ⟨I.cocomplex, I.boundedBelow⟩) := by
  have h1 : (derivedPushforwardSingleNatTrans f).app F ≫
        (RingedSpaceModuleAdjunction.modulePushforward f).rightDerivedFunctorPlus.map
          (CochainComplex.InjectiveResolution.qhHom F I) =
      DerivedCategory.Plus.qhHomMk (K := modulePushforwardComplex f I.cocomplex)
          ((RingedSpaceModuleAdjunction.modulePushforward f).obj F)
          (plus_modulePushforwardComplex f I.boundedBelow)
          ((HomologicalComplex.singleMapHomologicalComplex
                (RingedSpaceModuleAdjunction.modulePushforward f)
                (ComplexShape.up ℤ) 0).inv.app F ≫
            ((RingedSpaceModuleAdjunction.modulePushforward f).mapHomologicalComplex
              (ComplexShape.up ℤ)).map I.ι) ≫
        (RingedSpaceModuleAdjunction.modulePushforward f).rightDerivedFunctorPlusUnith.app
          ((HomotopyCategory.Plus.quotient (Modules X)).obj ⟨I.cocomplex, I.boundedBelow⟩) :=
    mapSingleFunctorPlusCompQhIso_inv_app_comp_map_qhHom
      (RingedSpaceModuleAdjunction.modulePushforward f) F I
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => (DerivedCategory.Plus.singleFunctor (Modules Y) 0).map ψ ≫ z) h1).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun z => z ≫
            (RingedSpaceModuleAdjunction.modulePushforward f).rightDerivedFunctorPlusUnith.app
              ((HomotopyCategory.Plus.quotient (Modules X)).obj ⟨I.cocomplex, I.boundedBelow⟩))
          (DerivedCategory.Plus.singleFunctor_map_comp_qhHomMk ψ
            (plus_modulePushforwardComplex f I.boundedBelow) _))))

/-- **The canonical functorial map of [Stacks, Tag 01F9], read on an injective resolution.**
Followed by the derived global sections of the localized resolution map and the comparison of
[Stacks, Tag 01EZ], the map `Stacks.Cohomology.derivedModuleGlobalSectionsMap` is the derived
global sections on `Y` of `Stacks.Cohomology.pushforwardResolutionHom` followed by the unit of
the derived pushforward. This is the third step of the identification asserted by
[Stacks, Tag 01FB]. -/
private lemma derivedModuleGlobalSectionsMap_comp_map_qhHom {G : Modules Y} {F : Modules X}
    (φ : (RingedSpaceModuleAdjunction.modulePullback f).obj G ⟶ F)
    (I : CochainComplex.InjectiveResolution
      ((CochainComplex.singleFunctor (Modules X) 0).obj F)) :
    derivedModuleGlobalSectionsMap f φ ≫
        (moduleGlobalSections X ⋙ restrictGlobalScalars f).rightDerivedFunctorPlus.map
          (CochainComplex.InjectiveResolution.qhHom F I) ≫
        (derivedModuleGlobalSectionsAlongIso f).hom.app
          (DerivedCategory.Plus.Qh.obj
            ((HomotopyCategory.Plus.quotient (Modules X)).obj ⟨I.cocomplex, I.boundedBelow⟩)) =
      (moduleGlobalSections Y).rightDerivedFunctorPlus.map
        (pushforwardResolutionHom f (RingedSpaceModuleAdjunction.homEquiv f F G φ) I ≫
          (RingedSpaceModuleAdjunction.modulePushforward f).rightDerivedFunctorPlusUnith.app
            ((HomotopyCategory.Plus.quotient (Modules X)).obj
              ⟨I.cocomplex, I.boundedBelow⟩)) := by
  have hdef : derivedModuleGlobalSectionsMap f φ =
      (moduleGlobalSections Y).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor (Modules Y) 0).map
              (RingedSpaceModuleAdjunction.homEquiv f F G φ) ≫
            (derivedPushforwardSingleNatTrans f).app F) ≫
        (derivedModuleGlobalSectionsAlongIso f).inv.app
          ((DerivedCategory.Plus.singleFunctor (Modules X) 0).obj F) :=
    rfl
  have h2 : (derivedModuleGlobalSectionsAlongIso f).inv.app
          ((DerivedCategory.Plus.singleFunctor (Modules X) 0).obj F) ≫
        (moduleGlobalSections X ⋙ restrictGlobalScalars f).rightDerivedFunctorPlus.map
            (CochainComplex.InjectiveResolution.qhHom F I) ≫
          (derivedModuleGlobalSectionsAlongIso f).hom.app
            (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient (Modules X)).obj
              ⟨I.cocomplex, I.boundedBelow⟩)) =
      (moduleGlobalSections Y).rightDerivedFunctorPlus.map
        ((RingedSpaceModuleAdjunction.modulePushforward f).rightDerivedFunctorPlus.map
          (CochainComplex.InjectiveResolution.qhHom F I)) :=
    NatIso.naturality_1 (derivedModuleGlobalSectionsAlongIso f) _
  refine Eq.trans ?_ (((moduleGlobalSections Y).rightDerivedFunctorPlus.map_comp
      ((DerivedCategory.Plus.singleFunctor (Modules Y) 0).map
          (RingedSpaceModuleAdjunction.homEquiv f F G φ) ≫
        (derivedPushforwardSingleNatTrans f).app F) _).symm.trans
    (congrArg (moduleGlobalSections Y).rightDerivedFunctorPlus.map
      (derivedPushforwardSingleNatTrans_app_comp_map_qhHom f
        (RingedSpaceModuleAdjunction.homEquiv f F G φ) I)))
  exact (congrArg (fun z => z ≫
        (moduleGlobalSections X ⋙ restrictGlobalScalars f).rightDerivedFunctorPlus.map
            (CochainComplex.InjectiveResolution.qhHom F I) ≫
          (derivedModuleGlobalSectionsAlongIso f).hom.app
            (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient (Modules X)).obj
              ⟨I.cocomplex, I.boundedBelow⟩))) hdef).trans
    ((Category.assoc _ _ _).trans
      (congrArg (fun z => (moduleGlobalSections Y).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor (Modules Y) 0).map
              (RingedSpaceModuleAdjunction.homEquiv f F G φ) ≫
            (derivedPushforwardSingleNatTrans f).app F) ≫ z) h2))

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- The unit `rightDerivedFunctorPlusUnith` (whose definition Mathlib does not expose) is
invertible at `K` when the unit of `Functor.totalRightDerived` is: both are units of right derived
functors of the same functor. -/
private lemma isIso_rightDerivedFunctorPlusUnith_app_of_isIso_totalRightDerivedUnit
    {D : Type*} {E : Type*} [Category* D] [Category* E] [Abelian D] [Abelian E]
    [HasDerivedCategory D] [HasDerivedCategory E] (G : D ⥤ E) [G.Additive]
    [EnoughInjectives D] (K : HomotopyCategory.Plus D)
    (h : IsIso (((G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
        DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso D)).app K)) :
    IsIso (G.rightDerivedFunctorPlusUnith.app K) := by
  have : IsIso (G.rightDerivedFunctorPlus.rightDerivedDesc G.rightDerivedFunctorPlusUnith
      (HomotopyCategory.Plus.quasiIso D) _
      ((G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
        DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso D))) :=
    (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc _ _ _ _ _).1 inferInstance
  rw [← Functor.rightDerived_fac_app G.rightDerivedFunctorPlus G.rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso D) _
    ((G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
      DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso D)) K] at h
  exact (isIso_comp_right_iff _ _).1 h

/-- The comparison of a bounded-below complex with the right derived functor is invertible when
every term is right acyclic. -/
private lemma isIso_mapHomologicalComplexDerivedUnit_of_rightAcyclic
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A] (T : A ⥤ B) [T.Additive]
    {K : CochainComplex A ℤ} (hK : CochainComplex.plus A K) (h : ∀ n, T.rightAcyclic (K.X n)) :
    IsIso (T.mapHomologicalComplexDerivedUnit hK) := by
  have hderives : (T.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A) :=
    Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _
  have hunit : IsIso (T.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient A).obj ⟨K, hK⟩)) :=
    isIso_rightDerivedFunctorPlusUnith_app_of_isIso_totalRightDerivedUnit T _
      (T.isIso_totalRightDerivedUnit_app_of_rightAcyclic K hK h)
  exact inferInstanceAs (IsIso ((T.mapHomologicalComplexQhIso hK).inv ≫
    DerivedCategory.Plus.ι.map (T.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient A).obj ⟨K, hK⟩))))

omit [EnoughInjectives (Modules X)] in
/-- The comparison of the global sections of a pushed-forward injective resolution with the
right derived functor is invertible: by part (2) of [Stacks, Tag 01EX] the terms of the
pushed-forward resolution have right acyclic global sections. -/
private lemma isIso_mapHomologicalComplexDerivedUnit_pushforward {F : Modules X}
    (I : CochainComplex.InjectiveResolution
      ((CochainComplex.singleFunctor (Modules X) 0).obj F)) :
    IsIso ((moduleGlobalSections Y).mapHomologicalComplexDerivedUnit
      (plus_modulePushforwardComplex f I.boundedBelow)) :=
  isIso_mapHomologicalComplexDerivedUnit_of_rightAcyclic _ _
    (fun n => DerivedPushforwardSections.rightAcyclic_modulePushforward_obj f ⊤
      (I.cocomplex.X n) (I.injective n))

omit [EnoughInjectives (Modules Y)]
  [HasSheafify (Opens.grothendieckTopology (Y : TopCat)) AddCommGrpCat]
  [(Opens.grothendieckTopology (Y : TopCat)).WEqualsLocallyBijective AddCommGrpCat] in
/-- The comparison of `Stacks.Cohomology.derivedModuleGlobalSectionsAlongResolutionIso` with the
right derived functor is invertible: an injective sheaf of modules is right acyclic for global
sections. -/
private lemma isIso_mapHomologicalComplexDerivedUnit_along {F : Modules X}
    (I : CochainComplex.InjectiveResolution
      ((CochainComplex.singleFunctor (Modules X) 0).obj F)) :
    IsIso ((moduleGlobalSections X ⋙
      restrictGlobalScalars f).mapHomologicalComplexDerivedUnit I.boundedBelow) :=
  isIso_mapHomologicalComplexDerivedUnit_of_rightAcyclic _ _ (fun n => by
    have : Injective (I.cocomplex.X n) := I.injective n
    exact (moduleGlobalSections X ⋙ restrictGlobalScalars f).rightAcyclic_of_injective
      (I.cocomplex.X n))

/-- The derived global sections on `Y` of the unit of the derived pushforward at a complex of
injective sheaves of modules is invertible. It is read off the comparison of
[Stacks, Tag 01EZ], in which the other three morphisms are invertible. -/
private lemma isIso_iotaMap_map_derivedPushforwardUnit {F : Modules X}
    (I : CochainComplex.InjectiveResolution
      ((CochainComplex.singleFunctor (Modules X) 0).obj F)) :
    IsIso (DerivedCategory.Plus.ι.map ((moduleGlobalSections Y).rightDerivedFunctorPlus.map
      ((RingedSpaceModuleAdjunction.modulePushforward f).rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.quotient (Modules X)).obj
          ⟨I.cocomplex, I.boundedBelow⟩)))) := by
  have h1 := isIso_mapHomologicalComplexDerivedUnit_along f I
  have h2 := isIso_mapHomologicalComplexDerivedUnit_pushforward f I
  have hiso : IsIso ((moduleGlobalSections X ⋙
      restrictGlobalScalars f).mapHomologicalComplexDerivedUnit I.boundedBelow ≫
    DerivedCategory.Plus.ι.map ((derivedModuleGlobalSectionsAlongIso f).hom.app
      (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient (Modules X)).obj
        ⟨I.cocomplex, I.boundedBelow⟩)))) :=
    IsIso.comp_isIso' h1 (inferInstanceAs (IsIso (DerivedCategory.Plus.ι.map
      ((derivedModuleGlobalSectionsAlongIso f).hom.app
        (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient (Modules X)).obj
          ⟨I.cocomplex, I.boundedBelow⟩))))))
  have hm : (moduleGlobalSections Y).mapHomologicalComplexDerivedUnit
        (plus_modulePushforwardComplex f I.boundedBelow) ≫
      DerivedCategory.Plus.ι.map ((moduleGlobalSections Y).rightDerivedFunctorPlus.map
        ((RingedSpaceModuleAdjunction.modulePushforward f).rightDerivedFunctorPlusUnith.app
          ((HomotopyCategory.Plus.quotient (Modules X)).obj ⟨I.cocomplex, I.boundedBelow⟩))) =
    (moduleGlobalSections X ⋙ restrictGlobalScalars f).mapHomologicalComplexDerivedUnit
        I.boundedBelow ≫
      DerivedCategory.Plus.ι.map ((derivedModuleGlobalSectionsAlongIso f).hom.app
        (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient (Modules X)).obj
          ⟨I.cocomplex, I.boundedBelow⟩))) :=
    (mapHomologicalComplexDerivedUnit_comp_alongIso_hom f I.boundedBelow).symm
  refine (isIso_comp_left_iff ((moduleGlobalSections Y).mapHomologicalComplexDerivedUnit
    (plus_modulePushforwardComplex f I.boundedBelow)) _).1 ?_
  exact (congrArg (fun g => IsIso g) hm).mpr hiso

/-- **The canonical functorial map of [Stacks, Tag 01F9], read through the resolution
comparison of `RΓ(X, F)`.** Followed by the comparison
`Stacks.Cohomology.derivedModuleGlobalSectionsAlongResolutionIso` and by the comparison of the
global sections of the pushed-forward resolution with the right derived functor, it is the
derived global sections on `Y` of `Stacks.Cohomology.pushforwardResolutionHom`. This is the
fourth step of the identification asserted by [Stacks, Tag 01FB]. -/
private lemma iotaMap_derivedModuleGlobalSectionsMap_comp_alongResolutionIso_hom
    {G : Modules Y} {F : Modules X}
    (φ : (RingedSpaceModuleAdjunction.modulePullback f).obj G ⟶ F)
    (I : CochainComplex.InjectiveResolution
      ((CochainComplex.singleFunctor (Modules X) 0).obj F)) :
    DerivedCategory.Plus.ι.map (derivedModuleGlobalSectionsMap f φ) ≫
        (derivedModuleGlobalSectionsAlongResolutionIso f I).hom ≫
        (moduleGlobalSections Y).mapHomologicalComplexDerivedUnit
          (plus_modulePushforwardComplex f I.boundedBelow) =
      DerivedCategory.Plus.ι.map ((moduleGlobalSections Y).rightDerivedFunctorPlus.map
        (pushforwardResolutionHom f (RingedSpaceModuleAdjunction.homEquiv f F G φ) I)) := by
  have hepsK := isIso_iotaMap_map_derivedPushforwardUnit f I
  have hm := mapHomologicalComplexDerivedUnit_comp_alongIso_hom f I.boundedBelow
  have hA : (derivedModuleGlobalSectionsAlongResolutionIso f I).hom ≫
      (moduleGlobalSections X ⋙ restrictGlobalScalars f).mapHomologicalComplexDerivedUnit
        I.boundedBelow =
    DerivedCategory.Plus.ι.map
      ((moduleGlobalSections X ⋙ restrictGlobalScalars f).rightDerivedFunctorPlus.map
        (CochainComplex.InjectiveResolution.qhHom F I)) :=
    (moduleGlobalSections X ⋙
      restrictGlobalScalars f).rightDerivedFunctorPlusInjectiveResolutionIso_hom_comp F I
  have hBig : (derivedModuleGlobalSectionsAlongResolutionIso f I).hom ≫
        (moduleGlobalSections Y).mapHomologicalComplexDerivedUnit
            (plus_modulePushforwardComplex f I.boundedBelow) ≫
          DerivedCategory.Plus.ι.map ((moduleGlobalSections Y).rightDerivedFunctorPlus.map
            ((RingedSpaceModuleAdjunction.modulePushforward f).rightDerivedFunctorPlusUnith.app
              ((HomotopyCategory.Plus.quotient (Modules X)).obj
                ⟨I.cocomplex, I.boundedBelow⟩))) =
      DerivedCategory.Plus.ι.map
        ((moduleGlobalSections X ⋙ restrictGlobalScalars f).rightDerivedFunctorPlus.map
            (CochainComplex.InjectiveResolution.qhHom F I) ≫
          (derivedModuleGlobalSectionsAlongIso f).hom.app
            (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient (Modules X)).obj
              ⟨I.cocomplex, I.boundedBelow⟩))) :=
    (congrArg (fun z => (derivedModuleGlobalSectionsAlongResolutionIso f I).hom ≫ z)
        hm.symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ DerivedCategory.Plus.ι.map
              ((derivedModuleGlobalSectionsAlongIso f).hom.app
                (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient (Modules X)).obj
                  ⟨I.cocomplex, I.boundedBelow⟩)))) hA).trans
          (DerivedCategory.Plus.ι.map_comp _ _).symm))
  refine (cancel_mono (DerivedCategory.Plus.ι.map
    ((moduleGlobalSections Y).rightDerivedFunctorPlus.map
      ((RingedSpaceModuleAdjunction.modulePushforward f).rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.quotient (Modules X)).obj
          ⟨I.cocomplex, I.boundedBelow⟩))))).1 ?_
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => DerivedCategory.Plus.ι.map (derivedModuleGlobalSectionsMap f φ) ≫ z)
        ((Category.assoc _ _ _).trans hBig)).trans
      ((DerivedCategory.Plus.ι.map_comp _ _).symm.trans
        ((congrArg DerivedCategory.Plus.ι.map
            (derivedModuleGlobalSectionsMap_comp_map_qhHom f φ I)).trans
          ((congrArg DerivedCategory.Plus.ι.map
              ((moduleGlobalSections Y).rightDerivedFunctorPlus.map_comp _ _)).trans
            (DerivedCategory.Plus.ι.map_comp _ _)))))

/-- **The roof of [Stacks, Tag 01FB] represents the canonical functorial map of
[Stacks, Tag 01F9].** Read through the canonical identifications of `RΓ(Y, G)` with
`Γ(Y, J⁼)` and of `RΓ(X, F)`, over `Γ(Y, 𝒪_Y)`, with `Γ(Y, f_* I⁼)`, the morphism
`Stacks.Cohomology.derivedModuleGlobalSectionsMap` attached to the `f`-map `φ` is the roof
`Stacks.Cohomology.injectiveResolutionGlobalSectionsMap` built from a lift `β` and the inverse
of the quasi-isomorphism `Γ(Y, f_* I⁼) ⟶ Γ(Y, J'⁼)`. Both comparisons are built from `I.ι`,
`J.ι` and the derived-functor units, so neither can be replaced by an arbitrary isomorphism,
and `CategoryTheory.DerivedCategory.Plus.ι` displays the bounded-below objects in the
unbounded derived category in which the roof was defined. -/
@[stacks 01FB "identification with the canonical functorial map",
  ega "0 12.1.4" "inj. resolution descr."]
theorem derivedModuleGlobalSectionsMap_eq_injectiveResolutionGlobalSectionsMap
    {G : Modules Y} {F : Modules X}
    (φ : (RingedSpaceModuleAdjunction.modulePullback f).obj G ⟶ F)
    (I : CochainComplex.InjectiveResolution
      ((CochainComplex.singleFunctor (Modules X) 0).obj F))
    (J : CochainComplex.InjectiveResolution
      ((CochainComplex.singleFunctor (Modules Y) 0).obj G))
    (J' : CochainComplex.InjectiveResolution (modulePushforwardComplex f I.cocomplex))
    (β : J.cocomplex ⟶ J'.cocomplex)
    (hβ : J.ι ≫ β =
      (CochainComplex.singleFunctor (Modules Y) 0).map
          (RingedSpaceModuleAdjunction.homEquiv f F G φ) ≫
        (HomologicalComplex.singleMapHomologicalComplex
            (RingedSpaceModuleAdjunction.modulePushforward f)
            (ComplexShape.up ℤ) 0).inv.app F ≫
        ((RingedSpaceModuleAdjunction.modulePushforward f).mapHomologicalComplex
            (ComplexShape.up ℤ)).map I.ι ≫ J'.ι) :
    ((moduleGlobalSections Y).rightDerivedFunctorPlusInjectiveResolutionIso G J).hom ≫
        injectiveResolutionGlobalSectionsMap f φ I J J' β hβ =
      DerivedCategory.Plus.ι.map (derivedModuleGlobalSectionsMap f φ) ≫
        (derivedModuleGlobalSectionsAlongResolutionIso f I).hom := by
  have hQd : QuasiIso (((moduleGlobalSections Y).mapHomologicalComplex
      (ComplexShape.up ℤ)).map J'.ι) :=
    quasiIso_moduleGlobalSections_map_pushforwardResolution f I J'
  have hp := isIso_mapHomologicalComplexDerivedUnit_pushforward f I
  have hQc : IsIso (DerivedCategory.Plus.Qh.map (HomotopyCategory.Plus.quotientHomMk
      (plus_modulePushforwardComplex f I.boundedBelow) J'.boundedBelow J'.ι)) :=
    Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso (Modules Y)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 (by
        change QuasiIso J'.ι
        infer_instance))
  have hlift : pushforwardResolutionHom f (RingedSpaceModuleAdjunction.homEquiv f F G φ) I ≫
        DerivedCategory.Plus.Qh.map (HomotopyCategory.Plus.quotientHomMk
          (plus_modulePushforwardComplex f I.boundedBelow) J'.boundedBelow J'.ι) =
      CochainComplex.InjectiveResolution.qhHom G J ≫
        DerivedCategory.Plus.Qh.map (HomotopyCategory.Plus.quotientHomMk
          J.boundedBelow J'.boundedBelow β) :=
    have hw : ((CochainComplex.singleFunctor (Modules Y) 0).map
            (RingedSpaceModuleAdjunction.homEquiv f F G φ) ≫
          (HomologicalComplex.singleMapHomologicalComplex
              (RingedSpaceModuleAdjunction.modulePushforward f)
              (ComplexShape.up ℤ) 0).inv.app F ≫
            ((RingedSpaceModuleAdjunction.modulePushforward f).mapHomologicalComplex
              (ComplexShape.up ℤ)).map I.ι) ≫ J'.ι =
        J.ι ≫ β :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun z => (CochainComplex.singleFunctor (Modules Y) 0).map
            (RingedSpaceModuleAdjunction.homEquiv f F G φ) ≫ z)
          (Category.assoc _ _ _)).trans hβ.symm)
    (DerivedCategory.Plus.qhHomMk_comp G (plus_modulePushforwardComplex f I.boundedBelow)
          J'.boundedBelow _ J'.ι).trans
      ((congrArg (fun z => DerivedCategory.Plus.qhHomMk G J'.boundedBelow z) hw).trans
        ((DerivedCategory.Plus.qhHomMk_comp G J.boundedBelow J'.boundedBelow J.ι β).symm.trans
          (congrArg (fun z => z ≫ DerivedCategory.Plus.Qh.map
              (HomotopyCategory.Plus.quotientHomMk J.boundedBelow J'.boundedBelow β))
            (CochainComplex.InjectiveResolution.qhHom_eq_qhHomMk G J).symm)))
  have hroof : injectiveResolutionGlobalSectionsMap f φ I J J' β hβ =
      DerivedCategory.Q.map (((moduleGlobalSections Y).mapHomologicalComplex
          (ComplexShape.up ℤ)).map β) ≫
        inv (DerivedCategory.Q.map (((moduleGlobalSections Y).mapHomologicalComplex
          (ComplexShape.up ℤ)).map J'.ι)) :=
    rfl
  have hnβ := (moduleGlobalSections Y).mapHomologicalComplexDerivedUnit_naturality
    J.boundedBelow J'.boundedBelow β
  have hnJ' := (moduleGlobalSections Y).mapHomologicalComplexDerivedUnit_naturality
    (plus_modulePushforwardComplex f I.boundedBelow) J'.boundedBelow J'.ι
  have hJ := (moduleGlobalSections Y).rightDerivedFunctorPlusInjectiveResolutionIso_hom_comp G J
  have hsub := iotaMap_derivedModuleGlobalSectionsMap_comp_alongResolutionIso_hom f φ I
  rw [hroof]
  refine (cancel_mono ((moduleGlobalSections Y).mapHomologicalComplexDerivedUnit
    (plus_modulePushforwardComplex f I.boundedBelow) ≫
      DerivedCategory.Plus.ι.map ((moduleGlobalSections Y).rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Qh.map (HomotopyCategory.Plus.quotientHomMk
          (plus_modulePushforwardComplex f I.boundedBelow) J'.boundedBelow J'.ι))))).1 ?_
  have hinner : (DerivedCategory.Q.map (((moduleGlobalSections Y).mapHomologicalComplex
            (ComplexShape.up ℤ)).map β) ≫
          inv (DerivedCategory.Q.map (((moduleGlobalSections Y).mapHomologicalComplex
            (ComplexShape.up ℤ)).map J'.ι))) ≫
        ((moduleGlobalSections Y).mapHomologicalComplexDerivedUnit
            (plus_modulePushforwardComplex f I.boundedBelow) ≫
          DerivedCategory.Plus.ι.map ((moduleGlobalSections Y).rightDerivedFunctorPlus.map
            (DerivedCategory.Plus.Qh.map (HomotopyCategory.Plus.quotientHomMk
              (plus_modulePushforwardComplex f I.boundedBelow) J'.boundedBelow J'.ι)))) =
      DerivedCategory.Q.map (((moduleGlobalSections Y).mapHomologicalComplex
          (ComplexShape.up ℤ)).map β) ≫
        (moduleGlobalSections Y).mapHomologicalComplexDerivedUnit J'.boundedBelow :=
    (congrArg (fun z => (DerivedCategory.Q.map
            (((moduleGlobalSections Y).mapHomologicalComplex (ComplexShape.up ℤ)).map β) ≫
          inv (DerivedCategory.Q.map (((moduleGlobalSections Y).mapHomologicalComplex
            (ComplexShape.up ℤ)).map J'.ι))) ≫ z) hnJ'.symm).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun z => DerivedCategory.Q.map
            (((moduleGlobalSections Y).mapHomologicalComplex (ComplexShape.up ℤ)).map β) ≫ z)
          (IsIso.inv_hom_id_assoc _ _)))
  refine Eq.trans ((Category.assoc _ _ _).trans
    ((congrArg (fun z =>
        ((moduleGlobalSections Y).rightDerivedFunctorPlusInjectiveResolutionIso G J).hom ≫ z)
      (hinner.trans hnβ)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ DerivedCategory.Plus.ι.map
              ((moduleGlobalSections Y).rightDerivedFunctorPlus.map
                (DerivedCategory.Plus.Qh.map (HomotopyCategory.Plus.quotientHomMk
                  J.boundedBelow J'.boundedBelow β)))) hJ).trans
          ((DerivedCategory.Plus.ι.map_comp _ _).symm.trans
            (congrArg DerivedCategory.Plus.ι.map
              ((moduleGlobalSections Y).rightDerivedFunctorPlus.map_comp _ _).symm)))))) ?_
  refine Eq.symm ((Category.assoc _ _ _).trans
    ((congrArg (fun z => DerivedCategory.Plus.ι.map (derivedModuleGlobalSectionsMap f φ) ≫ z)
      (Category.assoc _ _ _).symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ DerivedCategory.Plus.ι.map
              ((moduleGlobalSections Y).rightDerivedFunctorPlus.map
                (DerivedCategory.Plus.Qh.map (HomotopyCategory.Plus.quotientHomMk
                  (plus_modulePushforwardComplex f I.boundedBelow)
                  J'.boundedBelow J'.ι)))) hsub).trans
          ((DerivedCategory.Plus.ι.map_comp _ _).symm.trans
            ((congrArg DerivedCategory.Plus.ι.map
                ((moduleGlobalSections Y).rightDerivedFunctorPlus.map_comp _ _).symm).trans
              (congrArg (fun z => DerivedCategory.Plus.ι.map
                ((moduleGlobalSections Y).rightDerivedFunctorPlus.map z)) hlift)))))))

end

end Stacks.Cohomology

end
