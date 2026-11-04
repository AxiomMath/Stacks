module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologyWithSupportSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SupportedDerivedEquivalence
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsCanonicalMaps
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived category of a closed subscheme is the complexes supported on it

Let `i : Z ⟶ X` be a closed immersion of schemes.  Direct image of abelian sheaves along `i` is
exact, so `Ri_{small,*} = i_{small,*}` and the induced functor `D(Z_étale) ⟶ D(X_étale)` is
obtained by applying `i_*` termwise.  It identifies `D(Z_étale)` with the full subcategory
`D_Z(X_étale)` of `D(X_étale)` of complexes whose cohomology sheaves are supported on `Z`, and a
quasi-inverse is given on that subcategory both by inverse image `i^{-1}` and by the right
derived functor `Rℋ_Z` of sections with support in `Z`.

## Main definitions

* `AlgebraicGeometry.supportedSectionsAdjunction` — the adjunction `i_* ⊣ ℋ_Z` of direct image
  with sections with support in the closed subscheme.
* `AlgebraicGeometry.derivedSupportedSections` — the right derived functor
  `Rℋ_Z : D(X_étale) ⥤ D(Z_étale)` of sections with support in the closed subscheme, and
  `AlgebraicGeometry.derivedSupportedSectionsUnit`, the comparison exhibiting it as such.
* `AlgebraicGeometry.derivedSupportedSectionsAdjunction` — the adjunction `i_*^D ⊣ Rℋ_Z` on
  derived categories.
* `AlgebraicGeometry.ClosedImmersionSupportedDerivedEquivalence` — all of the assertions of
  Stacks 0AEG, as a structure.

## Main results

* `AlgebraicGeometry.closedImmersionSupportedDerivedEquivalence` — **Stacks 0AEG**: direct image
  along a closed immersion is exact and induces an equivalence of `D(Z_étale)` with the
  complexes on `X_étale` whose cohomology sheaves are supported on `Z`, whose quasi-inverse is
  computed both by `i^{-1}` and by `Rℋ_Z`.

## Implementation notes

The equivalence itself, with the inverse image as its quasi-inverse, is
`AlgebraicGeometry.smallEtalePushforwardSupportedEquivalence`, built from the adjunction
`i^{-1} ⊣ i_*` of exact functors.  What this file adds is the other description of the
quasi-inverse.  Sections with support in `Z` are right adjoint to direct image: a map out of
`i_*𝒢` has support in `Z` because `i_*𝒢` restricts to zero on the open complement, so it factors
uniquely through the subsheaf `ℋ_Z(ℱ)` of sections with support in `Z`, and that subsheaf is
itself a direct image, so the factorisation is a map on `Z_étale` by full faithfulness.  Both
functors being additive, with `i_*` exact, the adjunction derives to `i_*^D ⊣ Rℋ_Z` once
K-injective resolutions are available, which they are because abelian sheaves on a small étale
site form a Grothendieck abelian category.  The two descriptions of the quasi-inverse then agree
by uniqueness of a right adjoint: restricted to `D_Z(X_étale)`, `Rℋ_Z` is right adjoint to the
equivalence, as is its quasi-inverse.

That `D_Z(X_étale)` is cut out by membership of each cohomology sheaf in the essential image of
`i_*` is the same thing as the support of each cohomology sheaf being contained in `Z`, which is
Stacks 04CA; the identification is recorded in the statement.

## References

* [Stacks Project, Tag 0AEG](https://stacks.math.columbia.edu/tag/0AEG)
* [Stacks Project, Tag 04CA](https://stacks.math.columbia.edu/tag/04CA)
* [Stacks Project, Tag 09XQ](https://stacks.math.columbia.edu/tag/09XQ)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w₁ w₂ u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {Z X : B.Scheme} (i : Z ⟶ X)
  [IsClosedImmersion (B.inclusion.map i)]

/-! ### The adjunction of direct image with sections with support in the closed subscheme -/

/-- A map from a direct image along the closed immersion into an abelian sheaf `F` on `X_étale`
is the canonical map `i_*ℋ_Z(F) ⟶ F` preceded by a map from `Z_étale`: the map has support in
the closed subscheme because its source restricts to zero on the open complement, so it factors
through the subsheaf of sections of `F` with support in the closed subscheme, which is the direct
image of `ℋ_Z(F)`. -/
public theorem exists_comp_supportedSectionsPushforwardInclusion_eq
    (F : SmallEtaleAbelianSheaf B X) (G : SmallEtaleAbelianSheaf B Z)
    (φ : ((smallEtaleBaseChange B i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B Z.obj Z.property)).obj G ⟶ F) :
    ∃ α : G ⟶ (supportedSections B i).obj F,
      ((smallEtaleBaseChange B i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B Z.obj Z.property)).map α ≫
        (supportedSectionsPushforwardInclusion B i).app F = φ := by
  have : Mono (supportedSectionsShortComplex B i F).f :=
    mono_supportedSectionsPushforwardInclusion_app B i F
  have hzero : φ ≫ (complementRestriction B i).app F = 0 := by
    have hnat := (complementRestriction B i).naturality φ
    rw [complementRestriction_app_smallEtaleClosedPushforward B i G, zero_comp] at hnat
    simpa using hnat
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ((smallEtaleBaseChange B i).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B Z.obj Z.property)).obj G ⟶
        ((smallEtaleBaseChange B i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B Z.obj Z.property)).obj ((supportedSections B i).obj F),
      ψ ≫ (supportedSectionsPushforwardInclusion B i).app F = φ :=
    ⟨(supportedSectionsShortComplex_exact B i F).lift φ hzero,
      (supportedSectionsShortComplex_exact B i F).lift_f φ hzero⟩
  refine ⟨Functor.preimage _ ψ, ?_⟩
  rw [Functor.map_preimage]
  exact hψ

/-- Composing with the canonical map `i_*ℋ_Z(F) ⟶ F` identifies the maps `G ⟶ ℋ_Z(F)` on
`Z_étale` with the maps `i_*G ⟶ F` on `X_étale`: it is injective because the canonical map is a
monomorphism and direct image is faithful, and surjective by
`exists_comp_supportedSectionsPushforwardInclusion_eq`. -/
public theorem bijective_map_comp_supportedSectionsPushforwardInclusion
    (F : SmallEtaleAbelianSheaf B X) (G : SmallEtaleAbelianSheaf B Z) :
    Function.Bijective (fun α : G ⟶ (supportedSections B i).obj F =>
      ((smallEtaleBaseChange B i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B Z.obj Z.property)).map α ≫
        (supportedSectionsPushforwardInclusion B i).app F) := by
  have := mono_supportedSectionsPushforwardInclusion_app B i F
  refine ⟨fun α β h => ?_, fun φ => ?_⟩
  · exact Functor.map_injective _ ((cancel_mono
      ((supportedSectionsPushforwardInclusion B i).app F)).mp h)
  · exact exists_comp_supportedSectionsPushforwardInclusion_eq B i F G φ

/-- Composition with the canonical map `i_*ℋ_Z(F) ⟶ F`, as a bijection of the maps
`G ⟶ ℋ_Z(F)` on `Z_étale` with the maps `i_*G ⟶ F` on `X_étale`. -/
public def supportedSectionsHomEquiv (G : SmallEtaleAbelianSheaf B Z)
    (F : SmallEtaleAbelianSheaf B X) :
    (((smallEtaleBaseChange B i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B Z.obj Z.property)).obj G ⟶ F) ≃
      (G ⟶ (supportedSections B i).obj F) :=
  (Equiv.ofBijective _
    (bijective_map_comp_supportedSectionsPushforwardInclusion B i F G)).symm

/-- The inverse of `supportedSectionsHomEquiv` is composition with the canonical map
`i_*ℋ_Z(F) ⟶ F`. -/
public theorem supportedSectionsHomEquiv_symm_apply (G : SmallEtaleAbelianSheaf B Z)
    (F : SmallEtaleAbelianSheaf B X) (α : G ⟶ (supportedSections B i).obj F) :
    (supportedSectionsHomEquiv B i G F).symm α =
      ((smallEtaleBaseChange B i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B Z.obj Z.property)).map α ≫
        (supportedSectionsPushforwardInclusion B i).app F :=
  rfl

/-- A map `i_*G ⟶ F` is recovered from its transpose by composing with the canonical map
`i_*ℋ_Z(F) ⟶ F`. -/
public theorem map_supportedSectionsHomEquiv_comp (G : SmallEtaleAbelianSheaf B Z)
    (F : SmallEtaleAbelianSheaf B X)
    (φ : ((smallEtaleBaseChange B i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B Z.obj Z.property)).obj G ⟶ F) :
    ((smallEtaleBaseChange B i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B Z.obj Z.property)).map
        (supportedSectionsHomEquiv B i G F φ) ≫
      (supportedSectionsPushforwardInclusion B i).app F = φ :=
  (supportedSectionsHomEquiv B i G F).symm_apply_apply φ

/-- The canonical map `i_*ℋ_Z(F) ⟶ F` is natural in `F`. -/
public theorem map_supportedSections_map_comp_supportedSectionsPushforwardInclusion_app
    {F F' : SmallEtaleAbelianSheaf B X} (g : F ⟶ F') :
    ((smallEtaleBaseChange B i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B Z.obj Z.property)).map ((supportedSections B i).map g) ≫
        (supportedSectionsPushforwardInclusion B i).app F' =
      (supportedSectionsPushforwardInclusion B i).app F ≫ g :=
  (supportedSectionsPushforwardInclusion B i).naturality g

/-- **The adjunction `i_* ⊣ ℋ_Z`.** Direct image of abelian sheaves along a closed immersion is
left adjoint to the functor of sections with support in the closed subscheme, the bijection on
maps being composition with the canonical map `i_*ℋ_Z(F) ⟶ F`. -/
public def supportedSectionsAdjunction :
    (smallEtaleBaseChange B i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B Z.obj Z.property) ⊣
      supportedSections B i :=
  Adjunction.mkOfHomEquiv
    { homEquiv := supportedSectionsHomEquiv B i
      homEquiv_naturality_left_symm := fun {G' G F} f g => by
        rw [supportedSectionsHomEquiv_symm_apply, supportedSectionsHomEquiv_symm_apply,
          Functor.map_comp, Category.assoc]
      homEquiv_naturality_right := fun {G F F'} φ g => by
        refine (supportedSectionsHomEquiv B i G F').symm.injective ?_
        rw [Equiv.symm_apply_apply, supportedSectionsHomEquiv_symm_apply, Functor.map_comp,
          Category.assoc,
          map_supportedSections_map_comp_supportedSectionsPushforwardInclusion_app B i g,
          ← Category.assoc, map_supportedSectionsHomEquiv_comp] }

/-! ### The right derived functor of sections with support in the closed subscheme -/

/-- Every cochain complex of abelian sheaves on a small étale site admits a quasi-isomorphism
into a K-injective complex: such sheaves form a Grothendieck abelian category, and a
Grothendieck abelian category carries functorial K-injective resolutions by Stacks 079P. -/
public theorem exists_quasiIso_isKInjective_smallEtaleAbelianSheaf (Y : B.Scheme)
    (K : CochainComplex (SmallEtaleAbelianSheaf B Y) ℤ) :
    ∃ (I : CochainComplex (SmallEtaleAbelianSheaf B Y) ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f :=
  Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian
    (SmallEtaleAbelianSheaf B Y) K

variable [HasDerivedCategory.{w₁} (SmallEtaleAbelianSheaf B Z)]
  [HasDerivedCategory.{w₂} (SmallEtaleAbelianSheaf B X)]

/-- Sections with support in the closed subscheme have a right derived functor on the unbounded
derived category, computed by K-injective resolutions. -/
public instance supportedSections_hasPointwiseRightDerivedFunctor :
    Functor.HasPointwiseRightDerivedFunctor
      ((supportedSections B i).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (HomotopyCategory.quasiIso (SmallEtaleAbelianSheaf B X) (ComplexShape.up ℤ)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      _, _, 0, _, _, 0} _
    (exists_quasiIso_isKInjective_smallEtaleAbelianSheaf B X)).1

/-- The right derived functor `Rℋ_Z : D(X_étale) ⥤ D(Z_étale)` of sections with support in the
closed subscheme. -/
public def derivedSupportedSections :
    DerivedCategory (SmallEtaleAbelianSheaf B X) ⥤ DerivedCategory (SmallEtaleAbelianSheaf B Z) :=
  Functor.totalRightDerived
    ((supportedSections B i).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SmallEtaleAbelianSheaf B X) (ComplexShape.up ℤ))

/-- The canonical comparison from the sections with support in the closed subscheme of a complex
to the value of `Rℋ_Z` on it. -/
public def derivedSupportedSectionsUnit :
    (supportedSections B i).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ derivedSupportedSections B i :=
  Functor.totalRightDerivedUnit
    ((supportedSections B i).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SmallEtaleAbelianSheaf B X) (ComplexShape.up ℤ))

/-- The comparison exhibits `Rℋ_Z` as the right derived functor of sections with support in the
closed subscheme. -/
public instance derivedSupportedSections_isRightDerivedFunctor :
    (derivedSupportedSections B i).IsRightDerivedFunctor
      (derivedSupportedSectionsUnit B i)
      (HomotopyCategory.quasiIso (SmallEtaleAbelianSheaf B X) (ComplexShape.up ℤ)) := by
  dsimp only [derivedSupportedSections, derivedSupportedSectionsUnit]
  infer_instance

/-- **The derived adjunction `i_*^D ⊣ Rℋ_Z`.** Direct image is exact, so the functor it induces
on unbounded derived categories is left adjoint to the right derived functor of sections with
support in the closed subscheme. -/
public def derivedSupportedSectionsAdjunction :
    ((smallEtaleBaseChange B i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B Z.obj Z.property)).mapDerivedCategory ⊣
      derivedSupportedSections B i :=
  Stacks.Cohomology.SupportedComplexes.derivedAdjunctionOfExactLeftAdjoint
    (supportedSectionsAdjunction B i) (derivedSupportedSections B i)
    (derivedSupportedSectionsUnit B i)
    (exists_quasiIso_isKInjective_smallEtaleAbelianSheaf B X)

/-! ### The two descriptions of the quasi-inverse -/

/-- The equivalence of `D(Z_étale)` with `D_Z(X_étale)` is also inverted by `Rℋ_Z`: restricted
to `D_Z(X_étale)`, the right derived functor of sections with support in the closed subscheme is
right adjoint to the equivalence, as is its quasi-inverse, and a right adjoint is unique. -/
public def smallEtalePushforwardSupportedEquivalence_inverse_derivedSupportedSectionsIso :
    (smallEtalePushforwardSupportedEquivalence.{w₁, w₂} B i).inverse ≅
      (supportedDerivedProperty.{w₂} B i).ι ⋙ derivedSupportedSections B i :=
  (smallEtalePushforwardSupportedEquivalence.{w₁, w₂} B i).toAdjunction.rightAdjointUniq
    ((derivedSupportedSectionsAdjunction B i).restrictFullyFaithful
      (Functor.FullyFaithful.id _)
      (ObjectProperty.fullyFaithfulι (supportedDerivedProperty.{w₂} B i))
      (smallEtalePushforwardSupportedEquivalence_functor.{w₁, w₂} B i).symm (Iso.refl _))

/-! ### Stacks 0AEG -/

/-- The assertions of **Stacks 0AEG** for a closed immersion `i : Z ⟶ X` of schemes: direct
image of abelian sheaves along `i` is exact, so that `Ri_{small,*} = i_{small,*}`; the full
subcategory `D_Z(X_étale)` of `D(X_étale)` cut out by `supportedDerivedProperty` is the
complexes whose cohomology sheaves are supported on `Z`; `Rℋ_Z` is the right derived functor of
sections with support in `Z`; and direct image induces an equivalence of `D(Z_étale)` with
`D_Z(X_étale)` whose quasi-inverse is computed on `D_Z(X_étale)` both by the exact inverse image
`i_{small}^{-1}` and by `Rℋ_Z`. -/
public structure ClosedImmersionSupportedDerivedEquivalence where
  /-- `Ri_{small,*} = i_{small,*}`: direct image of abelian sheaves along the closed immersion is
  exact, hence coincides with its own right derived functor. -/
  pushforwardExact : exactFunctor (SmallEtaleAbelianSheaf B Z) (SmallEtaleAbelianSheaf B X)
    ((smallEtaleBaseChange B i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B X.obj X.property) (SmallEtale.topology B Z.obj Z.property))
  /-- `Ri_{small,*} = i_{small,*}` as an identification of functors on derived categories: the
  functor induced termwise on `D(Z_étale) ⥤ D(X_étale)` by direct image *is* a right derived
  functor of it, with the canonical comparison as its unit. -/
  pushforwardIsRightDerived :
    ((smallEtaleBaseChange B i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B Z.obj Z.property)).mapDerivedCategory.IsRightDerivedFunctor
      ((smallEtaleBaseChange B i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B Z.obj Z.property)).mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso (SmallEtaleAbelianSheaf B Z) (ComplexShape.up ℤ))
  /-- Inverse image of abelian sheaves along the closed immersion is exact as well, hence also
  coincides with its own derived functor. -/
  pullbackExact : exactFunctor (SmallEtaleAbelianSheaf B X) (SmallEtaleAbelianSheaf B Z)
    ((smallEtaleBaseChange B i).sheafPullback AddCommGrpCat.{u + 1}
      (SmallEtale.topology B X.obj X.property) (SmallEtale.topology B Z.obj Z.property))
  /-- `D_Z(X_étale)` is the full subcategory of complexes whose cohomology sheaves are supported
  on the closed subscheme. -/
  supported_iff : ∀ K : DerivedCategory (SmallEtaleAbelianSheaf B X),
    supportedDerivedProperty.{w₂} B i K ↔ ∀ n : ℤ,
      SmallEtale.supportSheaf B X.obj X.property
          ((DerivedCategory.homologyFunctor (SmallEtaleAbelianSheaf B X) n).obj K) ⊆
        Set.range (B.inclusion.map i).base
  /-- `Rℋ_Z` is the right derived functor of sections with support in the closed subscheme. -/
  derivedSupportedSectionsIsRightDerived :
    (derivedSupportedSections B i).IsRightDerivedFunctor (derivedSupportedSectionsUnit B i)
      (HomotopyCategory.quasiIso (SmallEtaleAbelianSheaf B X) (ComplexShape.up ℤ))
  /-- Direct image induces an equivalence of `D(Z_étale)` with `D_Z(X_étale)`. -/
  equivalence : DerivedCategory (SmallEtaleAbelianSheaf B Z) ≌ SupportedDerivedCategory.{w₂} B i
  /-- The equivalence is the functor induced by `i_{small,*}`: composed with the inclusion of
  `D_Z(X_étale)` into `D(X_étale)` it is direct image applied termwise. -/
  functorIso : equivalence.functor ⋙ (supportedDerivedProperty.{w₂} B i).ι ≅
    ((smallEtaleBaseChange B i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B Z.obj Z.property)).mapDerivedCategory
  /-- The quasi-inverse of the equivalence is inverse image on `D_Z(X_étale)`. -/
  inversePullbackIso : equivalence.inverse ≅ (supportedDerivedProperty.{w₂} B i).ι ⋙
    ((smallEtaleBaseChange B i).sheafPullback AddCommGrpCat.{u + 1}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B Z.obj Z.property)).mapDerivedCategory
  /-- The quasi-inverse of the equivalence is `Rℋ_Z` on `D_Z(X_étale)`. -/
  inverseDerivedSupportedSectionsIso : equivalence.inverse ≅
    (supportedDerivedProperty.{w₂} B i).ι ⋙ derivedSupportedSections B i

/-- **Stacks 0AEG.** Let `i : Z ⟶ X` be a closed immersion of schemes.  Direct image of abelian
sheaves along `i` is exact, so `Ri_{small,*} = i_{small,*} : D(Z_étale) ⟶ D(X_étale)`, and it
induces an equivalence of `D(Z_étale)` with the full subcategory `D_Z(X_étale)` of `D(X_étale)`
of complexes whose cohomology sheaves are supported on `Z`.  A quasi-inverse of that equivalence
is given on `D_Z(X_étale)` by the exact inverse image `i_{small}^{-1}`, and also by the right
derived functor `Rℋ_Z` of sections with support in `Z`. -/
@[stacks 0AEG]
public def closedImmersionSupportedDerivedEquivalence :
    ClosedImmersionSupportedDerivedEquivalence.{w₁, w₂} B i where
  pushforwardExact := smallEtalePushforward_exact_ab B i
  pushforwardIsRightDerived :=
    Functor.isRightDerivedFunctor_of_inverts _ _ (Functor.mapDerivedCategoryFactorsh _)
  pullbackExact := ⟨(leftExactFunctor_iff _).mpr inferInstance,
    (rightExactFunctor_iff _).mpr inferInstance⟩
  supported_iff K := forall_congr' fun n =>
    smallEtalePushforward_essImage_iff_abelian B i
      ((DerivedCategory.homologyFunctor (SmallEtaleAbelianSheaf B X) n).obj K)
  derivedSupportedSectionsIsRightDerived := inferInstance
  equivalence := smallEtalePushforwardSupportedEquivalence.{w₁, w₂} B i
  functorIso := smallEtalePushforwardSupportedEquivalence_functor.{w₁, w₂} B i
  inversePullbackIso := smallEtalePushforwardSupportedEquivalence_inverse.{w₁, w₂} B i
  inverseDerivedSupportedSectionsIso :=
    smallEtalePushforwardSupportedEquivalence_inverse_derivedSupportedSectionsIso.{w₁, w₂} B i

end AlgebraicGeometry

end
