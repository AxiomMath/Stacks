module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperExtFiniteComplexes
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackFiniteTypeReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseDerived
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseModuleTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.FormalAlgebraization
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.Deformation.ToposThickening.CoefficientExtUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissage
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeOverFieldCharacterization
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackDiagonal
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackFibreFiniteComparison

/-!
# The Ext groups of the fibre of `Complexes_{X/Y}` from Stacks 0D0T (towards Stacks 0DLL)

The fibre computation of the proof of Stacks 0DLL needs `Ext¹(E₀, E₀)` and `Ext⁰(E₀, E₀)` to be
finite dimensional over `k`, where `E₀` is the complex of a field point `x₀` on `X₀ = X_{x₀}`.
That is Stacks 0D0T, stated for an algebraic space *over `Spec A`*
(`AlgebraicGeometry.Space.moduleFinite_hom_shift_of_isProper`), whereas `X₀` lives over `S`. This
file is the bridge. It enters as the hypothesis `h0D0T`, in the form of that theorem: the standard
derived category, the `A`-linear structure `Linear.ofRingHom (baseRingHom A ..)`
(`AlgebraicGeometry.Space.modulesLinear`), `K ∈ D⁻_Coh`, `L ∈ D⁺_Coh`.

* `X₀` is read over `Spec k` through Stacks 04SG (`AlgebraicGeometry.Space.spaceOverSmallerBase`),
  proper there (`AlgebraicGeometry.Space.isProper_toYonedaId_spaceOverSmallerBase`).
* The module categories are identified (`AlgebraicGeometry.Space.smallerBaseModulesEquivalence`),
  `k`-linearly: on `X₀` a scalar acts through `φ : X₀ ⟶ Spec k`
  (`AlgebraicGeometry.Space.smallerBaseRingHom`), over `Spec k` through the structure morphism
  (`AlgebraicGeometry.Space.smallerBaseModulesEquivalence_functor_linear`), and so are the
  derived categories, the one of `X₀` at any model
  (`AlgebraicGeometry.Space.smallerBaseModulesEquivalence_mapDerivedCategory_linear`).
* `D⁻_Coh` and `D⁺_Coh` are transported
  (`AlgebraicGeometry.Space.derivedCategoryBMinus_smallerBase`,
  `AlgebraicGeometry.Space.derivedCategoryBPlus_smallerBase`), which gives Stacks 0D0T on `X₀`
  (`AlgebraicGeometry.Space.moduleFinite_hom_shift_smallerBase`).
* The `k`-structure of the obstruction groups is multiplication by `θ(c)`
  (`Stacks.TensorByBaseModule.linearOfHom`) for a coefficient map `θ` inducing `φ` on global
  functions, e.g. `AlgebraicGeometry.Space.smallerBaseCoefficientMap`; with
  `Deformation.ComplexLift.isCoefficientScalar_linearOfHom` this gives the finiteness of the
  groups at `V = k` (`AlgebraicGeometry.Space.finiteDimensional_coefficientExt_unit_of_isProper`,
  `AlgebraicGeometry.Space.finiteDimensional_coefficientHom_unit_of_isProper`). `Ext⁰` is
  `Hom(K, K⟦0⟧) ≅ Hom(K, K)`.
* The complex of a field point lies in `D⁻_Coh ∩ D⁺_Coh` by Stacks 0DKP and 08IK
  (`ComplexesSituation.derivedCategoryBMinus_and_plus_of_isRelativelyPerfect`).

The results are stated in the form
`AlgebraicGeometry.Space.ComplexesSituation.fibreTangentFinite_of_coefficientLiftComparison` and
`AlgebraicGeometry.Space.ComplexesSituation.fibreInfFinite_of_coefficientHom` consume, at the
spelling `(smallEtaleRingedSite B S hS X₀.1 X₀.2).C`, `.J`, `.O` of the site (the one under which
instance search sees the modules `AlgebraicGeometry.Space.Modules`), and they are plugged into
those two theorems at the coefficient map of the field point.

Nothing here is registered.

## Main results

* `AlgebraicGeometry.Space.moduleFinite_hom_shift_smallerBase`
* `AlgebraicGeometry.Space.ComplexesSituation.finiteDimensional_coefficientExt_unit_of_fieldPoint`
  and
  `AlgebraicGeometry.Space.ComplexesSituation.finiteDimensional_coefficientHom_unit_of_fieldPoint`
* `ComplexesSituation.fibreTangentFinite_of_coefficientLiftComparison_fieldPoint`
  and `AlgebraicGeometry.Space.ComplexesSituation.fibreInfFinite_of_coefficientHom_fieldPoint`

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
* [Stacks Project, Tag 0D0T](https://stacks.math.columbia.edu/tag/0D0T)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 0DKP](https://stacks.math.columbia.edu/tag/0DKP)
* [Stacks Project, Tag 08IK](https://stacks.math.columbia.edu/tag/08IK)
-/

/- See `StacksFrontier/Deformation/ToposThickening/CoefficientSquareZeroReduction.lean`: these
instances make the universe unifier get stuck on sheaves of modules over a site in
`Type (u + 1)`. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe d₀ u w

namespace Stacks.TensorByBaseModule

variable {C : Type*} [Category* C] (R : Type w) [CommRing R] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] (O : Sheaf J CommRingCat.{w})

/-- **The coefficient map of a ring homomorphism into the global sections**: a ring map
`ψ : R →+* Γ(C, O)` is the morphism of presheaves of commutative rings `\underline{R} ⟶ O` whose
value over `U` is `r ↦ ψ(r)|_U`. It is the inverse construction to
`Stacks.TensorByBaseModule.globalSectionRingHomOfHom`
(`Stacks.TensorByBaseModule.globalSectionRingHomOfHom_coefficientMapOfGlobalSections`). -/
def coefficientMapOfGlobalSections
    (ψ : R →+* ↥(Stacks.Cohomology.SiteModules.GlobalSectionRing (ringSheaf J O))) :
    constantRingPresheaf (C := C) R ⟶ O.val where
  app U := CommRingCat.ofHom
    { toFun r := (ψ r).1 U
      map_one' := congrFun (congrArg Subtype.val (map_one ψ)) U
      map_mul' r s := congrFun (congrArg Subtype.val (map_mul ψ r s)) U
      map_zero' := congrFun (congrArg Subtype.val (map_zero ψ)) U
      map_add' r s := congrFun (congrArg Subtype.val (map_add ψ r s)) U }
  naturality U V g := by
    ext r
    exact ((ψ r).2 g).symm

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- `Stacks.TensorByBaseModule.coefficientMapOfGlobalSections` inverts
`Stacks.TensorByBaseModule.globalSectionRingHomOfHom`. -/
theorem globalSectionRingHomOfHom_coefficientMapOfGlobalSections
    (ψ : R →+* ↥(Stacks.Cohomology.SiteModules.GlobalSectionRing (ringSheaf J O))) :
    globalSectionRingHomOfHom R J O (coefficientMapOfGlobalSections R J O ψ) = ψ :=
  RingHom.ext fun _ => rfl

end Stacks.TensorByBaseModule

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

/- The instances of the statement of Stacks 0D0T: the standard derived category of the modules on
an algebraic space, and sheafification on its small étale site. -/
attribute [local instance 10000] HasDerivedCategory.standard smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective smallEtaleRingedSite_hasSheafify_over
  smallEtaleRingedSite_wEqualsLocallyBijective_over

/-! ### The space over `Spec k` and its modules -/

section Bridge

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S) (Y : AlgebraicSpaces B S hS)
  (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (g : B.obj hk ⟶ B.obj hS)
  (φ : Y.1 ⟶ yoneda.obj (Over.mk g))

/-- The module equivalence of Stacks 04SG carries multiplication by a global function to
multiplication by its restriction along the equivalence of small étale sites. -/
theorem smallerBaseModulesEquivalence_functor_map_globalSmul
    (a : Stacks.Cohomology.SiteModules.GlobalSectionRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)))
    (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (smallerBaseModulesEquivalence.{u, u} B _ S hk hS g Y φ).functor.map
        (Stacks.Cohomology.SiteModules.globalSmul _ a M) =
      Stacks.Cohomology.SiteModules.globalSmul _
        (smallerBaseGlobalSectionRingHom B _ S hk hS g Y φ a)
        ((smallerBaseModulesEquivalence.{u, u} B _ S hk hS g Y φ).functor.obj M) := by
  rfl

/-- **The module equivalence of Stacks 04SG is `k`-linear**: on `Y` a scalar `c` acts by
multiplication by its image under `φ : Y ⟶ Spec k`
(`AlgebraicGeometry.Space.smallerBaseRingHom`), on the space `Y'` over `Spec k` by multiplication
by its image under the structure morphism (`AlgebraicGeometry.Space.baseRingHom`, the structure of
Stacks 0D0T). -/
theorem smallerBaseModulesEquivalence_functor_linear :
    letI : Linear k (Modules.{u, u} B S hS Y.1 Y.2) :=
      Linear.ofRingHom (smallerBaseRingHom B S hS Y k hk g φ)
    letI : Linear k (Modules.{u, u} B (Spec (.of k)) hk (spaceOverSmallerBase B _ S hk hS g Y φ).1
        (spaceOverSmallerBase B _ S hk hS g Y φ).2) :=
      Linear.ofRingHom (baseRingHom k B hk (spaceOverSmallerBase B _ S hk hS g Y φ).1
        (spaceOverSmallerBase B _ S hk hS g Y φ).2)
    (smallerBaseModulesEquivalence.{u, u} B _ S hk hS g Y φ).functor.Linear k := by
  let : Linear k (Modules.{u, u} B S hS Y.1 Y.2) :=
    Linear.ofRingHom (smallerBaseRingHom B S hS Y k hk g φ)
  let : Linear k (Modules.{u, u} B (Spec (.of k)) hk (spaceOverSmallerBase B _ S hk hS g Y φ).1
      (spaceOverSmallerBase B _ S hk hS g Y φ).2) :=
    Linear.ofRingHom (baseRingHom k B hk (spaceOverSmallerBase B _ S hk hS g Y φ).1
      (spaceOverSmallerBase B _ S hk hS g Y φ).2)
  refine ⟨fun {M N} f c => ?_⟩
  show (smallerBaseModulesEquivalence.{u, u} B _ S hk hS g Y φ).functor.map
      (Stacks.Cohomology.SiteModules.globalSmul _ (smallerBaseRingHom B S hS Y k hk g φ c) M ≫ f) =
    Stacks.Cohomology.SiteModules.globalSmul _
      (baseRingHom k B hk (spaceOverSmallerBase B _ S hk hS g Y φ).1
        (spaceOverSmallerBase B _ S hk hS g Y φ).2 c) _ ≫
      (smallerBaseModulesEquivalence.{u, u} B _ S hk hS g Y φ).functor.map f
  rw [Functor.map_comp, smallerBaseModulesEquivalence_functor_map_globalSmul,
    ← reindexGlobalSectionRingHom_comp_smallerBaseRingHom]
  rfl

/-- **The coefficient map of `φ : Y ⟶ Spec k`**: the morphism `\underline{k} ⟶ 𝒪_Y` of presheaves
of commutative rings on the small étale site of `Y` whose value over a chart `U` pulls a scalar
back along the morphism `U ⟶ Spec k` that `φ` induces (`smallerBaseCoefficientMap_app_apply`). It
is the coefficient map `θ` of the proof of Stacks 0DLL, and its ring map into the global functions
is `AlgebraicGeometry.Space.smallerBaseRingHom` on the nose
(`AlgebraicGeometry.Space.globalSectionRingHomOfHom_smallerBaseCoefficientMap`). -/
def smallerBaseCoefficientMap :
    Stacks.TensorByBaseModule.constantRingPresheaf
        (C := (smallEtaleRingedSite B S hS Y.1 Y.2).C) k ⟶
      (smallEtaleRingedSite B S hS Y.1 Y.2).O.val :=
  Stacks.TensorByBaseModule.coefficientMapOfGlobalSections k _ _
    (smallerBaseRingHom B S hS Y k hk g φ)

/-- Over a chart `U`, the coefficient map of `φ` is pullback of functions along the morphism
`U ⟶ Spec k` induced by `φ`, `k` being the functions on `Spec k`. -/
theorem smallerBaseCoefficientMap_app_apply (U : (smallEtaleRingedSite B S hS Y.1 Y.2).Cᵒᵖ)
    (c : k) :
    ((smallerBaseCoefficientMap B hS Y k hk g φ).app U).hom c =
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        (chartToScheme B S hS Y.1 φ U.unop)).op).hom ((Scheme.ΓSpecIso (.of k)).inv.hom c) :=
  rfl

/-- The ring map of global functions of the coefficient map of `φ` is
`AlgebraicGeometry.Space.smallerBaseRingHom`. -/
theorem globalSectionRingHomOfHom_smallerBaseCoefficientMap :
    Stacks.TensorByBaseModule.globalSectionRingHomOfHom k _ _
        (smallerBaseCoefficientMap B hS Y k hk g φ) =
      smallerBaseRingHom B S hS Y k hk g φ :=
  RingHom.ext fun _ => rfl

/-- **The space over `Spec k` is proper over `Spec k`** when `φ : Y ⟶ Spec k` is proper: the
counit of the equivalence of Stacks 04SG identifies `φ` with the structure morphism of the image
of `Y'` over `S`, up to an isomorphism of the source. -/
theorem isProper_toYonedaId_spaceOverSmallerBase (hφ : IsProper B S hS φ) :
    IsProper B (Spec (.of k)) hk
      (toYonedaId B (Spec (.of k)) hk (spaceOverSmallerBase B _ S hk hS g Y φ).1) := by
  let F := spacesOverSmallerBaseEquivalence B (Spec (.of k)) S hk hS g
  let c := (ObjectProperty.ι _).mapIso (F.counitIso.app ⟨Over.mk φ, Y.2⟩)
  have : IsIso c.hom.left := inferInstanceAs (IsIso ((Over.forget _).mapIso c).hom)
  have hc : c.hom.left ≫ φ = ((spacesOverSmallerBaseFunctor B (Spec (.of k)) S hk hS g).obj
      (spaceOverSmallerBase B _ S hk hS g Y φ)).1.hom :=
    Over.w c.hom
  have h₁ := (isProper_isIso_comp_iff B S hS c.hom.left φ).2 hφ
  rw [hc] at h₁
  exact (isProper_spacesOverSmallerBaseFunctor_obj_hom_iff B hk hS g _).1 h₁

end Bridge

/-! ### The derived categories -/

section Derived

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S) (Y : AlgebraicSpaces B S hS)
  (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (g : B.obj hk ⟶ B.obj hS)
  (φ : Y.1 ⟶ yoneda.obj (Over.mk g)) [HasDerivedCategory.{d₀} (Modules.{u, u} B S hS Y.1 Y.2)]

/-- The module equivalence of Stacks 04SG is additive. -/
instance smallerBaseModulesEquivalence_functor_additive :
    (smallerBaseModulesEquivalence.{u, u} B _ S hk hS g Y φ).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **The equivalence of derived categories of Stacks 04SG is `k`-linear**, for the structures of
`AlgebraicGeometry.Space.smallerBaseModulesEquivalence_functor_linear`; the derived category of
`Y` is any model, that of `Y'` the standard one. -/
theorem smallerBaseModulesEquivalence_mapDerivedCategory_linear :
    letI : Linear k (Modules.{u, u} B S hS Y.1 Y.2) :=
      Linear.ofRingHom (smallerBaseRingHom B S hS Y k hk g φ)
    letI : Linear k (Modules.{u, u} B (Spec (.of k)) hk (spaceOverSmallerBase B _ S hk hS g Y φ).1
        (spaceOverSmallerBase B _ S hk hS g Y φ).2) :=
      Linear.ofRingHom (baseRingHom k B hk (spaceOverSmallerBase B _ S hk hS g Y φ).1
        (spaceOverSmallerBase B _ S hk hS g Y φ).2)
    (smallerBaseModulesEquivalence.{u, u} B _ S hk hS g Y φ).functor.mapDerivedCategory.Linear
      k := by
  let : Linear k (Modules.{u, u} B S hS Y.1 Y.2) :=
    Linear.ofRingHom (smallerBaseRingHom B S hS Y k hk g φ)
  let : Linear k (Modules.{u, u} B (Spec (.of k)) hk (spaceOverSmallerBase B _ S hk hS g Y φ).1
      (spaceOverSmallerBase B _ S hk hS g Y φ).2) :=
    Linear.ofRingHom (baseRingHom k B hk (spaceOverSmallerBase B _ S hk hS g Y φ).1
      (spaceOverSmallerBase B _ S hk hS g Y φ).2)
  let F := (smallerBaseModulesEquivalence.{u, u} B _ S hk hS g Y φ).functor
  have : F.Linear k := smallerBaseModulesEquivalence_functor_linear B hS Y k hk g φ
  let : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ))
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) F.mapDerivedCategory :=
    ⟨F.mapDerivedCategoryFactors⟩
  exact (Localization.functor_linear_iff DerivedCategory.Q
    (HomologicalComplex.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ)) k
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      F.mapDerivedCategory).1 inferInstance

/-- The homology of the transport to `Y'` of an object of `D(𝒪_Y)` is the transport of its
homology. -/
abbrev smallerBaseHomologyIso (K : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)) (i : ℤ) :
    (DerivedCategory.homologyFunctor _ i).obj
        ((smallerBaseModulesEquivalence.{u, u} B _ S hk hS g Y φ).functor.mapDerivedCategory.obj
          K) ≅
      (smallerBaseModulesEquivalence.{u, u} B _ S hk hS g Y φ).functor.obj
        ((DerivedCategory.homologyFunctor _ i).obj K) :=
  ((smallerBaseModulesEquivalence.{u, u} B _ S hk hS g Y φ).functor.mapDerivedCategoryHomologyIso
    i).app K

/-- The transport to `Y'` preserves vanishing and coherence of the homology of an object. -/
private theorem homology_smallerBase
    [Fact (HasEtaleLocalProperty B (Spec (.of k)) hk (spaceOverSmallerBase B _ S hk hS g Y φ).1
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))]
    (K : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)) (P : ℤ → Prop)
    (hb : ∀ i, P i → IsZero ((DerivedCategory.homologyFunctor _ i).obj K))
    (hc : DerivedCategoryB.derivedCategoryB (isCoherent.{u, u} B S hS Y.1 Y.2) K) :
    (∀ i, P i → IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((smallerBaseModulesEquivalence.{u, u} B _ S hk hS g Y φ).functor.mapDerivedCategory.obj
          K))) ∧
      DerivedCategoryB.derivedCategoryB
        (isCoherent.{u, u} B (Spec (.of k)) hk (spaceOverSmallerBase B _ S hk hS g Y φ).1
          (spaceOverSmallerBase B _ S hk hS g Y φ).2)
        ((smallerBaseModulesEquivalence.{u, u} B _ S hk hS g Y φ).functor.mapDerivedCategory.obj
          K) :=
  ⟨fun i hi => ((smallerBaseModulesEquivalence.{u, u} B _ S hk hS g Y φ).functor.map_isZero
      (hb i hi)).of_iso (smallerBaseHomologyIso B hS Y k hk g φ K i),
    fun i => isCoherent_of_iso B _ hk _ (smallerBaseHomologyIso B hS Y k hk g φ K i).symm
      (isCoherent_smallerBaseModules B _ S hk hS g Y φ _ (hc i).toIsQuasicoherentOnSite
        (hc i).toIsCoherentOnSite.isFiniteType)⟩

/-- **The transport to `Y'` of an object of `D^-_Coh(𝒪_Y)` lies in `D^-_Coh(𝒪_{Y'})`**, for `Y'`
locally Noetherian. -/
theorem derivedCategoryBMinus_smallerBase
    [Fact (HasEtaleLocalProperty B (Spec (.of k)) hk (spaceOverSmallerBase B _ S hk hS g Y φ).1
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))]
    (K : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (hK : DerivedCategoryB.derivedCategoryBMinus (isCoherent.{u, u} B S hS Y.1 Y.2) K) :
    DerivedCategoryB.derivedCategoryBMinus
      (isCoherent.{u, u} B (Spec (.of k)) hk (spaceOverSmallerBase B _ S hk hS g Y φ).1
        (spaceOverSmallerBase B _ S hk hS g Y φ).2)
      ((smallerBaseModulesEquivalence.{u, u} B _ S hk hS g Y φ).functor.mapDerivedCategory.obj
        K) := by
  obtain ⟨⟨b, hb⟩, hc⟩ := hK
  exact ⟨⟨b, (homology_smallerBase B hS Y k hk g φ K _ hb hc).1⟩,
    (homology_smallerBase B hS Y k hk g φ K _ hb hc).2⟩

/-- **The transport to `Y'` of an object of `D^+_Coh(𝒪_Y)` lies in `D^+_Coh(𝒪_{Y'})`**, for `Y'`
locally Noetherian. -/
theorem derivedCategoryBPlus_smallerBase
    [Fact (HasEtaleLocalProperty B (Spec (.of k)) hk (spaceOverSmallerBase B _ S hk hS g Y φ).1
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))]
    (K : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (hK : DerivedCategoryB.derivedCategoryBPlus (isCoherent.{u, u} B S hS Y.1 Y.2) K) :
    DerivedCategoryB.derivedCategoryBPlus
      (isCoherent.{u, u} B (Spec (.of k)) hk (spaceOverSmallerBase B _ S hk hS g Y φ).1
        (spaceOverSmallerBase B _ S hk hS g Y φ).2)
      ((smallerBaseModulesEquivalence.{u, u} B _ S hk hS g Y φ).functor.mapDerivedCategory.obj
        K) := by
  obtain ⟨⟨b, hb⟩, hc⟩ := hK
  exact ⟨⟨b, (homology_smallerBase B hS Y k hk g φ K _ hb hc).1⟩,
    (homology_smallerBase B hS Y k hk g φ K _ hb hc).2⟩

/-- **Stacks 0D0T over `Spec k`, read on `Y`.** Let `φ : Y ⟶ Spec k` be a proper morphism from an
algebraic space over `S` to the spectrum of a field. For `K ∈ D^-_Coh(𝒪_Y)` and
`L ∈ D^+_Coh(𝒪_Y)` the `k`-vector space `Hom_{D(𝒪_Y)}(K, L[n])` is finite, `c ∈ k` acting by
multiplication by its image `ψ c` under `φ` (`AlgebraicGeometry.Space.smallerBaseRingHom`); the
derived category of `Y` is any model.

The hypothesis `h0D0T` is **Stacks 0D0T**, in the form of
`AlgebraicGeometry.Space.moduleFinite_hom_shift_of_isProper`: an algebraic space `X` proper
over `Spec A`, `A` Noetherian, the `A`-linear structure of multiplication by the image of `A` in
the global functions, the standard derived category. It is applied to the space `Y'` over
`Spec k` of Stacks 04SG (`AlgebraicGeometry.Space.spaceOverSmallerBase`), to which the module
category, the derived category, the `k`-linear structure and the conditions `D^-_Coh`, `D^+_Coh`
are transported. -/
theorem moduleFinite_hom_shift_smallerBase
    (h0D0T : ∀ (A : Type u) [CommRing A] (hA : B.Contains (Spec (.of A)))
      (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
      (hX : IsAlgebraicSpace B (Spec (.of A)) hA X),
      letI : Linear A (Modules.{u, u} B (Spec (.of A)) hA X hX) :=
        Linear.ofRingHom (baseRingHom A B hA X hX)
      ∀ [IsNoetherianRing A] (f : X ⟶ yoneda.obj (baseObject A B hA)),
        IsProper B (Spec (.of A)) hA f →
        ∀ (K L : DerivedCategory (Modules.{u, u} B (Spec (.of A)) hA X hX)),
          DerivedCategoryB.derivedCategoryBMinus (isCoherent.{u, u} B (Spec (.of A)) hA X hX) K →
          DerivedCategoryB.derivedCategoryBPlus (isCoherent.{u, u} B (Spec (.of A)) hA X hX) L →
          ∀ n : ℤ, Module.Finite A (K ⟶ L⟦n⟧))
    (hφ : IsProper B S hS φ)
    (ψ : k →+* Stacks.Cohomology.SiteModules.GlobalSectionRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)))
    (hψ : ψ = smallerBaseRingHom B S hS Y k hk g φ)
    (K L : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (hK : DerivedCategoryB.derivedCategoryBMinus (isCoherent.{u, u} B S hS Y.1 Y.2) K)
    (hL : DerivedCategoryB.derivedCategoryBPlus (isCoherent.{u, u} B S hS Y.1 Y.2) L) (n : ℤ) :
    letI : Linear k (Modules.{u, u} B S hS Y.1 Y.2) := Linear.ofRingHom ψ
    Module.Finite k (K ⟶ L⟦n⟧) := by
  subst hψ
  let : Linear k (Modules.{u, u} B S hS Y.1 Y.2) :=
    Linear.ofRingHom (smallerBaseRingHom B S hS Y k hk g φ)
  let : Linear k (Modules.{u, u} B (Spec (.of k)) hk (spaceOverSmallerBase B _ S hk hS g Y φ).1
      (spaceOverSmallerBase B _ S hk hS g Y φ).2) :=
    Linear.ofRingHom (baseRingHom k B hk (spaceOverSmallerBase B _ S hk hS g Y φ).1
      (spaceOverSmallerBase B _ S hk hS g Y φ).2)
  let F := (smallerBaseModulesEquivalence.{u, u} B _ S hk hS g Y φ).functor
  have : F.mapDerivedCategory.Linear k :=
    smallerBaseModulesEquivalence_mapDerivedCategory_linear B hS Y k hk g φ
  have : F.mapDerivedCategory.IsEquivalence :=
    Stacks.DerivedCategory.mapDerivedCategory_isEquivalence
      (smallerBaseModulesEquivalence.{u, u} B _ S hk hS g Y φ)
  have hZ := isProper_toYonedaId_spaceOverSmallerBase B hS Y k hk g φ hφ
  have : Fact (HasEtaleLocalProperty B (Spec (.of k)) hk (spaceOverSmallerBase B _ S hk hS g Y φ).1
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V)) :=
    ⟨hasEtaleLocalProperty_isLocallyNoetherian_of_isProper k B hk _
      (spaceOverSmallerBase B _ S hk hS g Y φ).2 _ hZ⟩
  have hfin := h0D0T k hk _ (spaceOverSmallerBase B _ S hk hS g Y φ).2 _ hZ
    (F.mapDerivedCategory.obj K) (F.mapDerivedCategory.obj L)
    (derivedCategoryBMinus_smallerBase B hS Y k hk g φ K hK)
    (derivedCategoryBPlus_smallerBase B hS Y k hk g φ L hL) n
  let Φ : (K ⟶ L⟦n⟧) →ₗ[k] (F.mapDerivedCategory.obj K ⟶ (F.mapDerivedCategory.obj L)⟦n⟧) :=
    (Linear.rightComp k _ ((F.mapDerivedCategory.commShiftIso n).hom.app L)).comp
      (F.mapDerivedCategory.mapLinearMap k)
  refine Module.Finite.of_injective Φ fun a b hab => F.mapDerivedCategory.map_injective ?_
  simpa [Φ, cancel_mono] using hab

end Derived

/-! ### The obstruction groups at `V = k` -/

section Coefficient

open Deformation.ComplexLift

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S) (Y : AlgebraicSpaces B S hS)
  (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (g : B.obj hk ⟶ B.obj hS)
  (φ : Y.1 ⟶ yoneda.obj (Over.mk g))
  [HasDerivedCategory.{d₀} (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))]

/-- **`Ext¹(K₀, K₀)` at `V = k` is finite dimensional, from Stacks 0D0T.** -/
theorem finiteDimensional_coefficientExt_unit_of_isProper
    (h0D0T : ∀ (A : Type u) [CommRing A] (hA : B.Contains (Spec (.of A)))
      (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
      (hX : IsAlgebraicSpace B (Spec (.of A)) hA X),
      letI : Linear A (Modules.{u, u} B (Spec (.of A)) hA X hX) :=
        Linear.ofRingHom (baseRingHom A B hA X hX)
      ∀ [IsNoetherianRing A] (f : X ⟶ yoneda.obj (baseObject A B hA)),
        IsProper B (Spec (.of A)) hA f →
        ∀ (K L : DerivedCategory (Modules.{u, u} B (Spec (.of A)) hA X hX)),
          DerivedCategoryB.derivedCategoryBMinus (isCoherent.{u, u} B (Spec (.of A)) hA X hX) K →
          DerivedCategoryB.derivedCategoryBPlus (isCoherent.{u, u} B (Spec (.of A)) hA X hX) L →
          ∀ n : ℤ, Module.Finite A (K ⟶ L⟦n⟧))
    (hφ : IsProper B S hS φ)
    (θ : Stacks.TensorByBaseModule.constantRingPresheaf
      (C := (smallEtaleRingedSite B S hS Y.1 Y.2).C) k ⟶
        (smallEtaleRingedSite B S hS Y.1 Y.2).O.obj)
    (hθ : Stacks.TensorByBaseModule.globalSectionRingHomOfHom k _ _ θ =
      smallerBaseRingHom B S hS Y k hk g φ)
    (K : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)))
    (hK : DerivedCategoryB.derivedCategoryBMinus (isCoherent.{u, u} B S hS Y.1 Y.2) K)
    (hK' : DerivedCategoryB.derivedCategoryBPlus (isCoherent.{u, u} B S hS Y.1 Y.2) K) :
    FiniteDimensional k ((coefficientExtLinearFunctor.{d₀} θ K).obj (FGModuleCat.of k k)) := by
  let : Linear k (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)) :=
    Stacks.TensorByBaseModule.linearOfHom k _ _ θ
  have : FiniteDimensional k (K ⟶ K⟦(1 : ℤ)⟧) :=
    moduleFinite_hom_shift_smallerBase B hS Y k hk g φ h0D0T hφ _ hθ K K hK hK' 1
  exact finiteDimensional_coefficientExt_unit K (isCoefficientScalar_linearOfHom θ)

/-- **`Ext⁰(K₀, K₀)` at `V = k` is finite dimensional, from Stacks 0D0T.** -/
theorem finiteDimensional_coefficientHom_unit_of_isProper
    (h0D0T : ∀ (A : Type u) [CommRing A] (hA : B.Contains (Spec (.of A)))
      (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
      (hX : IsAlgebraicSpace B (Spec (.of A)) hA X),
      letI : Linear A (Modules.{u, u} B (Spec (.of A)) hA X hX) :=
        Linear.ofRingHom (baseRingHom A B hA X hX)
      ∀ [IsNoetherianRing A] (f : X ⟶ yoneda.obj (baseObject A B hA)),
        IsProper B (Spec (.of A)) hA f →
        ∀ (K L : DerivedCategory (Modules.{u, u} B (Spec (.of A)) hA X hX)),
          DerivedCategoryB.derivedCategoryBMinus (isCoherent.{u, u} B (Spec (.of A)) hA X hX) K →
          DerivedCategoryB.derivedCategoryBPlus (isCoherent.{u, u} B (Spec (.of A)) hA X hX) L →
          ∀ n : ℤ, Module.Finite A (K ⟶ L⟦n⟧))
    (hφ : IsProper B S hS φ)
    (θ : Stacks.TensorByBaseModule.constantRingPresheaf
      (C := (smallEtaleRingedSite B S hS Y.1 Y.2).C) k ⟶
        (smallEtaleRingedSite B S hS Y.1 Y.2).O.obj)
    (hθ : Stacks.TensorByBaseModule.globalSectionRingHomOfHom k _ _ θ =
      smallerBaseRingHom B S hS Y k hk g φ)
    (K : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)))
    (hK : DerivedCategoryB.derivedCategoryBMinus (isCoherent.{u, u} B S hS Y.1 Y.2) K)
    (hK' : DerivedCategoryB.derivedCategoryBPlus (isCoherent.{u, u} B S hS Y.1 Y.2) K) :
    FiniteDimensional k ((coefficientHomLinearFunctor.{d₀} θ K).obj (FGModuleCat.of k k)) := by
  let : Linear k (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)) :=
    Stacks.TensorByBaseModule.linearOfHom k _ _ θ
  have : FiniteDimensional k (K ⟶ K⟦(0 : ℤ)⟧) :=
    moduleFinite_hom_shift_smallerBase B hS Y k hk g φ h0D0T hφ _ hθ K K hK hK' 0
  have : FiniteDimensional k (K ⟶ K) :=
    Module.Finite.equiv (Linear.homCongr k (Iso.refl K) ((shiftFunctorZero _ ℤ).app K))
  exact finiteDimensional_coefficientHom_unit K (isCoefficientScalar_linearOfHom θ)

end Coefficient

/-! ### The complex of a field point is bounded with coherent cohomology -/

/-- **Stacks 0D0T in the form of the hypothesis `h0D0T`** (unregistered). This is the base's
`AlgebraicGeometry.Space.moduleFinite_hom_shift_of_isProper`, with its
`A`-linear structure `AlgebraicGeometry.Space.modulesLinear` written out as
`Linear.ofRingHom (AlgebraicGeometry.Space.baseRingHom A B hA X hX)`, which it unfolds to. It
discharges the hypothesis `h0D0T` of the theorems below. -/
theorem moduleFinite_hom_shift_of_isProper_ofRingHom (B : BigFppfSite.{u}) (A : Type u)
    [CommRing A] (hA : B.Contains (Spec (.of A)))
    (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X) :
    letI : Linear A (Modules.{u, u} B (Spec (.of A)) hA X hX) :=
      Linear.ofRingHom (baseRingHom A B hA X hX)
    ∀ [IsNoetherianRing A] (f : X ⟶ yoneda.obj (baseObject A B hA)),
      IsProper B (Spec (.of A)) hA f →
      ∀ (K L : DerivedCategory (Modules.{u, u} B (Spec (.of A)) hA X hX)),
        DerivedCategoryB.derivedCategoryBMinus (isCoherent.{u, u} B (Spec (.of A)) hA X hX) K →
        DerivedCategoryB.derivedCategoryBPlus (isCoherent.{u, u} B (Spec (.of A)) hA X hX) L →
        ∀ n : ℤ, Module.Finite A (K ⟶ L⟦n⟧) :=
  by
  intro _ f hf K L hK hL n
  exact moduleFinite_hom_shift_of_isProper A B hA X hX f hf K L hK hL n

namespace ComplexesSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : ComplexesSituation B S hS)

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits
  RingedSite.sliceHasDerivedCategory Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived

/-- **An object of `Complexes_{X/Y}` over the spectrum of a field lies in `D^-_Coh ∩ D^+_Coh`.**
If the test scheme `T` is `Spec k` over `S`, an object `E` of `D(𝒪_{X_T})` perfect relative to
`T` (condition (1) of Stacks 0DLD) is bounded and pseudo-coherent (Stacks 0DKP, `X_T` being of
finite presentation over `k`), hence bounded with coherent cohomology (Stacks 08IK). -/
theorem derivedCategoryBMinus_and_plus_of_isRelativelyPerfect {k : Type u} [Field k]
    (hk : B.Contains (Spec (.of k))) (b : Spec (.of k) ⟶ S) (T : SchemesOver D.Y)
    (hT : T.left = Over.mk (ObjectProperty.homMk b : B.obj hk ⟶ B.obj hS))
    (E : derivedModules B S hS (D.space T)) (hE : D.IsRelativelyPerfect T E) :
    DerivedCategoryB.derivedCategoryBMinus (isCoherent.{u, u} B S hS (D.space T).1 (D.space T).2)
        E ∧
      DerivedCategoryB.derivedCategoryBPlus (isCoherent.{u, u} B S hS (D.space T).1 (D.space T).2)
        E := by
  obtain ⟨Tl, ⟨⟩, Th⟩ := T
  subst hT
  have hfp := projection_isFinitePresentation (D := D) (CostructuredArrow.mk Th)
  have h := isPerfectRelativeTo_canonical_iff_isBounded_and_isPseudoCoherent B S hS k hk b
    (X := D.space (CostructuredArrow.mk Th)) (D.projection (CostructuredArrow.mk Th)) hfp E
  have h2 := h.1 hE
  have hcoh := (isBounded_and_isPseudoCoherent_iff_derivedCategoryBBounded B S hS _ _
    (hasEtaleLocalProperty_isLocallyNoetherian_of_fieldSpace B S hS k hk b _ hfp.1) E).1 h2
  have hc : ∀ i : ℤ, isCoherent.{u, u} B S hS _ _
      ((DerivedCategory.homologyFunctor _ i).obj E) := fun i =>
    @isCoherent_of_isCoherentOnSite B S hS _ _ _ (hcoh.2 i)
  exact ⟨⟨h2.1.2, hc⟩, ⟨h2.1.1, hc⟩⟩

/-- The projection `X_T ⟶ T`, composed with the identification of `T` with a given object. -/
private theorem isProper_projection_comp_eqToHom (T : SchemesOver D.Y) {V : BigFppfOver B S hS}
    (e : T.left = V) : IsProper B S hS ((D.projection T).hom ≫ yoneda.map (eqToHom e)) := by
  subst e
  exact projection_isProper (D := D) T

/-- **`Ext¹(E, E)` at `V = k` is finite dimensional at a field point, from Stacks 0D0T.** Let `T`
be the spectrum of a field `k` over `S` and `E` an object of `D(𝒪_{X_T})` perfect relative to
`T`. For a coefficient map `θ : \underline{k} ⟶ 𝒪_{X_T}` inducing the structure morphism
`X_T ⟶ T = Spec k` on global functions (for instance
`AlgebraicGeometry.Space.smallerBaseCoefficientMap`), the obstruction group
`Hom(E, (E ⊗^L (𝒪 ⊗_k k))⟦1⟧)` is finite dimensional over `k`. This is the hypothesis of
`AlgebraicGeometry.Space.ComplexesSituation.fibreTangentFinite_of_coefficientLiftComparison`.

`h0D0T` is **Stacks 0D0T**, in the form of
`AlgebraicGeometry.Space.moduleFinite_hom_shift_of_isProper`. -/
theorem finiteDimensional_coefficientExt_unit_of_fieldPoint
    (h0D0T : ∀ (A : Type u) [CommRing A] (hA : B.Contains (Spec (.of A)))
      (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
      (hX : IsAlgebraicSpace B (Spec (.of A)) hA X),
      letI : Linear A (Modules.{u, u} B (Spec (.of A)) hA X hX) :=
        Linear.ofRingHom (baseRingHom A B hA X hX)
      ∀ [IsNoetherianRing A] (f : X ⟶ yoneda.obj (baseObject A B hA)),
        IsProper B (Spec (.of A)) hA f →
        ∀ (K L : DerivedCategory (Modules.{u, u} B (Spec (.of A)) hA X hX)),
          DerivedCategoryB.derivedCategoryBMinus (isCoherent.{u, u} B (Spec (.of A)) hA X hX) K →
          DerivedCategoryB.derivedCategoryBPlus (isCoherent.{u, u} B (Spec (.of A)) hA X hX) L →
          ∀ n : ℤ, Module.Finite A (K ⟶ L⟦n⟧))
    {k : Type u} [Field k] (hk : B.Contains (Spec (.of k))) (b : Spec (.of k) ⟶ S)
    (T : SchemesOver D.Y)
    (hT : T.left = Over.mk (ObjectProperty.homMk b : B.obj hk ⟶ B.obj hS))
    (θ : Stacks.TensorByBaseModule.constantRingPresheaf
      (C := (smallEtaleRingedSite B S hS (D.space T).1 (D.space T).2).C) k ⟶
        (smallEtaleRingedSite B S hS (D.space T).1 (D.space T).2).O.obj)
    (hθ : Stacks.TensorByBaseModule.globalSectionRingHomOfHom k _ _ θ =
      smallerBaseRingHom B S hS (D.space T) k hk (ObjectProperty.homMk b)
        ((D.projection T).hom ≫ yoneda.map (eqToHom hT)))
    (E : derivedModules B S hS (D.space T)) (hE : D.IsRelativelyPerfect T E) :
    FiniteDimensional k
      ((Deformation.ComplexLift.coefficientExtLinearFunctor.{u + 1} θ E).obj
        (FGModuleCat.of k k)) := by
  obtain ⟨hK, hK'⟩ := D.derivedCategoryBMinus_and_plus_of_isRelativelyPerfect hk b T hT E hE
  exact finiteDimensional_coefficientExt_unit_of_isProper B hS _ k hk _ _ h0D0T
    (isProper_projection_comp_eqToHom D T hT) θ hθ E hK hK'

/-- **`Ext⁰(E, E)` at `V = k` is finite dimensional at a field point, from Stacks 0D0T.** The
companion of
`AlgebraicGeometry.Space.ComplexesSituation.finiteDimensional_coefficientExt_unit_of_fieldPoint`
for the group `Hom(E, E ⊗^L (𝒪 ⊗_k k))`, the hypothesis of
`AlgebraicGeometry.Space.ComplexesSituation.fibreInfFinite_of_coefficientHom`.

`h0D0T` is **Stacks 0D0T**, in the form of
`AlgebraicGeometry.Space.moduleFinite_hom_shift_of_isProper`. -/
theorem finiteDimensional_coefficientHom_unit_of_fieldPoint
    (h0D0T : ∀ (A : Type u) [CommRing A] (hA : B.Contains (Spec (.of A)))
      (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
      (hX : IsAlgebraicSpace B (Spec (.of A)) hA X),
      letI : Linear A (Modules.{u, u} B (Spec (.of A)) hA X hX) :=
        Linear.ofRingHom (baseRingHom A B hA X hX)
      ∀ [IsNoetherianRing A] (f : X ⟶ yoneda.obj (baseObject A B hA)),
        IsProper B (Spec (.of A)) hA f →
        ∀ (K L : DerivedCategory (Modules.{u, u} B (Spec (.of A)) hA X hX)),
          DerivedCategoryB.derivedCategoryBMinus (isCoherent.{u, u} B (Spec (.of A)) hA X hX) K →
          DerivedCategoryB.derivedCategoryBPlus (isCoherent.{u, u} B (Spec (.of A)) hA X hX) L →
          ∀ n : ℤ, Module.Finite A (K ⟶ L⟦n⟧))
    {k : Type u} [Field k] (hk : B.Contains (Spec (.of k))) (b : Spec (.of k) ⟶ S)
    (T : SchemesOver D.Y)
    (hT : T.left = Over.mk (ObjectProperty.homMk b : B.obj hk ⟶ B.obj hS))
    (θ : Stacks.TensorByBaseModule.constantRingPresheaf
      (C := (smallEtaleRingedSite B S hS (D.space T).1 (D.space T).2).C) k ⟶
        (smallEtaleRingedSite B S hS (D.space T).1 (D.space T).2).O.obj)
    (hθ : Stacks.TensorByBaseModule.globalSectionRingHomOfHom k _ _ θ =
      smallerBaseRingHom B S hS (D.space T) k hk (ObjectProperty.homMk b)
        ((D.projection T).hom ≫ yoneda.map (eqToHom hT)))
    (E : derivedModules B S hS (D.space T)) (hE : D.IsRelativelyPerfect T E) :
    FiniteDimensional k
      ((Deformation.ComplexLift.coefficientHomLinearFunctor.{u + 1} θ E).obj
        (FGModuleCat.of k k)) := by
  obtain ⟨hK, hK'⟩ := D.derivedCategoryBMinus_and_plus_of_isRelativelyPerfect hk b T hT E hE
  exact finiteDimensional_coefficientHom_unit_of_isProper B hS _ k hk _ _ h0D0T
    (isProper_projection_comp_eqToHom D T hT) θ hθ E hK hK'

section FieldPoint

attribute [local instance] complexesCategory

open Deformation Deformation.Artin Deformation.ComplexLift

/-- The test scheme of a field point `x₀` of `Complexes_{X/Y}` over `Spec k ⟶ Spec Λ ⟶ S` is
`Spec k`, as an object of the site over `S`. -/
theorem fieldPoint_left_eq
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
    (x₀ : ComplexesObject D)
    (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hk : B.Contains (Spec (.of k))) :
    x₀.T.left = Over.mk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) :
      B.obj hk ⟶ B.obj hS) :=
  BigFppfOver.obj_injective_post_inclusion B S hS hx₀

/-- **The coefficient map `θ : \underline{k} ⟶ 𝒪_{X₀}` of a field point** `x₀`, on the small étale
site of `X₀ = X_{x₀}`: `AlgebraicGeometry.Space.smallerBaseCoefficientMap` of the projection
`X₀ ⟶ Spec k`. This is the `θ` at which the fibre computation of Stacks 0DLL is carried out. -/
abbrev fieldPointCoefficientMap
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
    (x₀ : ComplexesObject D)
    (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hk : B.Contains (Spec (.of k))) :
    Stacks.TensorByBaseModule.constantRingPresheaf
      (C := (smallEtaleRingedSite B S hS (D.space x₀.T).1 (D.space x₀.T).2).C) k ⟶
        (smallEtaleRingedSite B S hS (D.space x₀.T).1 (D.space x₀.T).2).O.val :=
  smallerBaseCoefficientMap B hS (D.space x₀.T) k hk _
    ((D.projection x₀.T).hom ≫ yoneda.map (eqToHom (fieldPoint_left_eq D iΛ x₀ hx₀ hk)))

/-- **The tangent-space hypothesis on the fibre from a comparison with derived lifts and Stacks
0D0T.**
`AlgebraicGeometry.Space.ComplexesSituation.fibreTangentFinite_of_coefficientLiftComparison`
at the coefficient map of the field point
(`AlgebraicGeometry.Space.ComplexesSituation.fieldPointCoefficientMap`) and at `K₀ = E₀`, the
complex of `x₀`, with the finiteness of `Ext¹(E₀, E₀)` discharged by
`AlgebraicGeometry.Space.ComplexesSituation.finiteDimensional_coefficientExt_unit_of_fieldPoint`.

`h0D0T` is **Stacks 0D0T**, in the form of
`AlgebraicGeometry.Space.moduleFinite_hom_shift_of_isProper`. -/
theorem fibreTangentFinite_of_coefficientLiftComparison_fieldPoint
    (h0D0T : ∀ (A : Type u) [CommRing A] (hA : B.Contains (Spec (.of A)))
      (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
      (hX : IsAlgebraicSpace B (Spec (.of A)) hA X),
      letI : Linear A (Modules.{u, u} B (Spec (.of A)) hA X hX) :=
        Linear.ofRingHom (baseRingHom A B hA X hX)
      ∀ [IsNoetherianRing A] (f : X ⟶ yoneda.obj (baseObject A B hA)),
        IsProper B (Spec (.of A)) hA f →
        ∀ (K L : DerivedCategory (Modules.{u, u} B (Spec (.of A)) hA X hX)),
          DerivedCategoryB.derivedCategoryBMinus (isCoherent.{u, u} B (Spec (.of A)) hA X hX) K →
          DerivedCategoryB.derivedCategoryBPlus (isCoherent.{u, u} B (Spec (.of A)) hA X hX) L →
          ∀ n : ℤ, Module.Finite A (K ⟶ L⟦n⟧))
    (hfib : (complexesFunctor D).IsFiberedInGroupoids)
    (rsC : SatisfiesRSStar B S hS (complexesFunctor D) hfib)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
    (x₀ : ComplexesObject D)
    (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hk : B.Contains (Spec (.of k)))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    [∀ V : FGModuleCat.{u} k, HasDerivedCategory.{u + 1} (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (coefficientRing (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V)))]
    (hK : DerivedCategory.TStructure.t.minus x₀.E)
    (Φ : CoefficientLiftComparison.{u + 1, u + 1} B S hS iΛ hk (complexesFunctor D) (baseProj D.Y)
      (Over.map x₀.T.left.hom) (complexesToBaseObjects D)
      (schemePointToBase D.Y x₀.T.left x₀.T.hom) (fibreBasePoint D x₀)
      (fibreBasePoint_eq_algebraOver D iΛ x₀ hx₀ hk) (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)
      ⟨x₀.E, hK⟩) :
    FibreTangentFinite D iΛ x₀ hx₀ := by
  have := finiteDimensional_coefficientExt_unit_of_fieldPoint D h0D0T hk _ x₀.T
    (fieldPoint_left_eq D iΛ x₀ hx₀ hk) _
    (globalSectionRingHomOfHom_smallerBaseCoefficientMap _ _ _ _ _ _ _) x₀.E x₀.relativelyPerfect
  exact fibreTangentFinite_of_coefficientLiftComparison D hfib rsC iΛ x₀ hx₀ hfinite hqc hk _ _ Φ

/-- **The infinitesimal-automorphism hypothesis on the fibre from the groups
`Hom(E₀, E₀ ⊗^L (𝒪 ⊗_k V))` and Stacks 0D0T.**
`AlgebraicGeometry.Space.ComplexesSituation.fibreInfFinite_of_coefficientHom` at the coefficient
map of the field point (`AlgebraicGeometry.Space.ComplexesSituation.fieldPointCoefficientMap`)
and at `K₀ = E₀`, with the finiteness of `Ext⁰(E₀, E₀)` discharged by
`AlgebraicGeometry.Space.ComplexesSituation.finiteDimensional_coefficientHom_unit_of_fieldPoint`.

`h0D0T` is **Stacks 0D0T**, in the form of
`AlgebraicGeometry.Space.moduleFinite_hom_shift_of_isProper`. -/
theorem fibreInfFinite_of_coefficientHom_fieldPoint
    (h0D0T : ∀ (A : Type u) [CommRing A] (hA : B.Contains (Spec (.of A)))
      (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
      (hX : IsAlgebraicSpace B (Spec (.of A)) hA X),
      letI : Linear A (Modules.{u, u} B (Spec (.of A)) hA X hX) :=
        Linear.ofRingHom (baseRingHom A B hA X hX)
      ∀ [IsNoetherianRing A] (f : X ⟶ yoneda.obj (baseObject A B hA)),
        IsProper B (Spec (.of A)) hA f →
        ∀ (K L : DerivedCategory (Modules.{u, u} B (Spec (.of A)) hA X hX)),
          DerivedCategoryB.derivedCategoryBMinus (isCoherent.{u, u} B (Spec (.of A)) hA X hX) K →
          DerivedCategoryB.derivedCategoryBPlus (isCoherent.{u, u} B (Spec (.of A)) hA X hX) L →
          ∀ n : ℤ, Module.Finite A (K ⟶ L⟦n⟧))
    (hfib : (complexesFunctor D).IsFiberedInGroupoids)
    (rsC : SatisfiesRSStar B S hS (complexesFunctor D) hfib)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
    (x₀ : ComplexesObject D)
    (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hk : B.Contains (Spec (.of k)))
    [∀ V : FGModuleCat.{u} k, HasDerivedCategory.{u + 1} (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (coefficientRing (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V)))]
    (hK : DerivedCategory.TStructure.t.minus x₀.E)
    (aut : ∀ V : FGModuleCat.{u} k,
      (coefficientHomLinearFunctor.{u + 1} (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) x₀.E).obj V →
      (trivialDeformation k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
          (TwoFibreProductOver.structureFunctor (complexesFunctor D) (Over.map x₀.T.left.hom)
            (baseProj D.Y) (complexesToBaseObjects D) (schemePointToBase D.Y x₀.T.left x₀.T.hom))
          (fibreBasePoint D x₀) (fibreBasePoint_eq_algebraOver D iΛ x₀ hx₀ hk)
          (TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _ hfib
            (Functor.IsFiberedInGroupoids.over_map x₀.T.left.hom)
            (baseProj_isFiberedInGroupoids D.Y) (complexesToBaseObjects_comp D)
            (schemePointToBase_comp D.Y x₀.T.left x₀.T.hom))
          ((fgSiteModule B hk).obj V) ⟶
        trivialDeformation k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
          (TwoFibreProductOver.structureFunctor (complexesFunctor D) (Over.map x₀.T.left.hom)
            (baseProj D.Y) (complexesToBaseObjects D) (schemePointToBase D.Y x₀.T.left x₀.T.hom))
          (fibreBasePoint D x₀) (fibreBasePoint_eq_algebraOver D iΛ x₀ hx₀ hk)
          (TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _ hfib
            (Functor.IsFiberedInGroupoids.over_map x₀.T.left.hom)
            (baseProj_isFiberedInGroupoids D.Y) (complexesToBaseObjects_comp D)
            (schemePointToBase_comp D.Y x₀.T.left x₀.T.hom))
          ((fgSiteModule B hk).obj V)))
    (haut : ∀ {V W : FGModuleCat.{u} k} (f : V ⟶ W)
      (g : (coefficientHomLinearFunctor.{u + 1} (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)
        x₀.E).obj V),
      aut W ((coefficientHomLinearFunctor.{u + 1} (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)
        x₀.E).map f g) =
        (infinitesimalAutomorphismSetFunctor k B S hS
          (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
          (TwoFibreProductOver.structureFunctor (complexesFunctor D) (Over.map x₀.T.left.hom)
            (baseProj D.Y) (complexesToBaseObjects D) (schemePointToBase D.Y x₀.T.left x₀.T.hom))
          (fibreBasePoint D x₀) (fibreBasePoint_eq_algebraOver D iΛ x₀ hx₀ hk)
          (TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _ hfib
            (Functor.IsFiberedInGroupoids.over_map x₀.T.left.hom)
            (baseProj_isFiberedInGroupoids D.Y) (complexesToBaseObjects_comp D)
            (schemePointToBase_comp D.Y x₀.T.left x₀.T.hom))).map
          ((fgSiteModule B hk).map f) (aut V g))
    (hsurj : Function.Surjective (aut (FGModuleCat.of k k))) :
    FibreInfFinite D iΛ x₀ hx₀ := by
  have := finiteDimensional_coefficientHom_unit_of_fieldPoint D h0D0T hk _ x₀.T
    (fieldPoint_left_eq D iΛ x₀ hx₀ hk) _
    (globalSectionRingHomOfHom_smallerBaseCoefficientMap _ _ _ _ _ _ _) x₀.E x₀.relativelyPerfect
  exact fibreInfFinite_of_coefficientHom D hfib rsC iΛ x₀ hx₀ hk _ (K₀ := ⟨x₀.E, hK⟩) aut haut hsurj

end FieldPoint

end ComplexesSituation

end AlgebraicGeometry.Space

end
