module

public import StacksFrontier.AlgebraicGeometry.Cohomology.SchemeOpenRestriction.Basic
public import StacksFrontier.AlgebraicGeometry.CohomologyGlobalSectionScalar.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CohomologyBridge
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.CompatibilityWithRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.SpectralSpaces

/-!
# Top degree cohomology of a quasi-compact open subscheme

Let `Y` be a quasi-compact and quasi-separated scheme over a field `k` of dimension at most `d`,
let `U ⊆ Y` be a quasi-compact open and `𝒢` an `𝒪_Y`-module. By clause (2) of
[Stacks, Tag 0A3G] the restriction `H^d(Y, 𝒢) ⟶ H^d(U, 𝒢|_U)` is surjective; in particular, if
`H^d(Y, 𝒢)` is a finite-dimensional `k`-vector space, so is `H^d(U, 𝒢|_U)`. This is the last step
of the proof of [Stacks, Tag 0A3M], where `Y` is a projective closure of a quasi-projective `U`.

Clause (2) of [Stacks, Tag 0A3G] is
`Stacks.CohomologyVanishing.surjective_cohomologyPresheaf_map_top_of_topologicalKrullDim_le`, a
statement about the `Ext`-theoretic cohomology presheaf of an abelian sheaf. It is carried to the
cohomology of modules in three steps, each an existing comparison which is compatible with
restriction: `Ext` out of the objects corepresenting sections against right derived sections
(`ModuleSheafCohomology.extFunctorObjIsoRightDerived_naturality`), abelian against module
cohomology over an open ([Stacks, Tag 01F1] part (1), compatibility with restriction), and
cohomology over the open `U` against the cohomology of the open subscheme `U`
([Stacks, Tag 01E1]). The `k`-linearity of the resulting map is not tracked through these
identifications: it follows from naturality in the module, multiplication by a scalar being
induced by an endomorphism of the module (`AlgebraicGeometry.cohomologyOverFieldMap_globalSmul`).

## Main results

* `AlgebraicGeometry.TopDegreeFiniteness.surjective_hrestrict_of_topologicalKrullDim_le`:
  surjectivity of `H^d(Y, 𝒢) ⟶ H^d(U, 𝒢)` for module cohomology.
* `AlgebraicGeometry.TopDegreeFiniteness.finiteDimensional_cohomologyOverField_restrict`:
  finite dimensionality passes from `H^d(Y, 𝒢)` to `H^d(U, 𝒢|_U)`.

## References

* [Stacks Project, Tag 0A3G](https://stacks.math.columbia.edu/tag/0A3G)
* [Stacks Project, Tag 01E1](https://stacks.math.columbia.edu/tag/01E1)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

-- The universe-polymorphic sheafification instance of the spectral-limit files would otherwise be
-- found for `Hgroup` here, with an unassigned universe, instead of the one the comparison
-- isomorphisms of [Stacks, Tag 01E1] and [Stacks, Tag 01F1] are stated with.
attribute [-instance] Stacks.Cohomology.SpectralLimit.hasSheafifyOpensMax

namespace AlgebraicGeometry.TopDegreeFiniteness

/-- A map `A` of abelian groups with `e₁ ≫ A = B ≫ e₂` is surjective as soon as `B` and `e₂` are:
the image of `A` contains that of `e₂ ∘ B`. -/
theorem surjective_of_comp_eq_comp {a b c d : AddCommGrpCat.{u}} (e₁ : a ⟶ b) (A : b ⟶ d)
    (B : a ⟶ c) (e₂ : c ⟶ d) (h : e₁ ≫ A = B ≫ e₂) (hB : Function.Surjective B)
    (he₂ : Function.Surjective e₂) : Function.Surjective A := by
  intro y
  obtain ⟨w, rfl⟩ := he₂ y
  obtain ⟨x, rfl⟩ := hB w
  refine ⟨e₁ x, ?_⟩
  rw [← ConcreteCategory.comp_apply, h, ConcreteCategory.comp_apply]

/-- A map `A` of abelian groups with `A ≫ e = C` is surjective when `C` is surjective and `e` is
injective. -/
theorem surjective_of_comp_eq {a b c : AddCommGrpCat.{u}} (A : a ⟶ b) (e : b ⟶ c) (C : a ⟶ c)
    (h : A ≫ e = C) (hC : Function.Surjective C) (he : Function.Injective e) :
    Function.Surjective A := by
  intro y
  obtain ⟨x, hx⟩ := hC (e y)
  refine ⟨x, he ?_⟩
  rw [← ConcreteCategory.comp_apply, h, hx]

section Abelian

variable {T : Type u} [TopologicalSpace T]

/-- **Restriction of `Ext`-theoretic cohomology against restriction of right derived sections.**
For opens `U ≤ V` of a space and an abelian sheaf `F`, if the restriction map of the cohomology
presheaf `Hⁿ(V, F) ⟶ Hⁿ(U, F)` is surjective, so is the map induced on the right derived functors
of sections by restriction of sections. The two are identified by
`ModuleSheafCohomology.extFunctorObjIsoRightDerived`, compatibly with restriction because the
corepresentation of sections is natural in the open. -/
theorem surjective_rightDerived_sectionsRestriction
    (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) {U V : Opens T} (h : U ≤ V)
    (n : ℕ) (hs : Function.Surjective ((F.cohomologyPresheaf n).map (homOfLE h).op)) :
    Function.Surjective ((NatTrans.rightDerived
      (Stacks.Cohomology.ModuleComparison.sectionsRestriction (Opens.grothendieckTopology T)
        (homOfLE h)) n).app F) := by
  have N := ModuleSheafCohomology.extFunctorObjIsoRightDerived_naturality
    (Stacks.Cohomology.ModuleComparison.freeYonedaSheafMap (Opens.grothendieckTopology T)
      (homOfLE h))
    (ModuleSheafCohomology.evaluationRepresentation (Opens.grothendieckTopology T) U)
    (ModuleSheafCohomology.evaluationRepresentation (Opens.grothendieckTopology T) V)
    (Stacks.Cohomology.ModuleComparison.sectionsRestriction (Opens.grothendieckTopology T)
      (homOfLE h))
    (Stacks.Cohomology.ModuleComparison.evaluationRepresentation_naturality
      (Opens.grothendieckTopology T) (homOfLE h)) n
  have NF := NatTrans.congr_app N F
  simp only [NatTrans.comp_app] at NF
  exact surjective_of_comp_eq_comp _ _ _ _ NF.symm hs
    (ConcreteCategory.bijective_of_isIso
        ((ModuleSheafCohomology.extFunctorObjIsoRightDerived _ _
      (ModuleSheafCohomology.evaluationRepresentation (Opens.grothendieckTopology T) U) n
        |>.app F)).hom).2

end Abelian

section Module

variable {Y : Scheme.{u}}

/-- A map `A` of abelian groups with `A ≫ e.hom = f.hom ≫ B` is surjective when `B` is and `e`, `f`
are isomorphisms. -/
private theorem surjective_of_comp_eq_iso {a b c d : AddCommGrpCat.{u}} (A : a ⟶ b) (e : b ≅ c)
    (f : a ≅ d) (B : d ⟶ c) (h : A ≫ e.hom = f.hom ≫ B) (hB : Function.Surjective B) :
    Function.Surjective A := by
  refine surjective_of_comp_eq A e.hom _ h (fun y => ?_)
    (ConcreteCategory.bijective_of_isIso e.hom).1
  obtain ⟨w, rfl⟩ := hB y
  obtain ⟨v, rfl⟩ := (ConcreteCategory.bijective_of_isIso f.hom).2 w
  exact ⟨v, rfl⟩

/-- **Clause (2) of [Stacks, Tag 0A3G] for module cohomology.** Let `Y` be a quasi-compact and
quasi-separated scheme of dimension at most `d`, `U ⊆ Y` a quasi-compact open and `𝒢` an
`𝒪_Y`-module. Then the restriction `H^d(Y, 𝒢) ⟶ H^d(U, 𝒢)` is surjective. -/
theorem surjective_hrestrict_of_topologicalKrullDim_le [CompactSpace Y]
    [QuasiSeparatedSpace Y] (G : Y.Modules) (d : ℕ)
    (hdim : topologicalKrullDim Y ≤ (d : WithBot ℕ∞)) (U : Y.Opens) (hU : IsCompact (U : Set Y)) :
    Function.Surjective (Hrestrict Y.ringCatSheaf (le_top : U ≤ ⊤) d G) := by
  have : SpectralSpace Y := {}
  have hab := surjective_rightDerived_sectionsRestriction
    ((SheafOfModules.toSheaf Y.ringCatSheaf).obj G) (le_top : U ≤ ⊤) d
    (Stacks.CohomologyVanishing.surjective_cohomologyPresheaf_map_top_of_topologicalKrullDim_le
      (X := (Y : Type u)) _ d hdim U hU)
  have key := Stacks.Cohomology.ModuleComparison.canonicalSectionsForgetIso_naturality_open
    Y.ringCatSheaf (le_top : U ≤ ⊤) d G
  exact surjective_of_comp_eq_iso _
    (((Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso Y.ringCatSheaf U d).app
      G).symm ≪≫ (Stacks.Cohomology.ModuleComparison.canonicalSectionsForgetIso
        Y.ringCatSheaf U d).app G)
    (((Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso Y.ringCatSheaf ⊤ d).app
      G).symm ≪≫ (Stacks.Cohomology.ModuleComparison.canonicalSectionsForgetIso
        Y.ringCatSheaf ⊤ d).app G) _ key hab

/-- Restricting a global function of `Y` to `U.ι ''ᵁ V` is restricting its restriction to `U` to
`V`, read through the identification `Γ(U, V) = Γ(Y, U.ι ''ᵁ V)`. -/
theorem restrictTop_image_eq (U : Y.Opens) (a : Γ(Y, ⊤)) (V : (U : Scheme).Opens) :
    restrictTop a (U.ι ''ᵁ V) = (U.ι.appIso V).inv (restrictTop (U.ι.appTop a) V) := by
  rw [Scheme.Opens.ι_appIso]
  exact congrArg (fun φ => (ConcreteCategory.hom φ) a)
    (show Y.presheaf.map (homOfLE (le_top : U.ι ''ᵁ V ≤ ⊤)).op =
        Y.presheaf.map (homOfLE (le_top : U.ι ''ᵁ ⊤ ≤ ⊤)).op ≫
          Y.presheaf.map (homOfLE (U.ι.image_mono (le_top : V ≤ ⊤))).op by
      rw [← Functor.map_comp]
      rfl)

/-- **Restriction to an open subscheme carries multiplication by a global function to
multiplication by its restriction.** -/
theorem restrictFunctor_map_globalSmul (U : Y.Opens) (a : Γ(Y, ⊤)) (G : Y.Modules) :
    (Scheme.Modules.restrictFunctor U.ι).map (globalSmul a G) =
      globalSmul (U.ι.appTop a) ((Scheme.Modules.restrictFunctor U.ι).obj G) := by
  ext V x
  refine (globalSmul_app a G (U.ι ''ᵁ V) x).trans (Eq.trans ?_
    (globalSmul_app (U.ι.appTop a) ((Scheme.Modules.restrictFunctor U.ι).obj G) V x).symm)
  rw [restrictTop_image_eq U a V]
  exact (ModuleCat.restrictScalars.smul_def _ _ _).symm

/-- The scalar `c ∈ k` seen on an open subscheme `U` through `U ⟶ Y ⟶ Spec k` is the
restriction to `U` of the scalar seen on `Y`. -/
theorem baseScalarSection_comp_ι (k : Type u) [Field k] (g : Y ⟶ Spec (.of k)) (U : Y.Opens)
    (c : k) : baseScalarSection k (U.ι ≫ g) c = U.ι.appTop (baseScalarSection k g c) := by
  have e : (U.ι ≫ g).appLE ⊤ ⊤ (Scheme.Hom.preimage_top _).ge =
      g.appLE ⊤ ⊤ (Scheme.Hom.preimage_top _).ge ≫ U.ι.app ⊤ := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    rfl
  exact congrArg (fun φ => (CommRingCat.Hom.hom ((Scheme.ΓSpecIso (.of k)).inv ≫ φ)) c) e

/-- **Restriction to an open subscheme carries multiplication by a scalar to multiplication by
the same scalar.** -/
theorem restrictFunctor_map_globalSmul_baseScalarSection (k : Type u) [Field k]
    (g : Y ⟶ Spec (.of k)) (U : Y.Opens) (G : Y.Modules) (c : k) :
    (Scheme.Modules.restrictFunctor U.ι).map (globalSmul (baseScalarSection k g c) G) =
      globalSmul (baseScalarSection k (U.ι ≫ g) c)
        ((Scheme.Modules.restrictFunctor U.ι).obj G) := by
  rw [baseScalarSection_comp_ι, restrictFunctor_map_globalSmul]

/-- The restriction maps of module cohomology are natural in the module, read on a class. -/
theorem hrestrict_naturality_apply {R : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}}
    [EnoughInjectives (SheafOfModules.{u} R)] {U V : Opens Y} (h : U ≤ V) (n : ℕ)
    {F F' : SheafOfModules.{u} R} (ψ : F ⟶ F') (y : Hgroup R V n F) :
    Hrestrict R h n F' ((Hfunctor R V n).map ψ y) =
      (Hfunctor R U n).map ψ (Hrestrict R h n F y) := by
  have := congrArg (fun φ => φ y) ((HrestrictNT R h n).naturality ψ)
  simp only [ConcreteCategory.comp_apply] at this
  exact this

/-- [Stacks, Tag 01E1] is natural in the module, read on a class. -/
theorem hfunctorRestrictNatIso_naturality_apply (U : Y.Opens) (n : ℕ) {F F' : Y.Modules}
    (ψ : F ⟶ F') (z : Hgroup Y.ringCatSheaf U n F) :
    (Stacks.Cohomology.SchemeOpenRestriction.hfunctorRestrictNatIso Y U n).hom.app F'
        ((Hfunctor Y.ringCatSheaf U n).map ψ z) =
      (Scheme.Modules.restrictFunctor U.ι ⋙ Hfunctor (U : Scheme).ringCatSheaf ⊤ n).map ψ
        ((Stacks.Cohomology.SchemeOpenRestriction.hfunctorRestrictNatIso Y U n).hom.app F z) :=
  NatTrans.naturality_apply
    (Stacks.Cohomology.SchemeOpenRestriction.hfunctorRestrictNatIso Y U n).hom ψ z

variable (k : Type u) [Field k] (g : Y ⟶ Spec (.of k))

/-- Multiplication by `c ∈ k` on `H^d(U, 𝒢|_U)`, read in the group spelling of the cohomology of
`𝒢` over the open `U`, is the map induced by multiplication by `c` on `𝒢`. -/
theorem restrictFunctor_hfunctor_map_globalSmul (U : Y.Opens) (G : Y.Modules) (d : ℕ) (c : k)
    (w : Hgroup (U : Scheme).ringCatSheaf ⊤ d ((Scheme.Modules.restrictFunctor U.ι).obj G)) :
    (Scheme.Modules.restrictFunctor U.ι ⋙ Hfunctor (U : Scheme).ringCatSheaf ⊤ d).map
        (globalSmul (baseScalarSection k g c) G) w =
      cohomologyOverFieldAddEquivHgroup k (U.ι ≫ g) ((Scheme.Modules.restrictFunctor U.ι).obj G) d
        (c • (cohomologyOverFieldAddEquivHgroup k (U.ι ≫ g)
          ((Scheme.Modules.restrictFunctor U.ι).obj G) d).symm w) := by
  show (Hfunctor (U : Scheme).ringCatSheaf ⊤ d).map
    ((Scheme.Modules.restrictFunctor U.ι).map (globalSmul (baseScalarSection k g c) G)) w = _
  rw [restrictFunctor_map_globalSmul_baseScalarSection k g U G c]
  have hn := cohomologyOverFieldAddEquivHgroup_naturality k (U.ι ≫ g)
    (globalSmul (baseScalarSection k (U.ι ≫ g) c) ((Scheme.Modules.restrictFunctor U.ι).obj G)) d
    ((cohomologyOverFieldAddEquivHgroup k (U.ι ≫ g)
      ((Scheme.Modules.restrictFunctor U.ι).obj G) d).symm w)
  rw [cohomologyOverFieldMap_globalSmul, AddEquiv.apply_symm_apply] at hn
  exact hn.symm

/-- **The restriction of top degree cohomology to an open subscheme**, as an additive map
`H^d(Y, 𝒢) ⟶ H^d(U, 𝒢|_U)`: the restriction of module cohomology to the open `U`
followed by [Stacks, Tag 01E1], both read through the comparison of [Stacks, Tag 01F1]. -/
def cohomologyRestrictHom (U : Y.Opens) (G : Y.Modules) (d : ℕ) :
    cohomologyOverField k g G d →+
      cohomologyOverField k (U.ι ≫ g) ((Scheme.Modules.restrictFunctor U.ι).obj G) d :=
  (cohomologyOverFieldAddEquivHgroup k (U.ι ≫ g)
      ((Scheme.Modules.restrictFunctor U.ι).obj G) d).symm.toAddMonoidHom.comp
    (((Stacks.Cohomology.SchemeOpenRestriction.hfunctorRestrictNatIso Y U d).hom.app G).hom.comp
      ((Hrestrict Y.ringCatSheaf (le_top : U ≤ ⊤) d G).hom.comp
        (cohomologyOverFieldAddEquivHgroup k g G d).toAddMonoidHom))

/-- The restriction `cohomologyRestrictHom` sends a class `x` to the image of its group spelling
under `Hrestrict` and `hfunctorRestrictNatIso`, read back through
`cohomologyOverFieldAddEquivHgroup`. -/
theorem cohomologyRestrictHom_apply (U : Y.Opens) (G : Y.Modules) (d : ℕ)
    (x : cohomologyOverField k g G d) :
    cohomologyRestrictHom k g U G d x =
      (cohomologyOverFieldAddEquivHgroup k (U.ι ≫ g)
        ((Scheme.Modules.restrictFunctor U.ι).obj G) d).symm
        ((Stacks.Cohomology.SchemeOpenRestriction.hfunctorRestrictNatIso Y U d).hom.app G
          (Hrestrict Y.ringCatSheaf (le_top : U ≤ ⊤) d G
            (cohomologyOverFieldAddEquivHgroup k g G d x))) :=
  rfl

/-- **The restriction of cohomology to an open subscheme is `k`-linear.** -/
theorem cohomologyRestrictHom_smul (U : Y.Opens) (G : Y.Modules) (d : ℕ) (c : k)
    (x : cohomologyOverField k g G d) :
    cohomologyRestrictHom k g U G d (c • x) = c • cohomologyRestrictHom k g U G d x := by
  have h1 := cohomologyOverFieldAddEquivHgroup_naturality k g
    (globalSmul (baseScalarSection k g c) G) d x
  rw [cohomologyOverFieldMap_globalSmul k g c G d x] at h1
  rw [cohomologyRestrictHom_apply, cohomologyRestrictHom_apply, h1]
  have h2 := hrestrict_naturality_apply (le_top : U ≤ ⊤) d
    (globalSmul (baseScalarSection k g c) G) (cohomologyOverFieldAddEquivHgroup k g G d x)
  have h3 := hfunctorRestrictNatIso_naturality_apply U d (globalSmul (baseScalarSection k g c) G)
    (Hrestrict Y.ringCatSheaf (le_top : U ≤ ⊤) d G (cohomologyOverFieldAddEquivHgroup k g G d x))
  have h4 := restrictFunctor_hfunctor_map_globalSmul k g U G d c
    ((Stacks.Cohomology.SchemeOpenRestriction.hfunctorRestrictNatIso Y U d).hom.app G
      (Hrestrict Y.ringCatSheaf (le_top : U ≤ ⊤) d G (cohomologyOverFieldAddEquivHgroup k g G d x)))
  exact (congrArg (fun z => (cohomologyOverFieldAddEquivHgroup k (U.ι ≫ g)
      ((Scheme.Modules.restrictFunctor U.ι).obj G) d).symm
      ((Stacks.Cohomology.SchemeOpenRestriction.hfunctorRestrictNatIso Y U d).hom.app G z))
        h2).trans
    ((congrArg (cohomologyOverFieldAddEquivHgroup k (U.ι ≫ g)
      ((Scheme.Modules.restrictFunctor U.ι).obj G) d).symm h3).trans
      ((congrArg (cohomologyOverFieldAddEquivHgroup k (U.ι ≫ g)
        ((Scheme.Modules.restrictFunctor U.ι).obj G) d).symm h4).trans
        (AddEquiv.symm_apply_apply _ _)))

/-- `cohomologyRestrictHom` as a `k`-linear map. -/
def cohomologyRestrictLinearMap (U : Y.Opens) (G : Y.Modules) (d : ℕ) :
    cohomologyOverField k g G d →ₗ[k]
      cohomologyOverField k (U.ι ≫ g) ((Scheme.Modules.restrictFunctor U.ι).obj G) d where
  toFun := cohomologyRestrictHom k g U G d
  map_add' := (cohomologyRestrictHom k g U G d).map_add
  map_smul' := cohomologyRestrictHom_smul k g U G d

/-- **The restriction of top degree cohomology to a quasi-compact open subscheme is surjective**,
on a quasi-compact quasi-separated scheme of dimension at most `d`. -/
theorem surjective_cohomologyRestrictHom [CompactSpace Y] [QuasiSeparatedSpace Y]
    (U : Y.Opens) (hU : IsCompact (U : Set Y)) (G : Y.Modules) (d : ℕ)
    (hdim : topologicalKrullDim Y ≤ (d : WithBot ℕ∞)) :
    Function.Surjective (cohomologyRestrictHom k g U G d) := by
  intro y
  obtain ⟨z, hz⟩ := (ConcreteCategory.bijective_of_isIso
      ((Stacks.Cohomology.SchemeOpenRestriction.hfunctorRestrictNatIso Y U d).app G).hom).2
      (cohomologyOverFieldAddEquivHgroup k (U.ι ≫ g)
        ((Scheme.Modules.restrictFunctor U.ι).obj G) d y)
  obtain ⟨w, rfl⟩ := surjective_hrestrict_of_topologicalKrullDim_le G d hdim U hU z
  refine ⟨(cohomologyOverFieldAddEquivHgroup k g G d).symm w, ?_⟩
  rw [cohomologyRestrictHom_apply, AddEquiv.apply_symm_apply]
  exact (congrArg _ hz).trans (AddEquiv.symm_apply_apply _ y)

/-- **Finite dimensionality of the top degree cohomology passes to a quasi-compact open.** Let
`Y` be a quasi-compact and quasi-separated scheme over a field `k`, of dimension at most `d`, let
`U ⊆ Y` be a quasi-compact open and `𝒢` an `𝒪_Y`-module. If `H^d(Y, 𝒢)` is finite-dimensional
over `k`, so is `H^d(U, 𝒢|_U)`.

The restriction `H^d(Y, 𝒢) ⟶ H^d(U, 𝒢)` is surjective by clause (2) of [Stacks, Tag 0A3G]
(`surjective_hrestrict_of_topologicalKrullDim_le`), and `H^d(U, 𝒢)` is `H^d(U, 𝒢|_U)` by
[Stacks, Tag 01E1]. The composite is `k`-linear: every map in it is natural in the module, and
multiplication by `c ∈ k` is induced by an endomorphism of the module which restricts to
multiplication by `c` (`restrictFunctor_map_globalSmul_baseScalarSection`). -/
theorem finiteDimensional_cohomologyOverField_restrict [CompactSpace Y] [QuasiSeparatedSpace Y]
    (G : Y.Modules) (d : ℕ) (hdim : topologicalKrullDim Y ≤ (d : WithBot ℕ∞)) (U : Y.Opens)
    (hU : IsCompact (U : Set Y)) (hfin : FiniteDimensional k (cohomologyOverField k g G d)) :
    FiniteDimensional k
      (cohomologyOverField k (U.ι ≫ g) ((Scheme.Modules.restrictFunctor U.ι).obj G) d) :=
  Module.Finite.of_surjective (cohomologyRestrictLinearMap k g U G d)
    (surjective_cohomologyRestrictHom k g U hU G d hdim)

end Module

end AlgebraicGeometry.TopDegreeFiniteness

end
