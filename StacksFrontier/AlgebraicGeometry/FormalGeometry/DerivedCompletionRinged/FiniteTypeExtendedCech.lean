module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.FiniteTypeFamilySystem
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.GlobalExtendedCech
public import StacksFrontier.RingTheory.Cech.FamilySystemLocalQuasiIso
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.HomologyLocallyBijectiveExtend
public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.SheafifyOverComparison
import StacksCore.Tactic.StacksAttribute

/-!
# Tag 099E: the extended Čech complex of a sheaf of ideals

Let `(𝒞, 𝒪)` be a ringed site and `ℐ ⊆ 𝒪` a sheaf of ideals. [Stacks, Tag 099E] asks for a map
`K ⟶ 𝒪` in `D(𝒪)` such that for every object `U` and every finite family `f_1, …, f_r` of sections
of `ℐ` over `U` generating `ℐ|_U`, the extended alternating Čech complex
`𝒪_U → ∏ 𝒪_{U, f_{i₀}} → ⋯ → 𝒪_{U, f_1 ⋯ f_r}` is isomorphic to `K|_U` compatibly with the maps
to `𝒪_U`. This file constructs `K` and proves that, for an arbitrary sheaf of ideals: the
finite-type hypothesis of the source is not used, an object over which `ℐ` is not finitely
generated imposing no condition.

## The construction

The source restricts to the objects over which `ℐ` is finitely generated, builds on each slice the
sheafified presheaf of Čech complexes `U'/U ↦ K(𝒪(U'), I𝒪(U'))` of a chosen finitely generated
ideal `I`, shows that it does not depend on `I`, and glues. Here no choice is made at all: over an
object `V` the presheaf `AlgebraicGeometry.RingedSite.finiteTypeCechPresheaf` takes the filtered
colimit, over *every* finite set of finite families of sections generating `ℐ|_V`, of the Čech
complexes of their product families (`Stacks.CechFamilySystem.cechComplexPresheaf` for the family
system `AlgebraicGeometry.RingedSite.generatesFamilySystem`). Its restriction maps compose on the
nose, so it is a presheaf of complexes on `𝒞` itself and `K` is its sheafification; there is
nothing to glue and no subcategory to restrict to.

Locally the colimit is the Čech complex of any one generating family: on the slice at `U` a family
`g` generating `ℐ|_U` maps into it by the leg of the colimit
(`AlgebraicGeometry.RingedSite.finiteTypeCechLeg`), and this map is locally bijective on homology
(`Stacks.CechFamilySystem.isLocallySurjective_homologyMap_legNat`,
`Stacks.CechFamilySystem.isLocallyInjective_homologyMap_legNat`), because finitely many families
generating `ℐ|_V` span one ideal of sections after passing to a covering — the hint of the source's
proof, `AlgebraicGeometry.RingedSite.exists_mem_sieve_span_eq_of_mem`.

## Main definitions

* `AlgebraicGeometry.RingedSite.finiteTypeCechPresheaf`: the presheaf of Čech complexes of all
  local generators of `ℐ`, and `AlgebraicGeometry.RingedSite.finiteTypeCechPresheafAugmentation`
  its augmentation onto `𝒪`.
* `AlgebraicGeometry.RingedSite.finiteTypeCechLeg`: on the slice at `U`, the comparison out of
  the sectionwise Čech complex of a family generating `ℐ|_U`.
* `AlgebraicGeometry.RingedSite.finiteTypeCech` and
  `AlgebraicGeometry.RingedSite.finiteTypeCechAugmentation`: **the map `K ⟶ 𝒪` of the tag.**

## Main results

* `AlgebraicGeometry.RingedSite.exists_isGlobalExtendedCech`: **[Stacks, Tag 099E]**, through
  `AlgebraicGeometry.RingedSite.isGlobalExtendedCech_finiteTypeCech`.
* `AlgebraicGeometry.RingedSite.finiteTypeCechLegOver_comp_augmentation`: the comparison is a map
  over `𝒪_U`.

* `AlgebraicGeometry.RingedSite.isLocallySurjective_homologyMap_finiteTypeCechLeg` and
  `AlgebraicGeometry.RingedSite.isLocallyInjective_homologyMap_finiteTypeCechLeg`: the comparison
  is locally bijective on homology.

## References

* [Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
* [Stacks Project, Tag 099E](https://stacks.math.columbia.edu/tag/099E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/-- The cancellation the augmentation compatibility of the leg reduces to, stated in a bare
category so that it can be applied by `exact` across two spellings of the same objects. -/
private theorem CategoryTheory.Functor.comp_map_comp_map_comp {𝒞 𝒟 : Type*} [Category 𝒞]
    [Category 𝒟] (Φ : 𝒞 ⥤ 𝒟) {B B' C₀ C₁ : 𝒞} {D₀ D₁ D₃ : 𝒟} (e : D₀ ⟶ D₁)
    (l : D₁ ⟶ Φ.obj B) (p : B' ≅ B) (c : B ⟶ C₀) (σ : C₁ ≅ C₀) (t : Φ.obj C₀ ⟶ D₃)
    (q : D₁ ⟶ Φ.obj C₀) (hq : l ≫ Φ.map c = q) :
    ((e ≫ l ≫ Φ.map p.inv) ≫ Φ.map (p.hom ≫ c ≫ σ.inv)) ≫ Φ.map σ.hom ≫ t = e ≫ q ≫ t := by
  rw [← hq]
  simp only [Category.assoc, ← Φ.map_comp_assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- The last step of the comparison, in a bare category: an isomorphism `i` carrying one map to a
target onto another transports a factorization of the second. -/
private theorem CategoryTheory.Functor.map_inv_comp_map_comp_map {𝒞 𝒟 : Type*} [Category 𝒞]
    [Category 𝒟] (Φ : 𝒞 ⥤ 𝒟) {A B C D : 𝒞} (i : B ≅ A) (ψ : B ⟶ C) (r : C ⟶ D) (c : A ⟶ D)
    (s : B ⟶ D) (hc : ψ ≫ r = s) (hk : i.hom ≫ c = s) :
    Φ.map i.inv ≫ Φ.map ψ ≫ Φ.map r = Φ.map c := by
  rw [← Φ.map_comp, hc, ← hk, ← Φ.map_comp, Iso.inv_hom_id_assoc]

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})
  (ℐ : SheafOfModules.Submodule
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))

/-- **The presheaf of Čech complexes of all local generators of `ℐ`**: over an object `V`, the
filtered colimit, over the finite sets of finite families of sections over `V` generating `ℐ|_V`,
of the extended alternating Čech complexes of their product families. -/
def finiteTypeCechPresheaf :
    CochainComplex (PresheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj) ℤ :=
  Stacks.CechFamilySystem.cechComplexPresheaf (generatesFamilySystem X ℐ)

/-- The augmentation of the presheaf of Čech complexes of all local generators onto `𝒪`. -/
def finiteTypeCechPresheafAugmentation :
    finiteTypeCechPresheaf X ℐ ⟶ (CochainComplex.singleFunctor _ 0).obj
      (PresheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj) :=
  Stacks.CechFamilySystem.cechAugmentation (generatesFamilySystem X ℐ)

section Slice

variable {X ℐ} (U : X.C)

/-- **Finitely many local generators of `ℐ` over an object of the slice span one ideal locally**,
for the topology of the slice. -/
theorem locallySpanEq_generatesFamilySystem :
    Stacks.CechFamilySystem.LocallySpanEq (generatesFamilySystem X ℐ) (Over.forget U)
      (X.J.over U) := by
  intro V T
  obtain ⟨S, hS, hspan⟩ := exists_mem_sieve_span_eq_of_mem (V := op V.left) T
  refine ⟨(Sieve.overEquiv V).symm S, ?_, fun W b hb x hx y hy => ?_⟩
  · rw [GrothendieckTopology.mem_over_iff, OrderIso.apply_symm_apply]
    exact hS
  · exact hspan b.left ((Sieve.overEquiv_symm_iff S b).1 hb) x hx y hy

variable {s : ℕ} (g : Fin s → Presheaf.globalSections ((X.over U).O.obj ⋙ forget CommRingCat.{u}))
  (hg : idealOfGlobalSections (X.over U) g = overIdeal ℐ U)

/-- **The leg of a generating family of `ℐ|_U`**, in nonnegative degrees: the sectionwise Čech
complex of the family on the slice maps into the restriction to the slice of the presheaf of
Čech complexes of all local generators. -/
def finiteTypeCechLegNat :
    Stacks.CechPresheaf.cechPresheafComplexNat ((Over.forget U).op ⋙ X.O.obj)
        (cechFamily (X.over U) g) (cechFamily_map (X.over U) g) ⟶
      ((PresheafOfModules.pushforward₀OfCommRingCat (Over.forget U) X.O.obj).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          (Stacks.CechFamilySystem.cechComplexPresheafNat (generatesFamilySystem X ℐ)) :=
  Stacks.CechFamilySystem.legNat (Over.forget U) (generatesFamilySystem X ℐ)
    (cechFamily (X.over U) g) (cechFamily_map (X.over U) g)
    (mem_generatesFamilySystem_of_eq U g hg)

/-- The leg is locally surjective on homology, in nonnegative degrees. -/
theorem isLocallySurjective_homologyMap_finiteTypeCechLegNat (n : ℕ) :
    Presheaf.IsLocallySurjective (X.J.over U) ((PresheafOfModules.toPresheaf _).map
      (HomologicalComplex.homologyMap (finiteTypeCechLegNat U g hg) n)) :=
  Stacks.CechFamilySystem.isLocallySurjective_homologyMap_legNat _ _ _
    (locallySpanEq_generatesFamilySystem U) n

/-- The leg is locally injective on homology, in nonnegative degrees. -/
theorem isLocallyInjective_homologyMap_finiteTypeCechLegNat (n : ℕ) :
    Presheaf.IsLocallyInjective (X.J.over U) ((PresheafOfModules.toPresheaf _).map
      (HomologicalComplex.homologyMap (finiteTypeCechLegNat U g hg) n)) :=
  Stacks.CechFamilySystem.isLocallyInjective_homologyMap_legNat _ _ _
    (locallySpanEq_generatesFamilySystem U) n

/-- **The leg of a generating family of `ℐ|_U`**, in integer degrees. -/
def finiteTypeCechLeg :
    Stacks.CechPresheaf.cechPresheafComplex ((Over.forget U).op ⋙ X.O.obj)
        (cechFamily (X.over U) g) (cechFamily_map (X.over U) g) ⟶
      ((PresheafOfModules.pushforward₀OfCommRingCat (Over.forget U) X.O.obj).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          (Stacks.CechFamilySystem.cechComplexPresheaf (generatesFamilySystem X ℐ)) :=
  HomologicalComplex.extendMap (finiteTypeCechLegNat U g hg) ComplexShape.embeddingUpNat ≫
    (HomologicalComplex.mapHomologicalComplexExtendIso
      (PresheafOfModules.pushforward₀OfCommRingCat (Over.forget U) X.O.obj)
      (Stacks.CechFamilySystem.cechComplexPresheafNat (generatesFamilySystem X ℐ))
      ComplexShape.embeddingUpNat).hom

/-- **The leg is locally surjective on homology.** -/
theorem isLocallySurjective_homologyMap_finiteTypeCechLeg (n : ℤ) :
    Presheaf.IsLocallySurjective (X.J.over U) ((PresheafOfModules.toPresheaf _).map
      (HomologicalComplex.homologyMap (finiteTypeCechLeg U g hg) n)) := by
  have := PresheafOfModules.isLocallySurjective_homologyMap_extendMap
    (finiteTypeCechLegNat U g hg) (isLocallySurjective_homologyMap_finiteTypeCechLegNat U g hg) n
  rw [finiteTypeCechLeg, HomologicalComplex.homologyMap_comp, Functor.map_comp]
  infer_instance

/-- **The leg is locally injective on homology.** -/
theorem isLocallyInjective_homologyMap_finiteTypeCechLeg (n : ℤ) :
    Presheaf.IsLocallyInjective (X.J.over U) ((PresheafOfModules.toPresheaf _).map
      (HomologicalComplex.homologyMap (finiteTypeCechLeg U g hg) n)) := by
  have := PresheafOfModules.isLocallyInjective_homologyMap_extendMap
    (finiteTypeCechLegNat U g hg) (isLocallyInjective_homologyMap_finiteTypeCechLegNat U g hg) n
  rw [finiteTypeCechLeg, HomologicalComplex.homologyMap_comp, Functor.map_comp]
  infer_instance

/-- The leg, with its target spelled through the restriction functor of
`SheafifyOverComparison.lean`. -/
def finiteTypeCechLegOver :
    cechPresheafComplex (X.over U) g ⟶
      ((presheafOver X U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (finiteTypeCechPresheaf X ℐ) :=
  finiteTypeCechLeg U g hg

/-- **The leg is a map over `𝒪_U`**, in the form `sheafifyOverMap_comp_restrictStructureSheafMap`
consumes. -/
theorem finiteTypeCechLegOver_comp_augmentation :
    finiteTypeCechLegOver U g hg ≫
        ((presheafOver X U).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (finiteTypeCechPresheafAugmentation X ℐ) =
      cechPresheafAugmentation (X.over U) g ≫
        (HomologicalComplex.singleMapHomologicalComplex (presheafOver X U)
          (ComplexShape.up ℤ) 0).inv.app
            (PresheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj) := by
  have hA := HomologicalComplex.extendMap_mapHomologicalComplexExtendIso_f
    (PresheafOfModules.pushforward₀OfCommRingCat (Over.forget U) X.O.obj)
    (Stacks.CechFamilySystem.cechComplexPresheafNat (generatesFamilySystem X ℐ))
    (finiteTypeCechLegNat U g hg) ComplexShape.embeddingUpNat
    (show ComplexShape.embeddingUpNat.f 0 = (0 : ℤ) from rfl)
  have hB := Stacks.CechFamilySystem.cechAugmentation_f_zero (generatesFamilySystem X ℐ)
  have hC := HomologicalComplex.singleMapHomologicalComplex_hom_app_self (presheafOver X U)
    (ComplexShape.up ℤ) (0 : ℤ)
    (PresheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj)
  have hD := Stacks.CechFamilySystem.legTerm_zero_comp_cechAugZero (Over.forget U)
    (generatesFamilySystem X ℐ) (cechFamily (X.over U) g) (cechFamily_map (X.over U) g)
    (mem_generatesFamilySystem_of_eq U g hg)
  have hE := Stacks.CechPresheaf.cechPresheafAugmentation_f_zero ((Over.forget U).op ⋙ X.O.obj)
    (cechFamily (X.over U) g) (cechFamily_map (X.over U) g)
  have h' : (finiteTypeCechLegOver U g hg ≫
        ((presheafOver X U).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (finiteTypeCechPresheafAugmentation X ℐ)) ≫
        (HomologicalComplex.singleMapHomologicalComplex (presheafOver X U)
          (ComplexShape.up ℤ) 0).hom.app
            (PresheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj) =
      cechPresheafAugmentation (X.over U) g := by
    refine HomologicalComplex.to_single_hom_ext ?_
    exact (congrArg₂ (· ≫ ·) (congrArg₂ (· ≫ ·) hA (congrArg (presheafOver X U).map hB)) hC).trans
      ((CategoryTheory.Functor.comp_map_comp_map_comp
        (PresheafOfModules.pushforward₀OfCommRingCat (Over.forget U) X.O.obj) _ _ _ _ _ _ _
        hD).trans hE.symm)
  exact (Iso.eq_comp_inv ((HomologicalComplex.singleMapHomologicalComplex (presheafOver X U)
    (ComplexShape.up ℤ) 0).app
      (PresheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj))).2 h'

end Slice

/-! ### The object and the tag -/

/-- **The object `K` of [Stacks, Tag 099E]**: the sheafification of the presheaf of Čech complexes
of all local generators of `ℐ`. -/
def finiteTypeCech :
    CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ℤ :=
  ((moduleSheafificationFunctor X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (finiteTypeCechPresheaf X ℐ)

/-- **The map `K ⟶ 𝒪` of [Stacks, Tag 099E]**: the sheafification of the augmentation of the
presheaf of Čech complexes of all local generators. -/
def finiteTypeCechAugmentation : finiteTypeCech X ℐ ⟶ structureSheafComplex X :=
  sheafifyAugmentation X (finiteTypeCechPresheafAugmentation X ℐ)

section Global

attribute [local instance] HasDerivedCategory.standard additive_overFunctor

/-- **`K ⟶ 𝒪` has the property of [Stacks, Tag 099E]**: on every object `U` and for every finite
family `g` of sections over `U` generating `ℐ|_U`, the extended alternating Čech complex of `g` is
isomorphic to `K|_U` in `D(𝒪_U)`, compatibly with the maps to `𝒪_U`.

The isomorphism is the sheafification of the leg of `g`
(`AlgebraicGeometry.RingedSite.finiteTypeCechLeg`), read through the comparison of sheafification
with restriction to the slice (`AlgebraicGeometry.RingedSite.sheafifyOverMap`): a
quasi-isomorphism because the leg is locally bijective on homology, and a map over `𝒪_U` because
the leg is (`AlgebraicGeometry.RingedSite.finiteTypeCechLegOver_comp_augmentation`). The
sheafified presheaf of Čech complexes of `g` is then the complex the tag displays,
`AlgebraicGeometry.RingedSite.sheafifiedCechIsoExtendedAlternatingCech`. -/
theorem isGlobalExtendedCech_finiteTypeCech :
    IsGlobalExtendedCech X ℐ (finiteTypeCech X ℐ) (finiteTypeCechAugmentation X ℐ) := by
  intro U _ s g hg
  have hq : QuasiIso (sheafifyOverMap (finiteTypeCechLegOver U g hg)) :=
    quasiIso_sheafifyOverMap _ (isLocallyInjective_homologyMap_finiteTypeCechLeg U g hg)
      (isLocallySurjective_homologyMap_finiteTypeCechLeg U g hg)
  have hc : sheafifyOverMap (finiteTypeCechLegOver U g hg) ≫
      restrictStructureSheafMap X U (finiteTypeCechAugmentation X ℐ) =
        sheafifiedCechAugmentation (X.over U) g :=
    sheafifyOverMap_comp_restrictStructureSheafMap _ _ _
      (finiteTypeCechLegOver_comp_augmentation U g hg)
  have hiso := (DerivedCategory.isIso_Q_map_iff_quasiIso
    (C := SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)))
    (K := sheafifiedCech (X.over U) g)
    (L := ((SheafOfModules.overFunctor
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (finiteTypeCech X ℐ))
    (sheafifyOverMap (finiteTypeCechLegOver U g hg))).2 hq
  refine ⟨(DerivedCategory.Q.mapIso
      (sheafifiedCechIsoExtendedAlternatingCech (X.over U) g)).symm ≪≫
    @asIso _ _ _ _ (DerivedCategory.Q.map (sheafifyOverMap (finiteTypeCechLegOver U g hg))) hiso,
    ?_⟩
  exact CategoryTheory.Functor.map_inv_comp_map_comp_map DerivedCategory.Q _ _ _ _ _ hc
    (sheafifiedCechIsoExtendedAlternatingCech_hom_comp_cechAugmentation (X.over U) g)

/-- **[Stacks, Tag 099E]**: for a sheaf of ideals `ℐ ⊆ 𝒪` on a ringed site there is a map
`K ⟶ 𝒪` such that for every object `U` and every finite family of sections over `U` generating
`ℐ|_U`, the extended alternating Čech complex of the family is isomorphic to `K|_U` in `D(𝒪_U)`,
compatibly with the maps to `𝒪_U`.

The source assumes `ℐ` of finite type; the construction does not use it — over an object on which
`ℐ` is not finitely generated the condition is empty — so it is not assumed here. The map is a map
of complexes, `AlgebraicGeometry.RingedSite.finiteTypeCechAugmentation`, whose image in `D(𝒪)` is
the map of the tag. -/
@[stacks 099E]
theorem exists_isGlobalExtendedCech :
    ∃ (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
      (a : K ⟶ structureSheafComplex X),
      IsGlobalExtendedCech X ℐ K a :=
  ⟨finiteTypeCech X ℐ, finiteTypeCechAugmentation X ℐ, isGlobalExtendedCech_finiteTypeCech X ℐ⟩

end Global

end AlgebraicGeometry.RingedSite

end
