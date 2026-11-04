module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedLimitOfTruncations
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfSheafFromSheafFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AssociatedModuleBaseChangeFinalSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LiftedFppfFamilyFromDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LiftedSectionsOfSheafifiedComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangePropertySheafified
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeWeakSerreEtaleModules
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineZariskiRefinement
public import StacksFrontier.AlgebraicGeometry.TopDirectImageRightExact.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSiteOfLe

/-!
# `LQCoh^fbc` in the fppf modules: kernels, cokernels and the extension step (Stacks 0771 (2))

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and `Mod(𝒪_𝒳)` the sheaves of
modules on its fppf site. This file proves the fppf half of **Stacks 0771 (2)** for
`LQCoh^fbc(𝒪_𝒳)` with the flat base change property of Stacks 0762 read with the pullback of
sheaves, following the source:

* a kernel computed in `Mod(𝒪_𝒳)` is the kernel computed in `Mod(𝒳_ét, 𝒪_𝒳)`, so the étale case
  (`AlgebraicGeometry.Stack.isWeakSerreClass_locallyQuasicoherentSheafFlatBaseChange`) applies;
* the cokernel computed in `Mod(𝒪_𝒳)` is the fppf sheafification of the cokernel computed in
  `Mod(𝒳_ét, 𝒪_𝒳)`, which is already an fppf sheaf by Stacks 0771 (1)
  (`AlgebraicGeometry.Stack.isSheaf_fppf_of_isLocallyQuasicoherentWithSheafFlatBaseChange`);
* an extension in `Mod(𝒪_𝒳)` of two members is an extension in `Mod(𝒳_ét, 𝒪_𝒳)` as soon as its
  quotient map is an epimorphism of étale sheaves, and then the étale case applies.

The last condition is what the source obtains from `H^1_{fppf}(x, ℱ₁) = H^1_{ét}(x, ℱ₁)`
(Stacks 075R) and the locality of cohomology; here it is the hypothesis of
`AlgebraicGeometry.Stack.isWeakSerreClass_locallyQuasicoherentSheafFlatBaseChangeFppf_of_epi`, and
`AlgebraicGeometry.Stack.epi_fppfToEtaleComparison_map_of_rightDerived_vanishing` derives it from
the vanishing of `H^1_{fppf}(x, ℱ₁)` on objects lying over affine schemes.

## Main definitions

* `AlgebraicGeometry.Stack.locallyQuasicoherentSheafFlatBaseChangeFppfSiteModules`: the class
  `LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)` for a category fibred in groupoids.

## Main results

* `AlgebraicGeometry.Stack.isWeakSerreClass_locallyQuasicoherentSheafFlatBaseChangeFppf_of_epi`
* `AlgebraicGeometry.Stack.epi_fppfToEtaleComparison_map_of_rightDerived_vanishing`
* `Stack.isWeakSerreClass_locallyQuasicoherentSheafFlatBaseChangeFppf_of_rightDerived_vanishing`
* `CategoryTheory.Sheaf.epi_of_isLocallySurjective_addCommGrpCat`: a locally surjective morphism
  of sheaves of abelian groups is an epimorphism, on any site.

## References

* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 075R](https://stacks.math.columbia.edu/tag/075R)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject

universe u v w

namespace CategoryTheory.Sheaf

/-- **A locally surjective morphism of sheaves of abelian groups is an epimorphism**, for an
arbitrary site: the underlying presheaves of sets of sheaves of abelian groups are sheaves, which
is all the separatedness argument needs. -/
@[sga "4½ Arcata 1.6.3" "partial"]
theorem epi_of_isLocallySurjective_addCommGrpCat {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {P Q : Sheaf J AddCommGrpCat.{u}} (φ : P ⟶ Q)
    [Presheaf.IsLocallySurjective J φ.hom] : Epi φ where
  left_cancellation {Z} f₁ f₂ h := by
    have hZ : Presheaf.IsSheaf J (Z.obj ⋙ CategoryTheory.forget AddCommGrpCat.{u}) :=
      Presheaf.isSheaf_comp_of_isSheaf J Z.obj (CategoryTheory.forget AddCommGrpCat.{u}) Z.property
    ext X x
    apply (((isSheaf_iff_isSheaf_of_type _ _).1 hZ).isSeparated _
      (Presheaf.imageSieve_mem J φ.hom x)).ext
    rintro Y f ⟨s, hs⟩
    have h₁ := ConcreteCategory.congr_hom (f₁.hom.naturality f.op) x
    have h₂ := ConcreteCategory.congr_hom (f₂.hom.naturality f.op) x
    simp only [ConcreteCategory.comp_apply] at h₁ h₂
    show (Z.obj.map f.op) (f₁.hom.app X x) = (Z.obj.map f.op) (f₂.hom.app X x)
    rw [← h₁, ← h₂]
    show f₁.hom.app _ ((Q.obj.map f.op) x) = f₂.hom.app _ ((Q.obj.map f.op) x)
    rw [← hs]
    exact ConcreteCategory.congr_hom (congr_app ((sheafToPresheaf J _).congr_map h) (op Y)) s

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- **The subcategory `LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)`** of the sheaves of modules on the fppf site of
a category fibred in groupoids which are locally quasi-coherent (Stacks 06WJ) and have the flat
base change property of Stacks 0762, read with the pullback of sheaves. -/
abbrev locallyQuasicoherentSheafFlatBaseChangeFppfSiteModules :
    ObjectProperty (fppfSiteModules B S hS p hp) :=
  fun F => IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, v, w, u} B E h S hS p hp F.val

/-- The comparison `ε_*` from fppf modules to étale modules: the same presheaf of modules, read
as a sheaf for the coarser étale topology. -/
abbrev fppfToEtaleComparison :=
  Stacks.SheafOfModules.comparisonPushforward.{v, w, u, u}
    (BigFppfOver.associatedTopology_le_fppf B S hS p .etale) (fppfSiteRingSheaf B S hS p hp)

/-- The étale associated topology has sheafification and `W = locally bijective`. -/
private theorem hasSheafify_and_wEqualsLocallyBijective_etale (hp : p.IsFiberedInGroupoids) :
    HasSheafify (BigFppfOver.associatedTopology B S hS p .etale) AddCommGrpCat.{u} ∧
      (BigFppfOver.associatedTopology B S hS p .etale).WEqualsLocallyBijective
        AddCommGrpCat.{u} :=
  ⟨hasSheafify_etaleAssociatedTopology B S hS p hp,
    wEqualsLocallyBijective_etaleAssociatedTopology B S hS p hp⟩

variable [HasSheafify (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u}]
  [(BigFppfOver.associatedTopology B S hS p .fppf).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Stacks 0771 (2) for `Mod(𝒪_𝒳)`, over the extension step.** If for every short exact
sequence `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` of fppf modules with `ℱ₁` in `LQCoh^fbc(𝒪_𝒳)` the quotient map
`ℱ₂ ⟶ ℱ₃` is an epimorphism of étale sheaves, then `LQCoh^fbc(𝒪_𝒳)` is a weak Serre subcategory
of `Mod(𝒪_𝒳)`. -/
theorem isWeakSerreClass_locallyQuasicoherentSheafFlatBaseChangeFppf_of_epi
    (hepi : ∀ {T : ShortComplex (fppfSiteModules B S hS p hp)}, T.ShortExact →
      locallyQuasicoherentSheafFlatBaseChangeFppfSiteModules B E h S hS p hp T.X₁ →
        Epi ((fppfToEtaleComparison B S hS p hp).map T.g)) :
    (locallyQuasicoherentSheafFlatBaseChangeFppfSiteModules B E h S hS p hp).IsWeakSerreClass := by
  obtain ⟨_, _⟩ := hasSheafify_and_wEqualsLocallyBijective_etale B S hS p hp
  let ε := fppfToEtaleComparison B S hS p hp
  let Pe : ObjectProperty (SheafOfModules.{u} (Stacks.SheafOfModules.ringOfLe
      (BigFppfOver.associatedTopology_le_fppf B S hS p .etale) (fppfSiteRingSheaf B S hS p hp))) :=
    fun F => IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, v, w, u} B E h S hS p hp F.val
  have hPe : Pe.IsWeakSerreClass :=
    isWeakSerreClass_locallyQuasicoherentSheafFlatBaseChange B E h S hS p hp
  have : ε.Additive := Stacks.SheafOfModules.additive_comparisonPushforward _ _
  have : ε.IsRightAdjoint :=
    (Stacks.SheafOfModules.comparisonAdjunction.{v, w, u, u}
      (BigFppfOver.associatedTopology_le_fppf B S hS p .etale)
      (fppfSiteRingSheaf B S hS p hp)).isRightAdjoint
  have : ε.Full := (Stacks.SheafOfModules.comparisonPushforwardFullyFaithful _ _).full
  have : ε.Faithful := (Stacks.SheafOfModules.comparisonPushforwardFullyFaithful _ _).faithful
  exact
  { exists_zero := by
      obtain ⟨Z, hZ, hPZ⟩ := Pe.exists_prop_of_containsZero
      refine ⟨0, isZero_zero _, ?_⟩
      exact Pe.prop_of_iso ((hZ.iso (ε.map_isZero (isZero_zero _)))) hPZ
    of_iso := fun e hX => Pe.prop_of_iso (ε.mapIso e) hX
    kernels_le := by
      rintro _ ⟨f, k, hk, hX, hY⟩
      exact Pe.prop_of_isLimit_kernelFork
        ((KernelFork.isLimitMapConeEquiv _ ε) (isLimitOfPreserves ε hk)) hX hY
    cokernels_le := by
      rintro _ ⟨f, k, hk, hX, hY⟩
      obtain ⟨cE, ⟨hcE⟩⟩ : ∃ cE : CokernelCofork (ε.map f), Nonempty (IsColimit cE) :=
        ⟨_, ⟨cokernelIsCokernel _⟩⟩
      have hc : Pe cE.pt := Pe.prop_of_isColimit_cokernelCofork hcE hX hY
      have hsh := isSheaf_fppf_of_isLocallyQuasicoherentWithSheafFlatBaseChange B E h S hS p hp
        cE.pt.val hc
      let c' : fppfSiteModules B S hS p hp := ⟨cE.pt.val, hsh⟩
      let π' : _ ⟶ c' :=
        (Stacks.SheafOfModules.comparisonPushforwardFullyFaithful _ _).preimage cE.π
      have hπ' : ε.map π' = cE.π :=
        (Stacks.SheafOfModules.comparisonPushforwardFullyFaithful _ _).map_preimage _
      have hz : f ≫ π' = 0 := ε.map_injective (by
        rw [ε.map_comp, hπ', ε.map_zero]
        exact cE.condition)
      have hcol : IsColimit (CokernelCofork.ofπ π' hz) := by
        refine isColimitOfReflects ε ?_
        refine (CokernelCofork.isColimitMapCoconeEquiv _ ε).symm ?_
        refine IsColimit.ofIsoColimit hcE ?_
        refine Cofork.ext (Iso.refl _) ?_
        show cE.π ≫ 𝟙 _ = ε.map π'
        rw [Category.comp_id, hπ']
      exact Pe.prop_of_iso (ε.mapIso (IsColimit.coconePointUniqueUpToIso hcol hk)) hc
    prop_X₂_of_shortExact := by
      intro T hT h₁ h₃
      have := hT.mono_f
      have : Epi ((T.map ε).g) := hepi hT h₁
      have hk : IsLimit (KernelFork.ofι (T.map ε).f (T.map ε).zero) :=
        (KernelFork.isLimitMapConeEquiv _ ε) (isLimitOfPreserves ε hT.fIsKernel)
      have : Mono (T.map ε).f := Fork.IsLimit.mono hk
      exact Pe.prop_X₂_of_shortExact ⟨ShortComplex.exact_of_f_is_kernel _ hk⟩ h₁ h₃ }

section Extension

attribute [local instance] Stacks.Cohomology.AcyclicCover.evaluation_additive
  HasDerivedCategory.standard

variable [EnoughInjectives (fppfSiteModules B S hS p hp)]

/-- **The extension step of Stacks 0771 (2), from the affine vanishing.** If `H^1_{fppf}(x, ℱ)`
vanishes for every `ℱ` in `LQCoh^fbc(𝒪_𝒳)` and every object `x` lying over an affine scheme,
then for a short exact sequence `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` of fppf modules with `ℱ₁` in
`LQCoh^fbc(𝒪_𝒳)` the map `ℱ₂ ⟶ ℱ₃` is an epimorphism of étale sheaves: every section of `ℱ₃`
over an object lying over an affine scheme lifts to `ℱ₂` (the long exact sequence of `H^*`), and
those objects cover every object for the étale topology. -/
theorem epi_fppfToEtaleComparison_map_of_rightDerived_vanishing
    (hvan : ∀ F : fppfSiteModules B S hS p hp,
      locallyQuasicoherentSheafFlatBaseChangeFppfSiteModules B E h S hS p hp F →
        ∀ x : 𝒳, IsAffineOver B S hS (p.obj x) →
          IsZero (((SheafOfModules.evaluation (fppfSiteRingSheaf B S hS p hp)
            (Opposite.op x)).rightDerived 1).obj F))
    {T : ShortComplex (fppfSiteModules B S hS p hp)} (hT : T.ShortExact)
    (h₁ : locallyQuasicoherentSheafFlatBaseChangeFppfSiteModules B E h S hS p hp T.X₁) :
    Epi ((fppfToEtaleComparison B S hS p hp).map T.g) := by
  obtain ⟨_, _⟩ := hasSheafify_and_wEqualsLocallyBijective_etale B S hS p hp
  -- surjectivity on sections over objects lying over affine schemes
  have hsurj : ∀ x : 𝒳, IsAffineOver B S hS (p.obj x) →
      Function.Surjective ((SheafOfModules.evaluation (fppfSiteRingSheaf B S hS p hp)
        (Opposite.op x)).map T.g) := by
    intro x hx
    let ev := SheafOfModules.evaluation (fppfSiteRingSheaf B S hS p hp) (Opposite.op x)
    have : PreservesFiniteLimits ev :=
      _root_.SheafOfModules.Finite.evaluationPreservesFiniteLimits (fppfSiteRingSheaf B S hS p hp) _
    have h0 : Epi ((ev.rightDerived 0).map T.g) :=
      Stacks.TopDirectImageRightExact.epi_rightDerived_map_g ev hT 0 (hvan _ h₁ x hx)
    have hfac : ev.map T.g = ev.rightDerivedZeroIsoSelf.inv.app _ ≫
        (ev.rightDerived 0).map T.g ≫ ev.rightDerivedZeroIsoSelf.hom.app _ := by
      rw [NatTrans.naturality, Iso.inv_hom_id_app_assoc]
    have : Epi (ev.map T.g) := by
      rw [hfac]
      exact epi_comp' (IsIso.epi_of_iso _) (epi_comp' h0 (IsIso.epi_of_iso _))
    exact (ModuleCat.epi_iff_surjective _).1 this
  -- local surjectivity on the étale site
  let g := (SheafOfModules.toSheaf _).map ((fppfToEtaleComparison B S hS p hp).map T.g)
  have hls : Sheaf.IsLocallySurjective g := by
    refine ⟨fun {X} s => ?_⟩
    obtain ⟨I, y, φ, hy, hcov⟩ := FibredSite.exists_affine_ofArrows_etale B S hS p hp X
    refine (BigFppfOver.associatedTopology B S hS p .etale).superset_covering ?_ hcov
    intro Z a ha
    rw [Sieve.mem_ofArrows_iff] at ha
    obtain ⟨j, b, rfl⟩ := ha
    refine Sieve.downward_closed _ ?_ b
    obtain ⟨t, ht⟩ := hsurj (y j) (hy j) (T.X₃.val.presheaf.map (φ j).op s)
    exact ⟨t, ht⟩
  have hg : Epi g := Sheaf.epi_of_isLocallySurjective_addCommGrpCat g
  have hfaith : (_root_.SheafOfModules.toSheaf (Stacks.SheafOfModules.ringOfLe
      (BigFppfOver.associatedTopology_le_fppf B S hS p .etale)
      (fppfSiteRingSheaf B S hS p hp))).Faithful :=
    Functor.Faithful.of_comp_iso (_root_.SheafOfModules.toSheafCompSheafToPresheafIso _)
  exact @Functor.epi_of_epi_map _ _ _ _ _ (Functor.reflectsEpimorphisms_of_faithful _) _ _ _ hg

/-- **Stacks 0771 (2) for `Mod(𝒪_𝒳)`, over the affine vanishing.** If `H^1_{fppf}(x, ℱ)`
vanishes for every `ℱ` in `LQCoh^fbc(𝒪_𝒳)` and every object `x` lying over an affine scheme, then
`LQCoh^fbc(𝒪_𝒳)` is a weak Serre subcategory of `Mod(𝒪_𝒳)`. -/
theorem isWeakSerreClass_locallyQuasicoherentSheafFlatBaseChangeFppf_of_rightDerived_vanishing
    (hvan : ∀ F : fppfSiteModules B S hS p hp,
      locallyQuasicoherentSheafFlatBaseChangeFppfSiteModules B E h S hS p hp F →
        ∀ x : 𝒳, IsAffineOver B S hS (p.obj x) →
          IsZero (((SheafOfModules.evaluation (fppfSiteRingSheaf B S hS p hp)
            (Opposite.op x)).rightDerived 1).obj F)) :
    (locallyQuasicoherentSheafFlatBaseChangeFppfSiteModules B E h S hS p hp).IsWeakSerreClass :=
  isWeakSerreClass_locallyQuasicoherentSheafFlatBaseChangeFppf_of_epi B E h S hS p hp
    fun hT h₁ => epi_fppfToEtaleComparison_map_of_rightDerived_vanishing B E h S hS p hp hvan hT h₁

end Extension

end AlgebraicGeometry.Stack
