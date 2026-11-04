module

public import StacksFrontier.AlgebraicGeometry.WeilDeRham.DiagonalCupStatements
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.DerivedSectionsBridge
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.StarIdentityProof
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.FormsTopGeneratorSection
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.FormsTopGeneratorFibres
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.CohomologyDerivedSingleIsoNaturality
public import StacksFrontier.AlgebraicGeometry.CohomologyGlobalSectionScalar.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.LocalDescentRefine
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedGlobalCupProduct.UnitEvaluation

/-!
# The Gysin class of a section generates the top cohomology of forms over the base

Let `A` be a Noetherian ring and `f : X ⟶ Spec A` proper and smooth of relative dimension
`n = e + 1` with `A ⟶ Γ(X, 𝒪_X)` bijective, and let `σ` be a section of `f`. The Gysin class
`ξ ∈ Hⁿ(X, Ωⁿ_{X/A})` of `σ` generates `Hⁿ(X, Ωⁿ_{X/A})` over `A` on the alternating Čech complex
of a finite affine covering (`Stacks.Cech.span_sectionGysinClass_eq_top`), so every class is the
image of `ξ` under multiplication by a function coming from the base. This file reads that
statement in the `Γ(Spec A, 𝒪)`-module `Hⁿ(RΓ_A(X, Ωⁿ_{X/A}))` of derived sections over the base,
through `hgroupSectionsOverBaseIso`.

The bridge from the multiplication map to the scalar action is the linearity of derived global
sections: multiplication by a global function `b` is a natural endomorphism of every complex of
modules; on a K-injective complex the derived global sections are computed termwise, where it is
the scalar action of `b` (`cohomologyModule_map_complexGlobalSmul_of_isKInjective`), and a
K-injective resolution transports this to every module placed in degree `0`
(`cohomologyModule_map_single_globalSmul`).

## Main definitions

* `Stacks.WeilDeRham.complexGlobalSmul`: multiplication by a global function on a complex.

## Main results

* `Stacks.WeilDeRham.hgroupSectionsOverBaseIso_globalSmul`: `hgroupSectionsOverBaseIso` carries
  multiplication by the image of a function on the base to its scalar action.
* `Stacks.WeilDeRham.sectionClassNormalized_generates`: every class of `Hⁿ(X, Ωⁿ_{X/A})` is a
  multiple of `ξ` in `Hⁿ(RΓ_A(X, Ωⁿ_{X/A}))`.

## References

* [Stacks Project, Tag 0G8J](https://stacks.math.columbia.edu/tag/0G8J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open AlgebraicGeometry.Scheme.Hom
open Stacks.Cohomology.GlobalKunneth (baseRing)
open scoped Stacks.StandardDerivedModel

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.WeilDeRham

attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat
attribute [local instance] Stacks.DeRham.CohomologicalGysin.moduleSheavesHasDerivedCategory
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules
  AlgebraicGeometry.SheafOfModules.hasSheafifyOpens
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijectiveOpens

section Linearity

open Stacks.DeRham.CohomologicalGysin

variable {V : Scheme.{u}}

/-- Multiplication by a global function, termwise on a complex of modules. -/
def complexGlobalSmul (b : Γ(V, ⊤)) (N : CochainComplex V.Modules ℤ) : N ⟶ N where
  f i := globalSmul b (N.X i)
  comm' i j _ := (comp_globalSmul b (N.d i j)).symm

/-- Multiplication by a global function is natural in the complex. -/
theorem complexGlobalSmul_naturality (b : Γ(V, ⊤)) {N N' : CochainComplex V.Modules ℤ}
    (g : N ⟶ N') : complexGlobalSmul b N ≫ g = g ≫ complexGlobalSmul b N' := by
  ext i : 1
  exact (comp_globalSmul b (g.f i)).symm

/-- On a module placed in degree `0`, multiplication by a global function is the single complex
of multiplication on the module. -/
theorem complexGlobalSmul_single (b : Γ(V, ⊤)) (F : V.Modules) :
    complexGlobalSmul b ((HomologicalComplex.single V.Modules (ComplexShape.up ℤ) 0).obj F) =
      (HomologicalComplex.single V.Modules (ComplexShape.up ℤ) 0).map (globalSmul b F) := by
  apply HomologicalComplex.to_single_hom_ext
  rw [HomologicalComplex.single_map_f_self]
  have h := comp_globalSmul b (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom
  rw [reassoc_of% h, Iso.hom_inv_id, Category.comp_id]
  rfl

/-- A monomorphism of modules detects scalar multiples. -/
private lemma eq_smul_of_hom_eq_smul {R : Type u} [Ring R] {M N : ModuleCat.{u} R} (φ : M ⟶ N)
    [Mono φ] (r : R) {x y : M} (h : φ.hom x = r • φ.hom y) : x = r • y :=
  ((ModuleCat.mono_iff_injective φ).1 ‹_›) (h.trans (map_smul φ.hom r y).symm)

open Stacks.Cohomology.DerivedGlobalCupProduct (cohomologyModule globalClass sectionsComplex) in
/-- On a K-injective complex, multiplication by a global function induces the scalar action on
the cohomology of derived global sections. -/
theorem cohomologyModule_map_complexGlobalSmul_of_isKInjective (b : Γ(V, ⊤))
    (I : CochainComplex V.Modules ℤ) (hI : I.IsKInjective) (n : ℤ)
    (y : cohomologyModule (DerivedCategory.Q.obj I) n) :
    ((DerivedCategory.homologyFunctor _ n).map
        ((Stacks.Cohomology.GlobalKunneth.baseSections V.toRingedSpace).map
          (DerivedCategory.Q.map (complexGlobalSmul b I)))).hom y = b • y := by
  obtain ⟨z, rfl⟩ :=
    Stacks.Cohomology.DerivedGlobalCupProduct.exists_globalClass_of_isKInjective I hI n y
  refine (Stacks.Cohomology.DerivedGlobalCupProduct.globalClass_map V.toRingedSpace
    (complexGlobalSmul b I) n z).trans ?_
  have hz : (HomologicalComplex.cyclesMap
      (((Stacks.Cohomology.DerivedGlobalCupProduct.globalSections
        V.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (complexGlobalSmul b I)) n).hom z = b • z := by
    apply eq_smul_of_hom_eq_smul ((sectionsComplex V.toRingedSpace I).iCycles n)
    refine (ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i _ n) z).trans ?_
    exact globalSmul_app_top b (I.X n) _
  rw [hz]
  exact map_smul _ b z

/-- A functor into modules applied to a commuting square, on an element. At variables. -/
private lemma map_square_apply {C : Type*} [Category C] {R : Type u} [Ring R]
    (Φ : C ⥤ ModuleCat.{u} R) {P Q : C} (a : P ⟶ P) (s : P ⟶ Q) (c : Q ⟶ Q)
    (h : a ≫ s = s ≫ c) (x : Φ.obj P) :
    (Φ.map s).hom ((Φ.map a).hom x) = (Φ.map c).hom ((Φ.map s).hom x) := by
  rw [← ModuleCat.comp_apply, ← Functor.map_comp, h, Functor.map_comp, ModuleCat.comp_apply]

open Stacks.Cohomology.DerivedGlobalCupProduct (cohomologyModule) in
/-- **Multiplication by a global function induces the scalar action on the cohomology of the
derived global sections of a module placed in degree `0`.** -/
theorem cohomologyModule_map_single_globalSmul (b : Γ(V, ⊤)) (F : V.Modules) (n : ℤ)
    (y : cohomologyModule ((DerivedCategory.singleFunctor V.Modules 0).obj F) n) :
    ((DerivedCategory.homologyFunctor _ n).map
        ((Stacks.Cohomology.GlobalKunneth.baseSections V.toRingedSpace).map
          ((DerivedCategory.singleFunctor V.Modules 0).map (globalSmul b F)))).hom y = b • y := by
  obtain ⟨I, s, hI, hs⟩ :=
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective V.toRingedSpace
      ((HomologicalComplex.single V.Modules (ComplexShape.up ℤ) 0).obj F)
  let Φ := Stacks.Cohomology.GlobalKunneth.baseSections V.toRingedSpace ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing V.toRingedSpace)) n
  have hsq : (DerivedCategory.singleFunctor V.Modules 0).map (globalSmul b F) ≫
      DerivedCategory.Q.map s = DerivedCategory.Q.map s ≫
        DerivedCategory.Q.map (complexGlobalSmul b I) := by
    have hc : (HomologicalComplex.single V.Modules (ComplexShape.up ℤ) 0).map (globalSmul b F) ≫ s =
        s ≫ complexGlobalSmul b I := by
      rw [← complexGlobalSmul_single]
      exact complexGlobalSmul_naturality b s
    exact (DerivedCategory.Q.map_comp _ _).symm.trans
      ((congrArg DerivedCategory.Q.map hc).trans (DerivedCategory.Q.map_comp _ _))
  have hiso : IsIso (DerivedCategory.Q.map s) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hs
  have hΦ : IsIso (Φ.map (DerivedCategory.Q.map s)) :=
    (Φ.mapIso (@asIso _ _ _ _ (DerivedCategory.Q.map s) hiso)).isIso_hom
  have := @IsIso.mono_of_iso _ _ _ _ _ hΦ
  apply eq_smul_of_hom_eq_smul (Φ.map (DerivedCategory.Q.map s))
  refine (map_square_apply Φ _ _ _ hsq y).trans ?_
  exact cohomologyModule_map_complexGlobalSmul_of_isKInjective b I hI n _

/-- The map on cohomology of a morphism of sheaves placed in degree `0` is the map it induces on
cohomology groups. -/
theorem cohomologyMapOfSingleHom_singleFunctor_map {X : RingedSpace.{u, u}}
    {F G : SheafOfModules.{u} (structureSheafRing X)} (ψ : F ⟶ G) (q : ℕ) :
    cohomologyMapOfSingleHom X F G 0 q
        ((DerivedCategory.singleFunctor _ ((0 : ℕ) : ℤ)).map ψ) =
      (Hfunctor (structureSheafRing X) ⊤ q).map ψ :=
  (Iso.inv_comp_eq _).2 (cohomologyDerivedSingleIso_hom_naturality X ψ ((0 : ℕ) : ℤ)
    ((q : ℤ) + ((0 : ℕ) : ℤ)) q (by omega))

/-- **On the cohomology of derived sections over the base, multiplication by the image of a
function on the base is the scalar action of that function.** -/
theorem homology_sectionsOverBase_map_globalSmul {S : Scheme.{u}} (c : V ⟶ S) (r : Γ(S, ⊤))
    (F : V.Modules) (m : ℤ)
    (w : (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S.toRingedSpace)) m).obj
      ((Stacks.Cohomology.GlobalKunneth.sectionsOverBase c.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor V.Modules 0).obj F))) :
    ((DerivedCategory.homologyFunctor _ m).map
        ((Stacks.Cohomology.GlobalKunneth.sectionsOverBase c.toLRSHom.toShHom).map
          ((DerivedCategory.singleFunctor V.Modules 0).map (globalSmul (c.appTop r) F)))).hom w =
      r • w := by
  apply eq_smul_of_hom_eq_smul (sectionsOverBaseHomologyIso c.toLRSHom.toShHom
    ((DerivedCategory.singleFunctor V.Modules 0).obj F) m).hom
  refine (ConcreteCategory.congr_hom (sectionsOverBaseHomologyIso_hom_naturality
    c.toLRSHom.toShHom ((DerivedCategory.singleFunctor V.Modules 0).map
      (globalSmul (c.appTop r) F)) m) w).trans ?_
  exact cohomologyModule_map_single_globalSmul (c.appTop r) F m _

/-- **The identification `hgroupSectionsOverBaseIso` is linear over the base**: it carries the
map induced on `H^q(V, F)` by multiplication by the image of a function `r` on the base to the
scalar action of `r`. -/
theorem hgroupSectionsOverBaseIso_globalSmul {S : Scheme.{u}} (c : V ⟶ S) (F : V.Modules) (q : ℕ)
    (r : baseRing S.toRingedSpace) (x : Hgroup (structureSheafRing V.toRingedSpace) ⊤ q F) :
    (show (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S.toRingedSpace)) (q : ℤ)).obj
        ((Stacks.Cohomology.GlobalKunneth.sectionsOverBase c.toLRSHom.toShHom).obj
          ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing V.toRingedSpace))
            ((0 : ℕ) : ℤ)).obj F)) from
      (hgroupSectionsOverBaseIso c.toLRSHom.toShHom F 0 q q (by simp)).hom
        ((Hfunctor (structureSheafRing V.toRingedSpace) ⊤ q).map (globalSmul (c.appTop r) F) x)) =
      r • (show (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S.toRingedSpace))
          (q : ℤ)).obj ((Stacks.Cohomology.GlobalKunneth.sectionsOverBase c.toLRSHom.toShHom).obj
            ((DerivedCategory.singleFunctor (SheafOfModules.{u}
              (structureSheafRing V.toRingedSpace)) ((0 : ℕ) : ℤ)).obj F)) from
        (hgroupSectionsOverBaseIso c.toLRSHom.toShHom F 0 q q (by simp)).hom x) := by
  have h₁ := congrArg (fun φ => ((hgroupSectionsOverBaseIso c.toLRSHom.toShHom F 0 q q
    (by simp)).hom).hom (φ.hom x))
    (cohomologyMapOfSingleHom_singleFunctor_map (globalSmul (c.appTop r) F) q)
  have h₂ := hgroupSectionsOverBaseIso_cohomologyMapOfSingleHom c.toLRSHom.toShHom F F 0 q
    (q : ℤ) (by simp) (by simp)
    ((DerivedCategory.singleFunctor _ ((0 : ℕ) : ℤ)).map (globalSmul (c.appTop r) F)) x
  exact h₁.symm.trans (h₂.trans (homology_sectionsOverBase_map_globalSmul c r F (q : ℤ) _))

end Linearity

section TopClass

open Stacks.DeRham.CohomologicalGysin Stacks.DeRham.GysinCohomologyBaseChange

/-- Being a multiple of a class by functions of the base is invariant under `classTransport`. -/
theorem exists_eq_globalSmul_classTransport {Y : Scheme.{u}} (M : ℤ → Y.Modules) {k k' : ℤ}
    (hk : k = k') {N N' : ℕ} (hN : N = N') {R : Type*} (g : R → Γ(Y, ⊤))
    (ξ : Hgroup (structureSheafRing Y.toRingedSpace) ⊤ N (M k))
    (h : ∀ y : Hgroup (structureSheafRing Y.toRingedSpace) ⊤ N (M k),
      ∃ a, y = ((Hfunctor (structureSheafRing Y.toRingedSpace) ⊤ N).map
        (globalSmul (g a) (M k))).hom ξ)
    (x : Hgroup (structureSheafRing Y.toRingedSpace) ⊤ N' (M k')) :
    ∃ a, x = ((Hfunctor (structureSheafRing Y.toRingedSpace) ⊤ N').map
      (globalSmul (g a) (M k'))).hom ((classTransport (Y := Y.toRingedSpace) M hk hN).hom ξ) := by
  subst hk hN
  obtain ⟨a, ha⟩ := h x
  refine ⟨a, ha.trans ?_⟩
  have h₂ : ∀ p : M k = M k,
      ((Hfunctor (structureSheafRing Y.toRingedSpace) ⊤ N).map (eqToHom p)).hom ξ = ξ := by
    intro p
    have hp := eqToHom_refl (C := SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) (M k) p
    refine (congrArg (fun φ => ((Hfunctor (structureSheafRing Y.toRingedSpace) ⊤ N).map φ).hom ξ)
      hp).trans ?_
    exact ConcreteCategory.congr_hom
      ((Hfunctor (structureSheafRing Y.toRingedSpace) ⊤ N).map_id (M k)) ξ
  exact (congrArg _ (h₂ _)).symm

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (e : ℕ)
  (σ : Spec (.of A) ⟶ X) [IsClosedImmersion σ] [LocallyOfFinitePresentation σ]
  [SmoothOfRelativeDimension (e + 1) f] [Smooth (σ ≫ f)] [FormallyUnramified (σ ≫ f)]

attribute [local instance] Scheme.Hom.isQuasicoherent_relativeDifferentialForms in
/-- **Every class of the top cohomology of forms is a multiple of the Gysin class of a
section**, by a function from the base acting through multiplication of forms. -/
theorem exists_eq_globalSmul_sectionGysinClass [IsNoetherianRing A] [IsProper f]
    [IsIso f.appTop] (hσ : σ ≫ f = 𝟙 _)
    (y : Hgroup (structureSheafRing X.toRingedSpace) ⊤ (0 + (e + 1))
      (relativeDifferentialForms f (((0 : ℕ) : ℤ) + ((e + 1 : ℕ) : ℤ)))) :
    ∃ a : A, y = ((Hfunctor (structureSheafRing X.toRingedSpace) ⊤ (0 + (e + 1))).map
      (globalSmul ((Stacks.Cech.globalRingHom f).hom a)
        (relativeDifferentialForms f (((0 : ℕ) : ℤ) + ((e + 1 : ℕ) : ℤ))))).hom
      (sectionGysinClass f σ (e + 1)) := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨ι, hfin, U, hUaff, hcov⟩ :=
    Stacks.AlgebraicGeometry.ModuleLimits.exists_finite_affineOpen_cover X
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ : LinearOrder ι := linearOrderOfSTO WellOrderingRel
  have hU : (⊤ : X.Opens) = ⨆ i, U i :=
    (eq_top_iff.2 fun x _ => by
      obtain ⟨a, ha⟩ := hcov x
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨a, ha⟩).symm
  have haff : ∀ (r : ℕ) (s : Fin (r + 1) → ι), IsAffineOpen (⨅ k, U (s k)) :=
    fun _ s => Stacks.Cech.inter_isAffineOpen f U hUaff s
  let φ := Stacks.Cech.hgroupIsoAlternatingCechModuleHomology f U hU haff
    (f.relativeDifferentialForms (((0 : ℕ) : ℤ) + ((e + 1 : ℕ) : ℤ))) (0 + (e + 1))
  have hmem := Stacks.Cech.span_sectionGysinClass_eq_top f e σ hσ U hU hUaff ▸
    Submodule.mem_top (x := (show ↑((Stacks.Cech.alternatingCechModuleComplex f U
      (f.relativeDifferentialForms (((0 : ℕ) : ℤ) + ((e + 1 : ℕ) : ℤ)))).homology (0 + (e + 1)))
        from φ.hom y))
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hmem
  exact ⟨a, (ConcreteCategory.bijective_of_isIso φ.hom).1 (ha.symm.trans
    (Stacks.Cech.hgroupIsoAlternatingCechModuleHomology_hom_globalSmul f U hU haff
      (f.relativeDifferentialForms (((0 : ℕ) : ℤ) + ((e + 1 : ℕ) : ℤ))) a (0 + (e + 1))
      (sectionGysinClass f σ (e + 1))).symm)⟩

/-- **The Gysin class of a section generates the top cohomology of differential forms over the
base** ([Stacks, Tag 0G8J], the claim that `ξ` is a basis element): every class of
`H^{e+1}(X, Ω^{e+1}_{X/A})`, read in the `Γ(Spec A, 𝒪)`-module `H^{e+1}(RΓ_A(X, Ω^{e+1}_{X/A}))`
through `hgroupSectionsOverBaseIso`, is a multiple of `sectionClassNormalized`. -/
theorem sectionClassNormalized_generates [IsNoetherianRing A] [IsProper f] [IsIso f.appTop]
    (hσ : σ ≫ f = 𝟙 _)
    (x : Hgroup (structureSheafRing X.toRingedSpace) ⊤ (e + 1)
      (relativeDifferentialForms f ((e + 1 : ℕ) : ℤ))) :
    ∃ r : baseRing (Spec (.of A)).toRingedSpace,
      (show (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (Spec (.of A)).toRingedSpace))
          ((e + 1 : ℕ) : ℤ)).obj ((Stacks.Cohomology.GlobalKunneth.sectionsOverBase
            f.toLRSHom.toShHom).obj ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ((0 : ℕ) : ℤ)).obj
                (relativeDifferentialForms f ((e + 1 : ℕ) : ℤ)))) from
        (hgroupSectionsOverBaseIso f.toLRSHom.toShHom
          (relativeDifferentialForms f ((e + 1 : ℕ) : ℤ)) 0 (e + 1) (e + 1) (by simp)).hom x) =
      r • (show (DerivedCategory.homologyFunctor
          (ModuleCat.{u} (baseRing (Spec (.of A)).toRingedSpace)) ((e + 1 : ℕ) : ℤ)).obj
            ((Stacks.Cohomology.GlobalKunneth.sectionsOverBase f.toLRSHom.toShHom).obj
              ((DerivedCategory.singleFunctor
                (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ((0 : ℕ) : ℤ)).obj
                  (relativeDifferentialForms f ((e + 1 : ℕ) : ℤ)))) from
        (hgroupSectionsOverBaseIso f.toLRSHom.toShHom
          (relativeDifferentialForms f ((e + 1 : ℕ) : ℤ)) 0 (e + 1) (e + 1) (by simp)).hom
            (sectionClassNormalized f e σ)) := by
  obtain ⟨a, rfl⟩ := exists_eq_globalSmul_classTransport (relativeDifferentialForms f)
    (show ((0 : ℕ) : ℤ) + ((e + 1 : ℕ) : ℤ) = ((e + 1 : ℕ) : ℤ) by push_cast; ring)
    (Nat.zero_add (e + 1)) (Stacks.Cech.globalRingHom f).hom (sectionGysinClass f σ (e + 1))
    (exists_eq_globalSmul_sectionGysinClass f e σ hσ) x
  exact ⟨(toSpecΓ (CommRingCat.of A)).hom a, hgroupSectionsOverBaseIso_globalSmul f
    (relativeDifferentialForms f ((e + 1 : ℕ) : ℤ)) (e + 1) ((toSpecΓ (CommRingCat.of A)).hom a)
      (sectionClassNormalized f e σ)⟩

end TopClass

end Stacks.WeilDeRham
