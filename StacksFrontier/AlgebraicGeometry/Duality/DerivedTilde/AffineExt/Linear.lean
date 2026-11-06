module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineExt.Ext

/-!
# Linearity of the comparison of the `Ext` presheaf with the cohomology sheaf

Over a principal open `D(f)` of `Spec R`, the group `Ext^n_{R_f}(K ⊗_R R_f, L ⊗_R R_f)` is an
`R_f`-module, the morphisms of the derived category of `R_f`-modules being `R_f`-linear, and the
sections over `D(f)` of the cohomology sheaf `Hⁿ(R𝓗om(K̃, L̃))` form an `R_f`-module, since
`R_f = Γ(Spec R, D(f))`. The comparison map between them is `R_f`-linear.

## Main definitions

* `AlgebraicGeometry.AffineExt.sectionsSmul`: multiplication by a section of the ring, as an
  endomorphism of the functor of sections over an object.
* `AlgebraicGeometry.AffineExt.extToCohomologySheafLinear`: the comparison map as an `R_f`-linear
  map.

## Main results

* `AlgebraicGeometry.AffineExt.extToCohomologySheaf_smul`: the comparison map is `R_f`-linear.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CochainComplex.HomComplex

universe u

namespace CochainComplex.HomComplex

variable {S : Type*} [Ring S] {C : Type*} [Category C] [Abelian C] [Linear S C]
  [HasDerivedCategory C]

/-- The identification of the cohomology classes of the Hom complex into a K-injective complex
with morphisms in the derived category is linear. -/
lemma cohomologyClassAddEquivShiftedHom_mk_smul (A J : CochainComplex C ℤ) [J.IsKInjective]
    (n : ℤ) (s : S) (z : Cocycle A J n) :
    cohomologyClassAddEquivShiftedHom A J n (CohomologyClass.mk (s • z)) =
      s • cohomologyClassAddEquivShiftedHom A J n (CohomologyClass.mk z) := by
  rw [cohomologyClassAddEquivShiftedHom_mk, cohomologyClassAddEquivShiftedHom_mk,
    Cocycle.equivHomShift_symm_smul, Functor.map_smul, Linear.smul_comp]

end CochainComplex.HomComplex

namespace AlgebraicGeometry.AffineExt

section Sections

variable {C : Type u} [SmallCategory C] {R : Cᵒᵖ ⥤ RingCat.{u}}

/-- Multiplication by a section `r` of the ring over `U`, as an endomorphism of the functor of
sections over `U`. -/
def sectionsSmul (U : Cᵒᵖ) (r : R.obj U) :
    (PresheafOfModules.toPresheaf R ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj U) ⟶
      (PresheafOfModules.toPresheaf R ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj U) where
  app M := AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom (M.obj U) r)
  naturality M N φ := by
    ext x
    exact ((φ.app U).hom.map_smul r x).symm

/-- The component of `sectionsSmul U r` at a presheaf of modules `M` sends a section `x` over `U`
to `r • x`. -/
lemma sectionsSmul_app_apply (U : Cᵒᵖ) (r : R.obj U) (M : PresheafOfModules.{u} R)
    (x : M.obj U) : (sectionsSmul U r).app M x = r • x :=
  rfl

end Sections

section Homology

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

variable (K : CochainComplex (SheafOfModules.{u} R) ℤ) (n : ℤ)

/-- Multiplication by `r` on the complex of sections over `U`. -/
abbrev sectionsComplexSmul (U : Cᵒᵖ) (r : R.obj.obj U) :
    sectionsComplex K U ⟶ sectionsComplex K U :=
  (NatTrans.mapHomologicalComplex (sectionsSmul U r) (ComplexShape.up ℤ)).app
    (((SheafOfModules.forget R).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The identification of the cohomology of sections with the sections of the cohomology
presheaf commutes with multiplication by sections of the ring. -/
lemma sectionsHomologyIso_smul (U : Cᵒᵖ) (r : R.obj.obj U) :
    HomologicalComplex.homologyMap (sectionsComplexSmul K U r) n ≫
        (sectionsHomologyIso K n U).hom =
      (sectionsHomologyIso K n U).hom ≫ (sectionsSmul U r).app (homologyPresheaf K n) := by
  have h := NatTrans.app_homology (sectionsSmul U r)
    ((((SheafOfModules.forget R).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).sc n)
  refine Eq.trans ?_ (congrArg ((sectionsHomologyIso K n U).hom ≫ ·) h.symm)
  exact (Iso.hom_inv_id_assoc _ _).symm

end Homology

attribute [local instance 10000] HasDerivedCategory.standard

variable (R : CommRingCat.{u}) (K L : DerivedCategory (ModuleCat.{u} R)) (n : ℤ)

/-- An element of `R_f = Γ(Spec R, D(f))`, read as a section over `D(f)` of the structure sheaf
of the ringed site of `Spec R`. -/
abbrev ringSec (f : R) (s : locRing R f) :
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (Stacks.SheafOfModules.ringedSite (Spec R).sheaf).O).obj.obj (op (basicOpen R f)) :=
  s

/-- Multiplication by `s ∈ R_f` on the complex of sections over `D(f)` of the internal Hom
complex. -/
abbrev secSmul (f : R) (s : locRing R f) : secC R K L f ⟶ secC R K L f :=
  sectionsComplexSmul (homModel R K L).obj (op (basicOpen R f)) (ringSec R f s)

/-- **The local identification of the internal Hom complex is linear.** Over `D(f)`, the
identification of sections of the internal Hom complex with the Hom complex of `R_f`-modules
carries multiplication by `s ∈ R_f` to multiplication by `s`. -/
lemma sectionComplexIsoS_hom_f_smul (f : R) (p q : ℤ) (hpq : p + n = q) (s : locRing R f)
    (x : ((homModel R K L).obj.X n).val.obj (op (basicOpen R f))) :
    (((sectionComplexIsoS R K L f).hom.f n) (ringSec R f s • x)).v p q hpq =
      s • (((sectionComplexIsoS R K L f).hom.f n) x).v p q hpq := by
  rw [sectionComplexIsoS_hom_f_v, sectionComplexIsoS_hom_f_v]
  have hg : (((sectionComplexIso R K L (basicOpen R f)).hom.f n) (ringSec R f s • x)).v p q hpq =
      (((sectionComplexIso R K L (basicOpen R f)).hom.f n) x).v p q hpq ≫
        (ModuleCat.restrictScalars (locMap R f).hom).map
          (s • 𝟙 ((sectionsS R (basicOpen R f)).obj ((resolution R L).X q))) := by
    ext m
    refine (TildeSlice.tildeOverHomEquiv_apply (basicOpen R f) _ _ _ m).trans ?_
    refine ((homModel R K L).smul_natural (basicOpen R f) (ringSec R f s) n p q hpq x
      (𝟙 _) _).trans ?_
    have hid : (Stacks.SheafOfModules.Tensor.ringSheaf
        (Stacks.SheafOfModules.ringedSite (Spec R).sheaf).O).obj.map
        (𝟙 (basicOpen R f)).op (ringSec R f s) = ringSec R f s := by
      rw [op_id, CategoryTheory.Functor.map_id]
      rfl
    rw [hid]
    exact (congrArg (fun z : ((sectionsS R (basicOpen R f)).obj ((resolution R L).X q)) => s • z)
      (TildeSlice.tildeOverHomEquiv_apply (basicOpen R f) _ _ _ m).symm :)
  rw [hg]
  refine ((ModuleCat.extendRestrictScalarsAdj (locMap R f).hom).homEquiv_naturality_right_symm
    _ _).trans ?_
  exact (Linear.comp_smul _ _ _ _ _ _).trans (congrArg
    (fun g : (ModuleCat.extendScalars (locMap R f).hom).obj ((srcModel R K).X p) ⟶
      (sectionsS R (basicOpen R f)).obj ((resolution R L).X q) => s • g) (Category.comp_id _))

/-- **Multiplication by `s ∈ R_f` on cocycles.** -/
lemma cycleCocycle_secSmul (f : R) (s : locRing R f)
    (c : ((secC R K L f).cycles n : Type u)) :
    cycleCocycle _ _ n (HomologicalComplex.cyclesMap (sectionComplexIsoS R K L f).hom n
        (HomologicalComplex.cyclesMap (secSmul R K L f s) n c)) =
      s • cycleCocycle _ _ n
        (HomologicalComplex.cyclesMap (sectionComplexIsoS R K L f).hom n c) := by
  apply Cocycle.ext
  refine Cochain.ext _ _ fun p q hpq => ?_
  rw [Cocycle.coe_smul, Cochain.smul_v, cycleCocycle_coe, cycleCocycle_coe]
  have key : ∀ {A B : HomologicalComplex AddCommGrpCat.{u} (ComplexShape.up ℤ)} (φ : A ⟶ B)
      (z : (A.cycles n : Type u)),
      B.iCycles n (HomologicalComplex.cyclesMap φ n z) = φ.f n (A.iCycles n z) := fun φ z =>
    ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i φ n) z
  rw [key, key, key]
  exact sectionComplexIsoS_hom_f_smul R K L n f p q hpq s _

/-- **The value of the `Ext` presheaf is linear.** The identification of the cohomology of
sections over `D(f)` of the internal Hom complex with `Ext^n_{R_f}(K ⊗ R_f, L ⊗ R_f)` carries
multiplication by `s ∈ R_f` to multiplication by `s`. -/
lemma sectionHomologyEquiv_secSmul (f : R) (s : locRing R f)
    (y : ((secC R K L f).homology n : Type u)) :
    sectionHomologyEquiv R K L f n
        (HomologicalComplex.homologyMap (secSmul R K L f s) n y) =
      s • sectionHomologyEquiv R K L f n y := by
  have := isKInjective_sectionsS R f (resolution R L) (isKInjective_resolution R L)
  obtain ⟨c, rfl⟩ := (AddCommGrpCat.epi_iff_surjective ((secC R K L f).homologyπ n)).1
    inferInstance y
  have e := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality (secSmul R K L f s) n) c
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at e
  rw [e, sectionHomologyEquiv_homologyπ, sectionHomologyEquiv_homologyπ, cycleCocycle_secSmul,
    cohomologyClassAddEquivShiftedHom_mk_smul, Linear.smul_comp, Linear.comp_smul]

/-- **The comparison into the cohomology sheaf is linear on the cohomology of sections.** -/
lemma sectionsToCohomologySheaf_secSmul (f : R) (s : locRing R f)
    (y : ((secC R K L f).homology n : Type u)) :
    sectionsToCohomologySheaf R K L n f
        (HomologicalComplex.homologyMap (secSmul R K L f s) n y) =
      s • sectionsToCohomologySheaf R K L n f y := by
  have e : (sectionsHomologyIso (homModel R K L).obj n (op (basicOpen R f))).hom
      (HomologicalComplex.homologyMap (secSmul R K L f s) n y) =
      ringSec R f s • (sectionsHomologyIso (homModel R K L).obj n (op (basicOpen R f))).hom y :=
    ConcreteCategory.congr_hom
      (sectionsHomologyIso_smul (homModel R K L).obj n (op (basicOpen R f)) (ringSec R f s)) y
  refine (congrArg (fun z => ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
      (cohomologySheafIso R K L n).inv).app (op (basicOpen R f))
      (((PresheafOfModules.toPresheaf _).map (toHomologySheaf (homModel R K L).obj n)).app
        (op (basicOpen R f)) z)) e).trans ?_
  exact (congrArg _ (((toHomologySheaf (homModel R K L).obj n).app _).hom.map_smul _ _)).trans
    (((cohomologySheafIso R K L n).inv.val.app _).hom.map_smul _ _)

/-- **The comparison of the `Ext` presheaf with the cohomology sheaf is `R_f`-linear.** -/
theorem extToCohomologySheaf_smul (f : R) (s : locRing R f) (α : localizedExt R K L f n) :
    extToCohomologySheaf R K L n f (s • α) = s • extToCohomologySheaf R K L n f α := by
  obtain ⟨y, rfl⟩ := (sectionHomologyEquiv R K L f n).surjective α
  rw [← sectionHomologyEquiv_secSmul, extToCohomologySheaf_sectionHomologyEquiv,
    extToCohomologySheaf_sectionHomologyEquiv, sectionsToCohomologySheaf_secSmul]

/-- **The comparison of the `Ext` presheaf with the cohomology sheaf, as an `R_f`-linear map.**
Over `D(f)`, the `R_f`-linear map
`Ext^n_{R_f}(K ⊗_R R_f, L ⊗_R R_f) ⟶ Γ(D(f), Hⁿ(R𝓗om(K̃, L̃)))`. -/
def extToCohomologySheafLinear (f : R) :
    localizedExt R K L f n →ₗ[locRing R f] Γ(cohomologySheaf R K L n, basicOpen R f) where
  toFun := extToCohomologySheaf R K L n f
  map_add' := map_add _
  map_smul' := extToCohomologySheaf_smul R K L n f

/-- The linear map `extToCohomologySheafLinear` agrees with `extToCohomologySheaf`. -/
@[simp]
lemma extToCohomologySheafLinear_apply (f : R) (α : localizedExt R K L f n) :
    extToCohomologySheafLinear R K L n f α = extToCohomologySheaf R K L n f α :=
  rfl

end AlgebraicGeometry.AffineExt
