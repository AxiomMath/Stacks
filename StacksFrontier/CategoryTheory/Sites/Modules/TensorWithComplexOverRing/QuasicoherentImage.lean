module

public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexQuasicoherentAdjoint
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexOverRing.SignTwist

/-!
# The image of the derived tensor product over the base ring lies in `D_QCoh`

Let `(C, O)` be a ringed site, let `R` be a commutative ring with a sheaf of commutative
`R`-algebra structures on `O`, let `K` be a complex of `O`-modules whose cohomology sheaves are
quasi-coherent and let `(E, d) = Hom_{Comp^dg(O)}(K, K)` be its endomorphism differential graded
`R`-algebra. Then `- ⊗_E^𝐋 K : D(E, d) ⥤ D(O)`, formed over `R`, has image in `D_QCoh(O)`
(Tag 09M3 for a scheme). The argument is the dévissage of
`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexQuasicoherentAdjoint`, which carries it
out for the base ring `ℤ`; nothing in it depends on the base ring.

## Main results

* `RingedSite.derivedCategoryB_tensorWithComplexDerived_obj_of_hqcsumOver`
* `RingedSite.derivedCategoryB_isQuasicoherent_tensorWithComplexDerived_obj_schemeOver`

## References

* [Stacks Project, Tag 09M3](https://stacks.math.columbia.edu/tag/09M3)
* [Stacks Project, Tag 0FQE](https://stacks.math.columbia.edu/tag/0FQE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open DifferentialGradedModule

namespace AlgebraicGeometry.RingedSite

universe u v w t s o

attribute [local instance] HasDerivedCategory.standard

section General

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})
  (R : Type o) [CommRing R] [Linear R (TensorModO.{u, v, w, t, s} X)]
  [ScalarSections.{u, v, w, t, s, o} X R]
  (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)

section Admissible

attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

/-- The image in `D(O)` of a cone triangle of `K(Mod_(E, d))` is distinguished once its third
arrow is negated. -/
theorem tensorWithComplexToDerivedCategory_negMor₃_distinguishedOver
    (T : Triangle (DifferentialGradedModule.HomotopyCategory.{o, max u v w t s, max u v w t s}
      (Rep.{u, v, w, t, s, o} X R K).algebra))
    (hT : T ∈ distinguishedConeTriangles.{o, max u v w t s, max u v w t s}
      (A := (Rep.{u, v, w, t, s, o} X R K).algebra)) :
    (tensorWithComplexToDerivedCategory.{u, v, w, t, s, o} X R K).mapTriangle.obj
        (Triangle.mk T.mor₁ T.mor₂ (-T.mor₃)) ∈
      distTriang (DerivedCategory (TensorModO.{u, v, w, t, s} X)) := by
  have := tensorWithComplexHomotopy_isTriangulated.{u, v, w, t, s, o} X R K
  have : (tensorWithComplexToDerivedCategory.{u, v, w, t, s, o} X R K).IsTriangulated :=
    show (tensorWithComplexHomotopy.{u, v, w, t, s, o} X R K ⋙
      DerivedCategory.Qh (C := TensorModO.{u, v, w, t, s} X)).IsTriangulated from inferInstance
  refine (tensorWithComplexToDerivedCategory.{u, v, w, t, s, o} X R K).map_distinguished _ ?_
  rw [distinguishedTriangles_eq]
  exact (mem_distinguishedConeTriangles_iff_isDistinguishedTriangle_negMor₃ T).1 hT


end Admissible

section Cone

attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory


/-- **Stacks 09MA at the regular module.** Let `K` be a complex of `O`-modules whose cohomology
sheaves are quasi-coherent. Then `- ⊗_E^𝐋 K` sends the free rank-one differential graded
`E`-module to an object of `D_QCoh(O)`, namely to `K` itself. -/
theorem derivedCategoryB_tensorWithComplexDerived_obj_regularOver
    (hK : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K))) :
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      ((tensorWithComplexDerived.{u, v, w, t, s, o} X R K).obj
        ((quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q.obj
          ((toHomotopyCategory (Rep.{u, v, w, t, s, o} X R K).algebra).obj
            ((Rep.{u, v, w, t, s, o} X R K).functor.obj
              (liftComplex.{u, v, w, t, s} X K))))) := fun n =>
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    (((DerivedCategory.homologyFunctor (TensorModO.{u, v, w, t, s} X) n).mapIso
      (tensorWithComplexDerivedObjRegularIsoOver.{u, v, w, t, s, o} X R K)).symm) (hK n)

/-! ### Cone triangles with left-orthogonal vertices -/

/-- Every distinguished triangle of `D(E, d)` is isomorphic to the image of a cone triangle of
`K(Mod_(E, d))` whose three vertices are orthogonal on the left to the acyclic modules: its first
arrow comes from an arrow between such objects, and a cone leaves the third vertex of that kind. -/
theorem exists_coneTriangle_leftOrthogonal_isoOver
    (Δ : Triangle (DifferentialGradedModule.derivedCategory.{o, max u v w t s, max u v w t s}
      (Rep.{u, v, w, t, s, o} X R K).algebra))
    (hΔ : Δ ∈ distTriang (DifferentialGradedModule.derivedCategory.{o, max u v w t s,
      max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra)) :
    ∃ T : Triangle (DifferentialGradedModule.HomotopyCategory.{o, max u v w t s, max u v w t s}
        (Rep.{u, v, w, t, s, o} X R K).algebra),
      T ∈ distinguishedConeTriangles.{o, max u v w t s, max u v w t s}
          (A := (Rep.{u, v, w, t, s, o} X R K).algebra) ∧
      (acyclic (Rep.{u, v, w, t, s, o} X R K).algebra).leftOrthogonal T.obj₁ ∧
      (acyclic (Rep.{u, v, w, t, s, o} X R K).algebra).leftOrthogonal T.obj₂ ∧
      (acyclic (Rep.{u, v, w, t, s, o} X R K).algebra).leftOrthogonal T.obj₃ ∧
      Nonempty (Δ ≅
        (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q.mapTriangle.obj T) := by
  have hres : (LeftDerivedByResolutions.inclusionLocalizerMorphism
      (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra)
      (acyclic (Rep.{u, v, w, t, s, o} X R K).algebra).leftOrthogonal).HasLeftResolutions :=
    fun Y => by
      obtain ⟨P, hP, f, hf⟩ :=
        exists_quasiIso_leftOrthogonal_acyclic_repOver.{u, v, w, t, s, o} X R K Y
      exact ⟨{ X₁ := ⟨P, hP⟩, w := f, hw := hf }⟩
  have := LeftDerivedByResolutions.isLocalizedEquivalence_inclusionLocalizerMorphism
    (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra)
    (acyclic (Rep.{u, v, w, t, s, o} X R K).algebra).leftOrthogonal
  have := LeftDerivedByResolutions.hasRightCalculusOfFractions_inverseImage_ι
    (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra)
    (acyclic (Rep.{u, v, w, t, s, o} X R K).algebra).leftOrthogonal
  have : ((acyclic (Rep.{u, v, w, t, s, o} X R K).algebra).leftOrthogonal.ι ⋙
      (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q).IsLocalization
      ((quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).inverseImage
        (acyclic (Rep.{u, v, w, t, s, o} X R K).algebra).leftOrthogonal.ι) :=
    LocalizerMorphism.IsLocalizedEquivalence.isLocalization
      (LeftDerivedByResolutions.inclusionLocalizerMorphism
        (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra)
        (acyclic (Rep.{u, v, w, t, s, o} X R K).algebra).leftOrthogonal)
      (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q
  have := Localization.essSurj_mapArrow_of_hasRightCalculusOfFractions
    ((acyclic (Rep.{u, v, w, t, s, o} X R K).algebra).leftOrthogonal.ι ⋙
      (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q)
    ((quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).inverseImage
      (acyclic (Rep.{u, v, w, t, s, o} X R K).algebra).leftOrthogonal.ι)
  obtain ⟨a, ⟨ea⟩⟩ := Functor.EssSurj.mem_essImage
    (F := ((acyclic (Rep.{u, v, w, t, s, o} X R K).algebra).leftOrthogonal.ι ⋙
      (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q).mapArrow) (Arrow.mk Δ.mor₁)
  obtain ⟨W, p, q, hT⟩ := distinguished_cocone_triangle
    ((acyclic (Rep.{u, v, w, t, s, o} X R K).algebra).leftOrthogonal.ι.map a.hom)
  refine ⟨Triangle.mk
      ((acyclic (Rep.{u, v, w, t, s, o} X R K).algebra).leftOrthogonal.ι.map a.hom) p q,
    hT, a.left.property, a.right.property,
    (acyclic (Rep.{u, v, w, t, s, o} X R K).algebra).leftOrthogonal.ext_of_isTriangulatedClosed₃
      _ hT a.left.property a.right.property, ⟨?_⟩⟩
  exact (isoTriangleOfIso₁₂ _ _
    ((quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q.map_distinguished _ hT) hΔ
    (Arrow.leftFunc.mapIso ea) (Arrow.rightFunc.mapIso ea) ea.hom.w.symm).symm

/-! ### The image of the derived tensor product -/

/-- **The image of `- ⊗_E^𝐋 K` lies in `D_QCoh(O)`** when the cohomology sheaves of `K` are
quasi-coherent, quasi-coherence is a weak Serre class and `hqcsum`, a direct sum of
quasi-coherent `O`-modules is quasi-coherent. -/
theorem derivedCategoryB_tensorWithComplexDerived_obj_of_hqcsumOver
    [ObjectProperty.IsWeakSerreClass (tensorModOQuasicoherent.{u, v, w, t, s} X)]
    (hqcsum : ∀ {ι : Type (max u v w t s)} (Mf : ι → TensorModO.{u, v, w, t, s} X)
      (c : Cofan Mf), IsColimit c →
      (∀ i, tensorModOQuasicoherent.{u, v, w, t, s} X (Mf i)) →
      tensorModOQuasicoherent.{u, v, w, t, s} X c.pt)
    (hK : tensorModOQuasicoherentDerived.{u, v, w, t, s} X
      (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K)))
    (M : DifferentialGradedModule.derivedCategory.{o, max u v w t s, max u v w t s}
      (Rep.{u, v, w, t, s, o} X R K).algebra) :
    tensorModOQuasicoherentDerived.{u, v, w, t, s} X
      ((tensorWithComplexDerived.{u, v, w, t, s, o} X R K).obj M) := by
  classical
  let _hgr : IsGrothendieckAbelian.{max u v w t s} (TensorModO.{u, v, w, t, s} X) :=
    Stacks.SheafOfModules.sheafModulesGrothendieck.{u, v, w, max t s} X.J
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  have hqc : WeakSerre.IsWeakSerre (tensorModOQuasicoherent.{u, v, w, t, s} X) :=
    WeakSerre.isWeakSerre_of_isWeakSerreClass _
  have hcl := DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms
    (tensorModOQuasicoherent.{u, v, w, t, s} X) hqc
  have hqcsum' : ∀ {ι : Type (max u v w t s)} (Mf : ι → TensorModO.{u, v, w, t, s} X),
      (∀ i, tensorModOQuasicoherent.{u, v, w, t, s} X (Mf i)) →
      tensorModOQuasicoherent.{u, v, w, t, s} X (∐ Mf) := fun Mf hMf =>
    hqcsum Mf _ (coproductIsCoproduct Mf) hMf
  refine General.property_of_coproducts_of_two_out_of_three_of_shifts
    (Rep.{u, v, w, t, s, o} X R K).algebra
    (fun N => tensorModOQuasicoherentDerived.{u, v, w, t, s} X
      ((tensorWithComplexDerived.{u, v, w, t, s, o} X R K).obj N)) ?_ ?_ ?_ M
  · intro ι Mfam hMfam
    let _ := Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory
      (TensorModO.{u, v, w, t, s} X) ι
    refine hcl.of_iso
      (PreservesCoproduct.iso (tensorWithComplexDerived.{u, v, w, t, s, o} X R K) Mfam).symm ?_
    exact Stacks.Duality.derivedCategoryB_prop_coproduct (TensorModO.{u, v, w, t, s} X)
      (tensorModOQuasicoherent.{u, v, w, t, s} X) hqc hqcsum' _ hMfam
  · intro Δ hΔ
    obtain ⟨T, hT, hO₁, hO₂, hO₃, ⟨e'⟩⟩ :=
      exists_coneTriangle_leftOrthogonal_isoOver.{u, v, w, t, s, o} X R K Δ hΔ
    have hmap :=
      tensorWithComplexToDerivedCategory_negMor₃_distinguishedOver.{u, v, w, t, s, o} X R K T hT
    have htri := DerivedCategoryB.derivedCategoryB_isTriangulated
      (tensorModOQuasicoherent.{u, v, w, t, s} X) hqc
    have e : ∀ {A : DifferentialGradedModule.derivedCategory.{o, max u v w t s, max u v w t s}
        (Rep.{u, v, w, t, s, o} X R K).algebra}
        {B : DifferentialGradedModule.HomotopyCategory.{o, max u v w t s, max u v w t s}
          (Rep.{u, v, w, t, s, o} X R K).algebra},
        (A ≅ (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q.obj B) →
        (acyclic (Rep.{u, v, w, t, s, o} X R K).algebra).leftOrthogonal B →
        ((tensorWithComplexDerived.{u, v, w, t, s, o} X R K).obj A ≅
          (tensorWithComplexToDerivedCategory.{u, v, w, t, s, o} X R K).obj B) :=
      fun i hB => (tensorWithComplexDerived.{u, v, w, t, s, o} X R K).mapIso i ≪≫
        @asIso _ _ _ _ ((tensorWithComplexDerivedCounit.{u, v, w, t, s, o} X R K).app _)
          (isIso_tensorWithComplexDerivedCounit_appOver.{u, v, w, t, s, o} X R K _ hB)
    have e₁ := e (Triangle.π₁.mapIso e') hO₁
    have e₂ := e (Triangle.π₂.mapIso e') hO₂
    have e₃ := e (Triangle.π₃.mapIso e') hO₃
    refine ⟨fun h₁ h₂ => ?_, fun h₁ h₃ => ?_, fun h₂ h₃ => ?_⟩
    · exact hcl.of_iso e₃.symm
        ((tensorModOQuasicoherentDerived.{u, v, w, t, s} X).ext_of_isTriangulatedClosed₃
          _ hmap (hcl.of_iso e₁ h₁) (hcl.of_iso e₂ h₂))
    · exact hcl.of_iso e₂.symm
        ((tensorModOQuasicoherentDerived.{u, v, w, t, s} X).ext_of_isTriangulatedClosed₂
          _ hmap (hcl.of_iso e₁ h₁) (hcl.of_iso e₃ h₃))
    · exact hcl.of_iso e₁.symm
        ((tensorModOQuasicoherentDerived.{u, v, w, t, s} X).ext_of_isTriangulatedClosed₁
          _ hmap (hcl.of_iso e₂ h₂) (hcl.of_iso e₃ h₃))
  · intro k
    have hreg :=
      derivedCategoryB_tensorWithComplexDerived_obj_regularOver.{u, v, w, t, s, o} X R K hK
    have h0 : tensorModOQuasicoherentDerived.{u, v, w, t, s} X
        ((tensorWithComplexDerived.{u, v, w, t, s, o} X R K).obj
          ((toHomotopyCategory (Rep.{u, v, w, t, s, o} X R K).algebra ⋙
            (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q).obj
              (regularModule (Rep.{u, v, w, t, s, o} X R K).algebra))) :=
      hcl.of_iso
        ((tensorWithComplexDerived.{u, v, w, t, s, o} X R K).mapIso
          ((toHomotopyCategory (Rep.{u, v, w, t, s, o} X R K).algebra ⋙
            (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q).mapIso
              DGCategory.representableSelfIsoRegular)) hreg
    exact hcl.of_iso
      (((tensorWithComplexDerived.{u, v, w, t, s, o} X R K).commShiftIso k).app _).symm
      (DerivedCategoryB.derivedCategoryB_shift_mem
        (tensorModOQuasicoherent.{u, v, w, t, s} X) hqc k h0)


end Cone

end General

/-! ### A scheme -/

section Scheme

attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory

/-- The standard model of the derived category of the ambient modules on the site of opens of a
scheme. -/
local instance hasDerivedCategorySchemeRingedSiteOver (Y : Scheme.{u}) :
    HasDerivedCategory.{u + 1, u, u + 1} (TensorModO.{u, u, u, u, u}
      (Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite Y)) :=
  HasDerivedCategory.standard _

variable (Y : Scheme.{u}) (R : Type o) [CommRing R]
  [Linear R (TensorModO.{u, u, u, u, u}
    (Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite Y))]
  [ScalarSections.{u, u, u, u, u, o}
    (Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite Y) R]

/-- **Tag 09M3 over the base ring `R`.** For a scheme `Y` and a complex `K` of `O_Y`-modules with
quasi-coherent cohomology sheaves, every object `M ⊗_E^𝐋 K` has quasi-coherent cohomology
sheaves, `E = Hom(K, K)` being read as a differential graded `R`-algebra. -/
theorem derivedCategoryB_isQuasicoherent_tensorWithComplexDerived_obj_schemeOver
    (K : CochainComplex (ModO.{u, u, u, u}
      (Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite Y)) ℤ)
    (hK : tensorModOQuasicoherentDerived.{u, u, u, u, u}
      (Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite Y)
      (DerivedCategory.Q.obj (liftComplex.{u, u, u, u, u}
        (Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite Y) K)))
    (M : DifferentialGradedModule.derivedCategory.{o, u, u}
      (Rep.{u, u, u, u, u, o}
        (Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite Y) R K).algebra) :
    DerivedCategoryB.derivedCategoryB
        (A := TensorModO.{u, u, u, u, u}
          (Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite Y))
        (SheafOfModules.isQuasicoherent Y.ringCatSheaf)
      ((tensorWithComplexDerived.{u, u, u, u, u, o}
        (Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite Y) R K).obj M) := by
  have h := derivedCategoryB_tensorWithComplexDerived_obj_of_hqcsumOver.{u, u, u, u, u, o} _ R K
    (fun Mf c hc hMf => tensorModOQuasicoherent_schemeRingedSite_colimit Y Mf c hc hMf) hK M
  rwa [tensorModOQuasicoherentDerived, tensorModOQuasicoherent_schemeRingedSite_eq Y] at h

end Scheme

end AlgebraicGeometry.RingedSite

end
