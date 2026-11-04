module

public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexQuasicoherentAdjoint
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.SupportedDirectSums

/-!
# The image of the derived tensor product lies in every localizing subcategory containing `K`

Let `(C, O)` be a ringed site, let `K` be a complex of `O`-modules and let
`(E, d) = Hom_{Comp^dg(O)}(K, K)` be its endomorphism differential graded algebra. The derived
tensor product `- ⊗_E^𝐋 K : D(E, d) ⥤ D(O)` sends every object into any strictly full
triangulated subcategory of `D(O)` which is closed under direct sums and contains `K`.

## Main results

* `AlgebraicGeometry.RingedSite.tensorWithComplexDerived_obj_mem_of_isTriangulated`: the image of
  `- ⊗_E^𝐋 K` lies in every strictly full triangulated subcategory of `D(O)` closed under direct
  sums and containing `K`.
* `AlgebraicGeometry.RingedSite.tensorWithComplexDerived_obj_quasiCoherentSupported_scheme`: on a
  scheme, if the cohomology sheaves of `K` are quasi-coherent and supported on `T`, then so are
  those of `M ⊗_E^𝐋 K` for every `M`.

## References

* [Stacks Project, Tag 09M3](https://stacks.math.columbia.edu/tag/09M3)
* [Stacks Project, Tag 0DJL](https://stacks.math.columbia.edu/tag/0DJL)
* [Stacks Project, Tag 0FQE](https://stacks.math.columbia.edu/tag/0FQE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open DifferentialGradedModule

namespace AlgebraicGeometry.RingedSite

universe u v w t s

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})
  (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)

attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory

/-- **The image of `- ⊗_E^𝐋 K` lies in every localizing subcategory containing `K`.** Let `P` be
a strictly full triangulated subcategory of `D(O)` closed under direct sums indexed by the universe
of the ambient modules, and containing `K`. Then `M ⊗_E^𝐋 K` lies in `P` for every object `M` of
`D(E, d)`. The derived category of `O`-modules is the standard model
`CategoryTheory.HasDerivedCategory.standard`. -/
theorem tensorWithComplexDerived_obj_mem_of_isTriangulated
    (P : ObjectProperty (@DerivedCategory (TensorModO.{u, v, w, t, s} X) _ _
      (HasDerivedCategory.standard _)))
    [P.IsClosedUnderIsomorphisms] [P.IsTriangulated]
    (hsum : ∀ ι : Type (max u v w t s), P.IsClosedUnderColimitsOfShape (Discrete ι))
    (hK : P ((@DerivedCategory.Q (TensorModO.{u, v, w, t, s} X) _ _
      (HasDerivedCategory.standard _)).obj (liftComplex.{u, v, w, t, s} X K)))
    (M : DifferentialGradedModule.derivedCategory.{0, max u v w t s, max u v w t s}
      (Rep.{u, v, w, t, s, 0} X ℤ K).algebra) :
    P ((tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).obj M) := by
  classical
  let : HasDerivedCategory (TensorModO.{u, v, w, t, s} X) := HasDerivedCategory.standard _
  let _hgr : IsGrothendieckAbelian.{max u v w t s} (TensorModO.{u, v, w, t, s} X) :=
    Stacks.SheafOfModules.sheafModulesGrothendieck.{u, v, w, max t s} X.J
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  refine General.property_of_coproducts_of_two_out_of_three_of_shifts
    (Rep.{u, v, w, t, s, 0} X ℤ K).algebra
    (fun N => P ((tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).obj N)) ?_ ?_ ?_ M
  · intro ι Mfam hMfam
    let _ := Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory
      (TensorModO.{u, v, w, t, s} X) ι
    have := hsum ι
    refine P.prop_of_iso
      (PreservesCoproduct.iso (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K) Mfam).symm ?_
    exact P.prop_colimit _ fun j => hMfam j.as
  · intro Δ hΔ
    obtain ⟨T, hT, hO₁, hO₂, hO₃, ⟨e⟩⟩ :=
      exists_coneTriangle_leftOrthogonal_iso.{u, v, w, t, s} X K Δ hΔ
    have hmap := tensorWithComplexToDerivedCategory_negMor₃_distinguished.{u, v, w, t, s} X K T hT
    have key : ∀ {A : DifferentialGradedModule.derivedCategory.{0, max u v w t s, max u v w t s}
          (Rep.{u, v, w, t, s, 0} X ℤ K).algebra}
        {B : DifferentialGradedModule.HomotopyCategory.{0, max u v w t s, max u v w t s}
          (Rep.{u, v, w, t, s, 0} X ℤ K).algebra}
        (e : A ≅ (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q.obj B),
        (acyclic (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).leftOrthogonal B →
        ((tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).obj A ≅
          (tensorWithComplexToDerivedCategory.{u, v, w, t, s, 0} X ℤ K).obj B) :=
      fun e hO =>
        have := isIso_tensorWithComplexDerivedCounit_app.{u, v, w, t, s} X K _ hO
        (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).mapIso e ≪≫
          asIso ((tensorWithComplexDerivedCounit.{u, v, w, t, s, 0} X ℤ K).app _)
    have e₁ := key (Triangle.π₁.mapIso e) hO₁
    have e₂ := key (Triangle.π₂.mapIso e) hO₂
    have e₃ := key (Triangle.π₃.mapIso e) hO₃
    refine ⟨fun h₁ h₂ => ?_, fun h₁ h₃ => ?_, fun h₂ h₃ => ?_⟩
    · exact P.prop_of_iso e₃.symm
        (P.ext_of_isTriangulatedClosed₃ _ hmap (P.prop_of_iso e₁ h₁) (P.prop_of_iso e₂ h₂))
    · exact P.prop_of_iso e₂.symm
        (P.ext_of_isTriangulatedClosed₂ _ hmap (P.prop_of_iso e₁ h₁) (P.prop_of_iso e₃ h₃))
    · exact P.prop_of_iso e₁.symm
        (P.ext_of_isTriangulatedClosed₁ _ hmap (P.prop_of_iso e₂ h₂) (P.prop_of_iso e₃ h₃))
  · intro k
    have h0 : P ((tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).obj
        ((toHomotopyCategory (Rep.{u, v, w, t, s, 0} X ℤ K).algebra ⋙
          (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q).obj
            (regularModule (Rep.{u, v, w, t, s, 0} X ℤ K).algebra))) :=
      P.prop_of_iso
        (((tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).mapIso
          ((toHomotopyCategory (Rep.{u, v, w, t, s, 0} X ℤ K).algebra ⋙
            (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q).mapIso
              DGCategory.representableSelfIsoRegular)).symm ≪≫
          tensorWithComplexDerivedObjRegularIso.{u, v, w, t, s} X K).symm hK
    exact P.prop_of_iso
      (((tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).commShiftIso k).app _).symm
      (P.le_shift k _ h0)


/-! ### Complexes with quasi-coherent cohomology supported on a closed subset -/

/-- The standard model of the derived category of `𝒪_Y`-modules on the site of opens of a scheme,
the one on which `- ⊗_E^𝐋 K` is defined. -/
abbrev schemeStandardDerivedCategory (Y : Scheme.{u}) :
    HasDerivedCategory.{u + 1} (SheafOfModules.{u} Y.ringCatSheaf) :=
  HasDerivedCategory.standard _

/-- Let `Y` be a scheme, read as the ringed site of its
opens, let `T ⊆ Y` be a subset and let `K` be a complex of `𝒪_Y`-modules whose cohomology sheaves
are quasi-coherent and supported on `T`. Then for every object `M` of `D(E, d)`, where
`(E, d) = Hom(K, K)`, the cohomology sheaves of `M ⊗_E^𝐋 K` are quasi-coherent and supported on
`T`: the functor `- ⊗_E^𝐋 K` takes values in `D_{QCoh,T}(𝒪_Y)`. The derived category of
`𝒪_Y`-modules is the standard model `schemeStandardDerivedCategory Y`. -/
theorem tensorWithComplexDerived_obj_quasiCoherentSupported_scheme (Y : Scheme.{u}) (T : Set Y)
    (K : CochainComplex (ModO.{u, u, u, u}
      (Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite Y)) ℤ)
    (hK : @Stacks.Duality.quasiCoherentSupported Y T (schemeStandardDerivedCategory Y)
      ((@DerivedCategory.Q _ _ _ (schemeStandardDerivedCategory Y)).obj
        (liftComplex.{u, u, u, u, u}
          (Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite Y) K)))
    (M : DifferentialGradedModule.derivedCategory.{0, u, u}
      (Rep.{u, u, u, u, u, 0}
        (Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite Y) ℤ K).algebra) :
    @Stacks.Duality.quasiCoherentSupported Y T (schemeStandardDerivedCategory Y)
      ((tensorWithComplexDerived.{u, u, u, u, u, 0}
        (Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite Y) ℤ K).obj M) := by
  let := schemeStandardDerivedCategory Y
  exact @tensorWithComplexDerived_obj_mem_of_isTriangulated.{u, u, u, u, u} _ K
    (Stacks.Duality.quasiCoherentSupported Y T)
    (Stacks.Duality.Supported.quasiCoherentSupported_isClosedUnderIsomorphisms Y T)
    (Stacks.Duality.Supported.quasiCoherentSupported_isTriangulated Y T)
    (fun ι => Stacks.Duality.Supported.quasiCoherentSupported_isClosedUnderCoproducts Y T ι) hK M

end AlgebraicGeometry.RingedSite

end
