module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraSectionAction

/-!
# Surjectivity of the trace on the image of a map, after an étale restriction

Let `π : Y ⟶ X` be a morphism of algebraic spaces with direct-image algebra `𝒜 = π_*𝒪_Y`, let
`ℱ` be an `𝒪_X`-module and let `c : Res(Coext ℱ) ⟶ ℱ` be the counit of restriction and
coextension of scalars along `π♯ : 𝒪_X ⟶ 𝒜`.  Let `g : U ⟶ X` be étale and let
`ε : 𝒪_U ⟶ g^*𝒜` be a split global section.

Given an `𝒪_X`-linear map `ψ : 𝒫 ⟶ Res(Coext ℱ)`, the composite `g^*(ψ ≫ c)` is an epimorphism as
soon as multiplication by `ε(1)` kills every map out of `g^*Res(Coext ℱ)` killing `g^*ψ`.  The
second result discharges that condition in the situation of the proof of [Stacks, Tag 0GUZ]:
`Coext ℱ` is the direct image of an `𝒪_Y`-module `𝒢`, the map `ψ` has image in `π_*𝒢` whose
cokernel is the direct image of a quotient `𝒢 ⟶ 𝒬`, and `ε` is a section of `(π_*𝒦)|_U` for a
sheaf of ideals `𝒦` killing `𝒬`.

## Main results

* `AlgebraicGeometry.Space.epi_etaleModulePullback_map_comp_counit_of_split`: the first statement.
* `AlgebraicGeometry.Space.epi_etaleModulePullback_map_comp_counit_of_killed`: the second.

## References

* [Stacks Project, Tag 0GUZ](https://stacks.math.columbia.edu/tag/0GUZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y X U : AlgebraicSpaces B S hS} (π : Y ⟶ X) (g : U ⟶ X) (hg : IsEtale B S hS g.hom)
    (F : Modules.{u, u} B S hS X.1 X.2)

/-- **The trace is surjective on the image of `ψ`, after restriction to `U`**, as soon as the
section `ε(1)` of a split section `ε : 𝒪_U ⟶ (π_*𝒪_Y)|_U` acts by zero modulo the image of `ψ`. -/
theorem epi_etaleModulePullback_map_comp_counit_of_split {P : Modules.{u, u} B S hS X.1 X.2}
    (ψ : P ⟶ (directImageAlgebraRestrictScalars B S hS π).obj
      ((directImageAlgebraCoextendScalars B S hS π).obj F))
    (ε : SheafOfModules.unit (structureRingSheaf B S hS U) ⟶
      (etaleModulePullback B S hS g hg).obj (directImageAlgebraUnitModule B S hS π))
    (pr : (etaleModulePullback B S hS g hg).obj (directImageAlgebraUnitModule B S hS π) ⟶
      SheafOfModules.unit (structureRingSheaf B S hS U))
    (hε : ε ≫ pr = 𝟙 _)
    (hμ : ∀ ⦃Z : Modules.{u, u} B S hS U.1 U.2⦄
      (d : (etaleModulePullback B S hS g hg).obj ((directImageAlgebraRestrictScalars B S hS π).obj
        ((directImageAlgebraCoextendScalars B S hS π).obj F)) ⟶ Z),
      (etaleModulePullback B S hS g hg).map ψ ≫ d = 0 →
        etaleSectionAction B S hS π g hg ε ((directImageAlgebraCoextendScalars B S hS π).obj F) ≫
          d = 0) :
    Epi ((etaleModulePullback B S hS g hg).map
      (ψ ≫ (directImageAlgebraRestrictCoextendAdjunction B S hS π).counit.app F)) := by
  rw [Functor.map_comp]
  exact CategoryTheory.epi_comp_of_epi_comp_of_forall_comp_eq_zero _ _ _
    (epi_etaleSectionAction_comp_map_counit B S hS π g hg ε F pr hε) hμ

/-- **Multiplication by a section of `(π_*𝒦)|_U` kills every map factoring through the restriction
of `π_*𝒬`**, when `𝒦 · 𝒬 = 0`. -/
theorem etaleSectionAction_comp_eq_zero_of_factorsThrough {G Q : Modules.{u, u} B S hS Y.1 Y.2}
    (p : G ⟶ Q)
    (K : (SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).Submodule)
    (hK : ∀ (W : (smallEtaleRingedSite B S hS Y.1 Y.2).Cᵒᵖ)
      (r : (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj.obj W),
      r ∈ K.obj W → ∀ q : Q.val.obj W, r • q = 0)
    (εK : SheafOfModules.unit (structureRingSheaf B S hS U) ⟶
      (etaleModulePullback B S hS g hg).obj ((modulePushforward B S hS π).obj K.toSheafOfModules))
    (ε : SheafOfModules.unit (structureRingSheaf B S hS U) ⟶
      (etaleModulePullback B S hS g hg).obj (directImageAlgebraUnitModule B S hS π))
    (hfac : (εK ≫ (etaleModulePullback B S hS g hg).map ((modulePushforward B S hS π).map K.ι) :
          SheafOfModules.unit (structureRingSheaf B S hS U) ⟶
            (etaleModulePullback B S hS g hg).obj (pushforwardStructureModule B S hS π)) = ε)
    {Z : Modules.{u, u} B S hS U.1 U.2}
    (d'' : (etaleModulePullback B S hS g hg).obj ((directImageAlgebraRestrictScalars B S hS π).obj
      ((moduleDirectImage B S hS π).obj Q)) ⟶ Z) :
    etaleSectionAction B S hS π g hg ε ((moduleDirectImage B S hS π).obj G) ≫
      (etaleModulePullback B S hS g hg).map
        ((directImageAlgebraRestrictScalars B S hS π).map ((moduleDirectImage B S hS π).map p)) ≫
      d'' = 0 := by
  rw [← Category.assoc, ← etaleSectionAction_naturality, Category.assoc]
  subst hfac
  rw [etaleSectionAction_moduleDirectImage_eq_zero B S hS π g hg Q K hK εK, zero_comp, comp_zero]

/-- **The trace is surjective on the image of `ψ₀`, after restriction to `U`, when the cokernel
of `ψ₀` is killed by a section of `(π_*𝒦)|_U` splitting `(π_*𝒪_Y)|_U`.**

Here `Coext ℱ ≅ π_*𝒢` over `𝒜`, the map `ψ₀ : 𝒫 ⟶ π_*𝒢` has the property that every map out of
`g^*π_*𝒢` killing `g^*ψ₀` factors through `g^*π_*(p)` for a quotient `p : 𝒢 ⟶ 𝒬`, and the split
section `ε` of `(π_*𝒪_Y)|_U` factors through `(π_*𝒦)|_U` for a sheaf of ideals `𝒦` with
`𝒦 · 𝒬 = 0`.  This is the per-neighbourhood step of the proof of [Stacks, Tag 0GUZ]. -/
theorem epi_etaleModulePullback_map_comp_counit_of_killed {G Q : Modules.{u, u} B S hS Y.1 Y.2}
    (e : (directImageAlgebraCoextendScalars B S hS π).obj F ≅ (moduleDirectImage B S hS π).obj G)
    {P : Modules.{u, u} B S hS X.1 X.2}
    (ψ₀ : P ⟶ (directImageAlgebraRestrictScalars B S hS π).obj ((moduleDirectImage B S hS π).obj G))
    (p : G ⟶ Q)
    (hcok : ∀ ⦃Z : Modules.{u, u} B S hS U.1 U.2⦄
      (d : (etaleModulePullback B S hS g hg).obj ((directImageAlgebraRestrictScalars B S hS π).obj
        ((moduleDirectImage B S hS π).obj G)) ⟶ Z),
      (etaleModulePullback B S hS g hg).map ψ₀ ≫ d = 0 →
        ∃ d'' : (etaleModulePullback B S hS g hg).obj
            ((directImageAlgebraRestrictScalars B S hS π).obj ((moduleDirectImage B S hS π).obj Q))
            ⟶ Z,
          d = (etaleModulePullback B S hS g hg).map
            ((directImageAlgebraRestrictScalars B S hS π).map
              ((moduleDirectImage B S hS π).map p)) ≫ d'')
    (K : (SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).Submodule)
    (hK : ∀ (W : (smallEtaleRingedSite B S hS Y.1 Y.2).Cᵒᵖ)
      (r : (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj.obj W),
      r ∈ K.obj W → ∀ q : Q.val.obj W, r • q = 0)
    (εK : SheafOfModules.unit (structureRingSheaf B S hS U) ⟶
      (etaleModulePullback B S hS g hg).obj ((modulePushforward B S hS π).obj K.toSheafOfModules))
    (ε : SheafOfModules.unit (structureRingSheaf B S hS U) ⟶
      (etaleModulePullback B S hS g hg).obj (directImageAlgebraUnitModule B S hS π))
    (hfac : (εK ≫ (etaleModulePullback B S hS g hg).map ((modulePushforward B S hS π).map K.ι) :
          SheafOfModules.unit (structureRingSheaf B S hS U) ⟶
            (etaleModulePullback B S hS g hg).obj (pushforwardStructureModule B S hS π)) = ε)
    (pr : (etaleModulePullback B S hS g hg).obj (directImageAlgebraUnitModule B S hS π) ⟶
      SheafOfModules.unit (structureRingSheaf B S hS U))
    (hε : ε ≫ pr = 𝟙 _) :
    Epi ((etaleModulePullback B S hS g hg).map
      ((ψ₀ ≫ (directImageAlgebraRestrictScalars B S hS π).map e.inv) ≫
        (directImageAlgebraRestrictCoextendAdjunction B S hS π).counit.app F)) := by
  refine epi_etaleModulePullback_map_comp_counit_of_split B S hS π g hg F _ ε pr hε ?_
  intro Z d hd
  obtain ⟨d'', hd''⟩ := hcok ((etaleModulePullback B S hS g hg).map
    ((directImageAlgebraRestrictScalars B S hS π).map e.inv) ≫ d) (by
      rw [← Category.assoc, ← Functor.map_comp]
      exact hd)
  have hnat := etaleSectionAction_naturality B S hS π g hg ε e.hom
  have hd' : d = (etaleModulePullback B S hS g hg).map
      ((directImageAlgebraRestrictScalars B S hS π).map e.hom) ≫
      (etaleModulePullback B S hS g hg).map
        ((directImageAlgebraRestrictScalars B S hS π).map e.inv) ≫ d := by
    rw [← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, e.hom_inv_id,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [hd', ← Category.assoc, ← hnat, Category.assoc, hd'',
    etaleSectionAction_comp_eq_zero_of_factorsThrough B S hS π g hg p K hK εK ε hfac d'',
    comp_zero]

end AlgebraicGeometry.Space

end
