module

public import StacksFrontier.AlgebraicGeometry.ProjAwayChartFactor.Forward
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.TwistPullbackRatio.Basic

/-!
# The transition ratio of a pulled-back degree-one section, as a chart homomorphism

On the standard open `D₊(q)` of a graded ring the degree-one section of `p` is the fraction `p/q`
times the degree-one section of `q`. Pulled back along a morphism `g` into `Proj 𝒮` landing in
`D₊(q)`, the scalar becomes the value at `p/q` of the chart homomorphism
`Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.chartHomEquiv` of `g`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.pullbackSection_smul`: pulling a section back is semilinear
  over `AlgebraicGeometry.Scheme.Hom.appLE`.
* `AlgebraicGeometry.Scheme.Modules.pullbackSection_res`: pulling back a restricted section is
  pulling back the section.
* `Stacks.TwistPullbackRatio.pullbackSection_degreeSection_eq_smul`: for `g` landing in `D₊(q)`
  the pullback of the degree-one section of `p` is `chartHomEquiv ⟨g, hg⟩ (p/q)` times the
  pullback of the degree-one section of `q`.

## References

* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
* [Stacks Project, Tag 01NA](https://stacks.math.columbia.edu/tag/01NA)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistSections
open HomogeneousLocalization

universe u w

namespace AlgebraicGeometry.Scheme.Modules

/-- Pulling a section back is semilinear: the pullback of `r • a` is `f.appLE U V h r` times the
pullback of `a`. -/
public theorem pullbackSection_smul {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules)
    (U : X.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U) (r : Γ(X, U)) (a : Γ(F, U)) :
    pullbackSection f F U V h (r • a) =
      (((Scheme.Modules.pullback f).obj F).smul (f.appLE U V h r)).asHom.hom
        (pullbackSection f F U V h a) := by
  have hps : ∀ b : Γ(F, U), pullbackSection f F U V h b =
      ((Scheme.Modules.pullback f).obj F).presheaf.map (homOfLE h).op
        (Stacks.TwistPullbackRatio.pbSec f F U b) := fun _ ↦ rfl
  rw [hps, hps, Stacks.TwistPullbackRatio.pbSec_smul, Scheme.Modules.map_smul,
    Scheme.Modules.smul_apply]
  rfl

/-- A section over `U` restricted to a smaller open `U'` and then pulled back to `V ≤ f⁻¹U'` is
the pullback of the original section to `V`. -/
public theorem pullbackSection_res {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules)
    {U U' : X.Opens} (hU : U' ≤ U) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U') (a : Γ(F, U)) :
    pullbackSection f F U' V h (F.presheaf.map (homOfLE hU).op a) =
      pullbackSection f F U V (h.trans ((Opens.map f.base).map (homOfLE hU)).le) a := by
  have hnat : ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).val.app (op U')
        (F.presheaf.map (homOfLE hU).op a) =
      ((Scheme.Modules.pullback f).obj F).presheaf.map
        ((Opens.map f.base).map (homOfLE hU)).op
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).val.app (op U) a) :=
    PresheafOfModules.naturality_apply
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).val (homOfLE hU).op a
  have hmap : ((Scheme.Modules.pullback f).obj F).presheaf.map
          ((Opens.map f.base).map (homOfLE hU)).op ≫
        ((Scheme.Modules.pullback f).obj F).presheaf.map (homOfLE h).op =
      ((Scheme.Modules.pullback f).obj F).presheaf.map
        (homOfLE (h.trans ((Opens.map f.base).map (homOfLE hU)).le)).op := by
    rw [← Functor.map_comp,
      show ((Opens.map f.base).map (homOfLE hU)).op ≫ (homOfLE h).op =
        (homOfLE (h.trans ((Opens.map f.base).map (homOfLE hU)).le)).op from
          Subsingleton.elim _ _]
  change ((Scheme.Modules.pullback f).obj F).presheaf.map (homOfLE h).op
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).val.app (op U')
        (F.presheaf.map (homOfLE hU).op a)) = _
  rw [hnat]
  exact (ConcreteCategory.comp_apply
      (((Scheme.Modules.pullback f).obj F).presheaf.map
        ((Opens.map f.base).map (homOfLE hU)).op)
      (((Scheme.Modules.pullback f).obj F).presheaf.map (homOfLE h).op) _).symm.trans
    (congrArg
      (fun φ : ((Scheme.Modules.pullback f).obj F).presheaf.obj (op (f ⁻¹ᵁ U)) ⟶
          ((Scheme.Modules.pullback f).obj F).presheaf.obj (op V) ↦
        ConcreteCategory.hom φ
          (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).val.app (op U) a)) hmap)

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.TwistPullbackRatio

variable {S : Type u} [CommRing S] {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

/-- Let `p` and `q` be degree-one elements of a graded ring and let `g` be a morphism into
`Proj 𝒮` whose preimage of the standard open `D₊(q)` is everything. Then the pullback along `g` of
the degree-one section of `p` is the value of the chart homomorphism of `g` at the fraction `p/q`
times the pullback of the degree-one section of `q`. -/
theorem pullbackSection_degreeSection_eq_smul {Y : Scheme.{u}} {p q : S} (hp : p ∈ 𝒮 1)
    (hq : q ∈ 𝒮 1) (g : Y ⟶ AlgebraicGeometry.Proj 𝒮)
    (hg : g ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒮 q = ⊤) :
    Scheme.Modules.pullbackSection g (O1 𝒮) (AlgebraicGeometry.Proj.basicOpen 𝒮 q) ⊤ hg.ge
        ((O1 𝒮).presheaf.map
          (homOfLE (le_top (a := AlgebraicGeometry.Proj.basicOpen 𝒮 q))).op
          (degreeSection 𝒮 1 ⟨p, hp⟩)) =
      (((Scheme.Modules.pullback g).obj (O1 𝒮)).smul
            ((Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.chartHomEquiv 𝒮 hq Nat.one_pos Y
              ⟨g, hg⟩).hom (Away.mk 𝒮 hq 1 p (by simpa using hp)))).asHom.hom
        (Scheme.Modules.pullbackSection g (O1 𝒮) (AlgebraicGeometry.Proj.basicOpen 𝒮 q) ⊤ hg.ge
          ((O1 𝒮).presheaf.map
            (homOfLE (le_top (a := AlgebraicGeometry.Proj.basicOpen 𝒮 q))).op
            (degreeSection 𝒮 1 ⟨q, hq⟩))) := by
  have hscal := congrArg
    (fun φ : CommRingCat.of (HomogeneousLocalization.Away 𝒮 q) ⟶ Γ(Y, ⊤) ↦
      φ.hom (Away.mk 𝒮 hq 1 p (by simpa using hp)))
    (Stacks.AlgebraicGeometry.ProjAwayChartFactor.chartHomEquiv_apply 𝒮 hq Nat.one_pos hg)
  dsimp only at hscal
  rw [degreeSection_res_eq 𝒮 hp hq, Scheme.Modules.pullbackSection_smul, hscal]
  rfl

end Stacks.TwistPullbackRatio

end
