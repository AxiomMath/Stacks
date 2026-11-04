module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.ConormalSourceReading
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionConormalScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedClosedImmersionConormal
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiReadingIsoLift
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels

/-!
# The conormal isomorphism of a section of `𝐏(ℰ)` at an étale scheme point

Let `σ` be a section of `π : 𝐏(ℰ) ⟶ X` corresponding to the invertible quotient `q : ℰ ⟶ ℒ`
(Stacks 0B4I), and `x : T ⟶ X` an étale scheme point.  Reading `x^*(Ker q ⊗ ℒ^{⊗ -1})` and
`x^*𝒞_σ` on the scheme `T`, the first is `Ker(q_x) ⊗ ℒ_x^{⊗ -1}` and the second is the conormal
sheaf of the section `s_x` of `𝐏((x^*ℰ)_Zar) ⟶ T`; Stacks 0B3V on `T` identifies them.  Since the
Zariski reading is fully faithful on quasi-coherent modules this gives an isomorphism
`x^*(Ker q ⊗ ℒ^{⊗ -1}) ≅ x^*𝒞_σ` on the represented algebraic space of `T`: the chart
isomorphism the conormal clause of Stacks 0B4I is glued from.

## Main definitions

* `AlgebraicGeometry.Space.sectionConormalPointReadingIso`: the isomorphism of the readings.
* `AlgebraicGeometry.Space.sectionConormalPointIso`: the isomorphism on the represented space.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.SheafOfModules (IsInvertible)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory
attribute [local instance] Stacks.ProjectiveBundleConormal.monoidalSheafTensor

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (X : AlgebraicSpaces B S hS) (E : SheafOfModules.{u} (structureRingSheaf B S hS X))
  (hE : E.IsQuasicoherentOnSite) (hb : SymmetricAlgebraBounded X E)
  (σ : X ⟶ relativeProjSymmetricAlgebra X E hE hb) (hσ : σ ≫ projectiveBundleπ X E hE hb = 𝟙 X)
  (Q : InvertibleQuotient X E)

/-- The source `Ker(q) ⊗ ℒ^{⊗ -1}` of the conormal isomorphism of Stacks 0B4I. -/
abbrev sectionConormalSource : Modules.{u, u} B S hS X.1 X.2 :=
  haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L :=
    Q.invertible.toAlgebraicGeometry
  kernel Q.q ⊗ Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
    (structureRingSheaf B S hS X).property Q.L (-1)

/-- The target `𝒞_{σ(X)/𝐏(ℰ)}` of the conormal isomorphism of Stacks 0B4I. -/
abbrev sectionConormalTarget : Modules.{u, u} B S hS X.1 X.2 :=
  conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
    (isImmersion_of_isClosedImmersion B S hS
      (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ))

include hE in
/-- The source `Ker(q) ⊗ ℒ^{⊗ -1}` of the conormal isomorphism of Stacks 0B4I is
quasi-coherent. -/
theorem isQuasicoherentOnSite_sectionConormalSource :
    (sectionConormalSource X E Q).IsQuasicoherentOnSite :=
  have : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L :=
    Q.invertible.toAlgebraicGeometry
  isQuasicoherentOnSite_kernel_tensor_tensorPower_neg_one X Q.q hE

/-- The pullback of the conormal module of `σ` to an étale scheme point is quasi-coherent: it is
the conormal module of the closed immersion `k_x` of schemes. -/
theorem isQuasicoherentOnSite_pointPullback_sectionConormalTarget (T : BigFppfOver B S hS)
    (x : yoneda.obj T ⟶ X.1) (hx : IsEtale B S hS x) :
    ((modulePullback B S hS (pointHom x)).obj
      (sectionConormalTarget X E hE hb σ hσ)).IsQuasicoherentOnSite :=
  have := isClosedImmersion_sectionFibreLift X E hE hb σ hσ T x
  SheafOfModules.IsQuasicoherentOnSite.of_iso (sectionConormalChartIso X E hE hb σ hσ T x hx).symm
    (isQuasicoherentOnSite_conormalAlgebra_piece_one_yonedaSpaceMap
      (sectionFibreLift X E hE hb σ hσ T x))

/-- **The conormal isomorphism of Stacks 0B4I read at an étale scheme point**: the source reading,
Stacks 0B3V at `s_x`, the identification of `s_x` with the section `k_x` of the fibre, and the
reading of the conormal module of `k_x` (Stacks 09RR along the fibre). -/
def sectionConormalPointReadingIso
    (hQ : projectiveBundleSectionsEquiv X E hE hb ⟨σ, hσ⟩ = Quotient.mk _ Q)
    (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) (hx : IsEtale B S hS x) :
    (zariskiReadingFunctor T).obj
        ((modulePullback B S hS (pointHom x)).obj (sectionConormalSource X E Q)) ≅
      (zariskiReadingFunctor T).obj
        ((modulePullback B S hS (pointHom x)).obj (sectionConormalTarget X E hE hb σ hσ)) :=
  haveI := isClosedImmersion_sectionFibreLift X E hE hb σ hσ T x
  conormalSourceReadingIso X E hE Q T x hx ≪≫
    sectionPointConormalIso X E hE hb σ hσ Q hQ T x ≪≫
    sectionPointConormalFibreIso X E hE hb σ hσ T x ≪≫
    (zariskiReadingConormalIso (sectionFibreLift X E hE hb σ hσ T x)).symm ≪≫
    ((zariskiReadingFunctor T).mapIso (sectionConormalChartIso X E hE hb σ hσ T x hx)).symm

/-- **The chart isomorphism of the conormal clause of Stacks 0B4I** at an étale scheme point:
the lift of `sectionConormalPointReadingIso` along the Zariski reading. -/
def sectionConormalPointIso
    (hQ : projectiveBundleSectionsEquiv X E hE hb ⟨σ, hσ⟩ = Quotient.mk _ Q)
    (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) (hx : IsEtale B S hS x) :
    (modulePullback B S hS (pointHom x)).obj (sectionConormalSource X E Q) ≅
      (modulePullback B S hS (pointHom x)).obj (sectionConormalTarget X E hE hb σ hσ) :=
  isoOfZariskiReadingIso T
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x) _
      (isQuasicoherentOnSite_sectionConormalSource X E hE Q))
    (isQuasicoherentOnSite_pointPullback_sectionConormalTarget X E hE hb σ hσ T x hx)
    (sectionConormalPointReadingIso X E hE hb σ hσ Q hQ T x hx)

/-- The reading of the chart isomorphism is the reading isomorphism. -/
theorem zariskiReading_map_sectionConormalPointIso_hom
    (hQ : projectiveBundleSectionsEquiv X E hE hb ⟨σ, hσ⟩ = Quotient.mk _ Q)
    (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) (hx : IsEtale B S hS x) :
    (zariskiReadingFunctor T).map (sectionConormalPointIso X E hE hb σ hσ Q hQ T x hx).hom =
      (sectionConormalPointReadingIso X E hE hb σ hσ Q hQ T x hx).hom :=
  zariskiReading_map_isoOfZariskiReadingIso_hom T _ _ _

end AlgebraicGeometry.Space

end
