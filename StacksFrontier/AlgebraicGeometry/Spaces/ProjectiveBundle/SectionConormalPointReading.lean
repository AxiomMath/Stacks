module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraPieceSquareMap
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionsConormalChartIso

/-!
# The conormal module of a section of `𝐏(ℰ)` read at an arbitrary scheme point, and its base
change

Let `σ` be a section of `π : 𝐏(ℰ) ⟶ X`.  At a scheme point `x : T ⟶ X` the base change of `σ` is
the section `k_x` of the fibre `𝐏(ℰ)_T` (`AlgebraicGeometry.Space.sectionFibreLift`), and the
cartesian square of `k_x`, `x`, `σ` and the projection of the fibre gives the canonical map of
conormal modules `x^*𝒞_σ ⟶ 𝒞_{k_x}` (the degree-one map of Stacks 09RS,
`AlgebraicGeometry.Space.conormalAlgebraPieceSquareMap`).  For étale `x` it is the chart
isomorphism `AlgebraicGeometry.Space.sectionConormalChartIso` (Stacks 09RR); for every `x` its
Zariski reading followed by the identification of `𝒞_{k_x}` with the conormal sheaf of the
section `s_x` of `𝐏((x^*ℰ)_Zar)` on `T` is the target reading of the conormal clause of Stacks
0B4I at `x`.

For `g : X' ⟶ X` and a section `σ'` of `𝐏(g^*ℰ) ⟶ X'` over `σ`, the square of `σ'`, `g`, `σ` and
`𝐏(g^*ℰ) ⟶ 𝐏(ℰ)` gives the base-change map `g^*𝒞_σ ⟶ 𝒞_{σ'}` of the conormal clause.

## Main definitions

* `AlgebraicGeometry.Space.sectionConormalTargetPointHom`: `x^*𝒞_σ ⟶ 𝒞_{k_x}`.
* `AlgebraicGeometry.Space.sectionConormalTargetPointReadingHom`:
  `R_T(x^*𝒞_σ) ⟶ 𝒞_{T/𝐏(ℰ)_T}`, the conormal sheaf of the closed immersion `k_x` of schemes.
* `AlgebraicGeometry.Space.conormalAlgebraPieceSquareMapOfIsos`: the degree-`n` map of conormal
  algebras of a square, read through identifications of the pieces on both sides.
* `AlgebraicGeometry.Space.sectionConormalTargetBaseChangeHom`: `g^*𝒞_σ ⟶ 𝒞_{σ'}`.

## Main results

* `AlgebraicGeometry.Space.sectionConormalTargetPointHom_eq_chartIso`: at an étale point the map
  is the chart isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (X : AlgebraicSpaces B S hS) (E : SheafOfModules.{u} (structureRingSheaf B S hS X))
  (hE : E.IsQuasicoherentOnSite) (hb : SymmetricAlgebraBounded X E)
  (σ : X ⟶ relativeProjSymmetricAlgebra X E hE hb) (hσ : σ ≫ projectiveBundleπ X E hE hb = 𝟙 X)

variable (B S hS) in
/-- The degree-`n` map of conormal algebras of a commutative square
(`AlgebraicGeometry.Space.conormalAlgebraPieceSquareMapOfIso`), read through identifications `κ`
and `κ'` of the degree-`n` pieces on both sides. -/
def conormalAlgebraPieceSquareMapOfIsos {X₀ Z₀ U₀ ZU₀ : AlgebraicSpaces B S hS} (p : ZU₀ ⟶ Z₀)
    (iU : ZU₀ ⟶ U₀) (i : Z₀ ⟶ X₀) (φ : U₀ ⟶ X₀) (hsq : iU ≫ φ = p ≫ i) (n : ℤ)
    {M : Modules.{u, u} B S hS Z₀.1 Z₀.2} (κ : M ≅ (conormalAlgebra B S hS i).piece n)
    {M' : Modules.{u, u} B S hS ZU₀.1 ZU₀.2} (κ' : M' ≅ (conormalAlgebra B S hS iU).piece n) :
    (modulePullback B S hS p).obj M ⟶ M' :=
  conormalAlgebraPieceSquareMapOfIso B S hS p iU i φ hsq n κ ≫ κ'.inv

/-- **The conormal module of a section, pulled back to an arbitrary scheme point `x`, maps to the
conormal module of the section `k_x` of the fibre**: the degree-one map of conormal algebras of
the cartesian square of `k_x`, `x`, `σ` and the projection of the fibre. -/
def sectionConormalTargetPointHom (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) :
    (modulePullback B S hS (pointHom x)).obj (sectionConormalTarget X E hE hb σ hσ) ⟶
      (conormalAlgebra B S hS (yonedaSpaceMap (sectionFibreLift X E hE hb σ hσ T x))).piece 1 :=
  conormalAlgebraPieceSquareMapOfIso B S hS (pointHom x)
    (yonedaSpaceMap (sectionFibreLift X E hE hb σ hσ T x)) σ _
    (isPullback_sectionFibreLift X E hE hb σ hσ T x).w.symm 1
    (sectionConormalTargetPieceIso X E hE hb σ hσ)

/-- **At an étale scheme point the map is the chart isomorphism** of Stacks 09RR. -/
theorem sectionConormalTargetPointHom_eq_chartIso (T : BigFppfOver B S hS)
    (x : yoneda.obj T ⟶ X.1) (hx : IsEtale B S hS x) :
    sectionConormalTargetPointHom X E hE hb σ hσ T x =
      (sectionConormalChartIso X E hE hb σ hσ T x hx).hom := by
  unfold sectionConormalTargetPointHom sectionConormalChartIso
  exact conormalAlgebraPieceSquareMapOfIso_eq B S hS _ _ _ _
    (isPullback_sectionFibreLift X E hE hb σ hσ T x) (isEtale_fibreToSpace X E hE hb T x hx) _ _

/-- **The target of the conormal isomorphism of Stacks 0B4I read at an arbitrary scheme point
`x : T ⟶ X`**: the Zariski reading of `x^*𝒞_σ ⟶ 𝒞_{k_x}` followed by the identification of the
reading of `𝒞_{k_x}` with the conormal sheaf of the closed immersion `k_x` of schemes
(`AlgebraicGeometry.Space.sectionPointConormalFibreIso` identifies the latter with the conormal
sheaf of the section `s_x` of `𝐏((x^*ℰ)_Zar) ⟶ T`). -/
def sectionConormalTargetPointReadingHom (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) :
    haveI := isClosedImmersion_sectionFibreLift X E hE hb σ hσ T x
    (zariskiReadingFunctor T).obj
        ((modulePullback B S hS (pointHom x)).obj (sectionConormalTarget X E hE hb σ hσ)) ⟶
      Stacks.Conormal.conormalSheaf (Z := (BigFppfOver.toScheme B S hS).obj T)
        (X := (BigFppfOver.toScheme B S hS).obj
          ((projectiveBundleSituation X E hE hb).relativeProjPoints.fibre T x))
        ((BigFppfOver.toScheme B S hS).map (sectionFibreLift X E hE hb σ hσ T x)) :=
  haveI := isClosedImmersion_sectionFibreLift X E hE hb σ hσ T x
  (zariskiReadingFunctor T).map (sectionConormalTargetPointHom X E hE hb σ hσ T x) ≫
    (zariskiReadingConormalIso (sectionFibreLift X E hE hb σ hσ T x)).hom

section BaseChange

variable {X' : AlgebraicSpaces B S hS} (g : X' ⟶ X)
  (hb' : SymmetricAlgebraBounded X' ((modulePullback B S hS g).obj E))
  (σ' : X' ⟶ relativeProjSymmetricAlgebra X' ((modulePullback B S hS g).obj E)
    (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb')
  (hσ' : σ' ≫ projectiveBundleπ X' ((modulePullback B S hS g).obj E)
    (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' = 𝟙 X')

/-- **The base change of the target of the conormal isomorphism of Stacks 0B4I** along
`g : X' ⟶ X`: for a section `σ'` of `𝐏(g^*ℰ) ⟶ X'` lying over `σ`, the degree-one map of
conormal algebras of the square of `σ'`, `g`, `σ` and `𝐏(g^*ℰ) ⟶ 𝐏(ℰ)`, read on the conormal
modules of the two closed immersions. -/
def sectionConormalTargetBaseChangeHom
    (comm : σ' ≫ projectiveBundleBaseChange X E hE hb g hb' = g ≫ σ) :
    (modulePullback B S hS g).obj
        (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
          (isImmersion_of_isClosedImmersion B S hS
            (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ))) ⟶
      sectionConormalTarget X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' :=
  conormalAlgebraPieceSquareMapOfIsos B S hS g σ' σ (projectiveBundleBaseChange X E hE hb g hb')
    comm 1 (sectionConormalTargetPieceIso X E hE hb σ hσ)
    (sectionConormalTargetPieceIso X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ')

end BaseChange

end AlgebraicGeometry.Space

end
