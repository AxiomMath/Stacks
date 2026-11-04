module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionsConormalFibreTwoSpaceComparison.FibreSections

/-!
# The quotient carried by the section of the fibre of `𝐏(g^*ℰ)`, transported

The quotient carried by the section of the fibre of `𝐏(g^*ℰ)` over `v` is the Zariski reading of
a representative of the class of the inclusion of the fibre (Tag 0B3V), also when read through
`(u ∘ h ∘ f')^*ℰ ≅ (v ∘ f')^* g^*ℰ`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable (X : AlgebraicSpaces B S hS) (E : SheafOfModules.{u} (structureRingSheaf B S hS X))
variable {T : BigFppfOver B S hS} (u : yoneda.obj T ⟶ X.1)
variable {X' : AlgebraicSpaces B S hS} (g : X' ⟶ X) {T' : BigFppfOver B S hS}
variable (v : yoneda.obj T' ⟶ X'.1) (h : T' ⟶ T) (hvh : v ≫ g.hom = yoneda.map h ≫ u)
variable (hE : E.IsQuasicoherentOnSite) (hb : SymmetricAlgebraBounded X E)
variable (hb' : SymmetricAlgebraBounded X' ((modulePullback B S hS g).obj E))

include u h hvh hE hb hb' in
/-- The quotient carried by the section of the fibre of `𝐏(g^*ℰ)` over `v` is the Zariski reading
of a representative of the class of the inclusion of the fibre (Tag 0B3V). -/
theorem overQuotient_pointBundleSection_eq_zariskiReading
    (Q₀ : InvertibleQuotient (yonedaSpace B S hS ((projectiveBundleSituation X'
    ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE
    g) hb').relativeProjPoints.fibre T' v)) ((modulePullback B S hS
    (pointHom (yoneda.map ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
    (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
    hb').relativeProjPoints.fibreHom T' v) ≫ v))).obj ((modulePullback B S hS g).obj E)))
    (hQ₀ : Quotient.mk _ Q₀ = (pointsEquivInvertibleQuotientClass X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb' ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibre T' v) (yoneda.map
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v) ≫ v)
        (⟨(projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreToSpace T' v,
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.isPullback T' v).w⟩ :
        {w : yoneda.obj ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibre T' v) ⟶ (relativeProjSymmetricAlgebra X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb').1 // w ≫ (projectiveBundleπ X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').hom = yoneda.map
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v) ≫ v}))) :
    haveI := isQuasicoherent_pointZariskiModule X E hE T u
    haveI := isQuasicoherent_pointZariskiModule X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) T' v
    haveI := isQuasicoherent_pointZariskiModule X E hE
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibre T' v) (yoneda.map
        (((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v) ≫ h) ≫ u)
    haveI := isQuasicoherent_pointZariskiModule X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibre T' v) (yoneda.map
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v) ≫ v)
    Quotient.mk (Stacks.Divisors.invertibleQuotientSetoid
        ((BigFppfOver.toScheme B S hS).obj ((projectiveBundleSituation X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb').relativeProjPoints.fibre T' v))
        (pointZariskiModule X' ((modulePullback B S hS g).obj E)
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibre T' v) (yoneda.map
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v) ≫ v)))
        ((Stacks.RelativeProj.tautologicalDatum (pointZariskiModule X'
        ((modulePullback B S hS g).obj E) T' v)).overQuotient
        (pointZariskiModule X' ((modulePullback B S hS g).obj E)
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibre T' v) (yoneda.map
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v) ≫ v))
        (pointZariskiModuleBaseChangeIso X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) v
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v)) ((pointRelativeProjSection X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb' ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibre T' v) (yoneda.map
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v) ≫ v)
        (⟨(projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreToSpace T' v,
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.isPullback T' v).w⟩ :
        {w : yoneda.obj ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibre T' v) ⟶ (relativeProjSymmetricAlgebra X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb').1 // w ≫ (projectiveBundleπ X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').hom = yoneda.map
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v) ≫ v})).1 ≫
        (Stacks.RelativeProj.projectiveBundleBaseChange
        ((BigFppfOver.toScheme B S hS).map ((projectiveBundleSituation X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb').relativeProjPoints.fibreHom T' v))
        (pointZariskiModule X' ((modulePullback B S hS g).obj E) T' v)
        (pointZariskiModule X' ((modulePullback B S hS g).obj E)
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibre T' v) (yoneda.map
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v) ≫ v))
        (pointZariskiModuleBaseChangeIso X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) v
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v))))
        (pointBundleSection_comp_projectiveBundleBaseChange_comp_toBase X E u g v h hvh hE hb hb'))
        = Quotient.mk (Stacks.Divisors.invertibleQuotientSetoid
        ((BigFppfOver.toScheme B S hS).obj ((projectiveBundleSituation X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb').relativeProjPoints.fibre T' v))
        (pointZariskiModule X' ((modulePullback B S hS g).obj E)
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibre T' v) (yoneda.map
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v) ≫ v)))
        (zariskiReadingInvertibleQuotient (isQuasicoherentOnSite_pointPullback X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibre T' v) (yoneda.map
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v) ≫ v)) Q₀) := by
  have := isQuasicoherent_pointZariskiModule X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) T' v
  have := isQuasicoherent_pointZariskiModule X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
      ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').relativeProjPoints.fibre
      T' v) (yoneda.map ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
      hb').relativeProjPoints.fibreHom T' v) ≫ v)
  exact ((Stacks.RelativeProj.projectiveBundleSectionsEquiv_eq_overQuotient
      (pointZariskiModule X' ((modulePullback B S hS g).obj E)
      ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').relativeProjPoints.fibre
      T' v) (yoneda.map ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
      hb').relativeProjPoints.fibreHom T' v) ≫ v))
      (pointZariskiModuleBaseChangeIso X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) v
      ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
      hb').relativeProjPoints.fibreHom T' v)) (pointRelativeProjSection X'
      ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
      hE g) hb' ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').relativeProjPoints.fibre
      T' v) (yoneda.map ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
      hb').relativeProjPoints.fibreHom T' v) ≫ v) (⟨(projectiveBundleSituation X'
      ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
      hE g) hb').relativeProjPoints.fibreToSpace T' v,
      ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
      hb').relativeProjPoints.isPullback T' v).w⟩ :
      {w : yoneda.obj ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').relativeProjPoints.fibre
      T' v) ⟶ (relativeProjSymmetricAlgebra X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').1 // w ≫
      (projectiveBundleπ X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').hom = yoneda.map
      ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
      hb').relativeProjPoints.fibreHom T' v) ≫ v}))
      (pointBundleSection_comp_projectiveBundleBaseChange_comp_toBase X E u g v h hvh hE hb
      hb')).symm.trans
    (projectiveBundleSectionsEquiv_pointBundleSection X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb'
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibre T' v) (yoneda.map
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v) ≫ v)
        (⟨(projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreToSpace T' v,
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.isPullback T' v).w⟩ :
        {w : yoneda.obj ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibre T' v) ⟶ (relativeProjSymmetricAlgebra X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb').1 // w ≫ (projectiveBundleπ X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').hom = yoneda.map
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v) ≫ v}))).trans
      ((congrArg (invertibleQuotientClassZariskiEquiv
          ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
          hb').relativeProjPoints.fibre T' v) _ (isQuasicoherentOnSite_pointPullback X'
          ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X
          E hE g) ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
          hb').relativeProjPoints.fibre T' v) (yoneda.map
          ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
          hb').relativeProjPoints.fibreHom T' v) ≫ v))) hQ₀.symm).trans
        (invertibleQuotientClassZariskiEquiv_mk _ _ Q₀))

include u h hvh hE hb hb' in
/-- The quotient carried by the section of the fibre of `𝐏(g^*ℰ)` over `v`, read through
`(u ∘ h ∘ f')^*ℰ ≅ (v ∘ f')^* g^*ℰ`, is the Zariski reading of the transported representative. -/
theorem overQuotient_pointBundleSection_twoSpace_transport
    (Q₀ : InvertibleQuotient (yonedaSpace B S hS ((projectiveBundleSituation X'
    ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE
    g) hb').relativeProjPoints.fibre T' v)) ((modulePullback B S hS
    (pointHom (yoneda.map ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
    (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
    hb').relativeProjPoints.fibreHom T' v) ≫ v))).obj ((modulePullback B S hS g).obj E)))
    (hQ₀ : Quotient.mk _ Q₀ = (pointsEquivInvertibleQuotientClass X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb' ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibre T' v) (yoneda.map
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v) ≫ v)
        (⟨(projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreToSpace T' v,
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.isPullback T' v).w⟩ :
        {w : yoneda.obj ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibre T' v) ⟶ (relativeProjSymmetricAlgebra X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb').1 // w ≫ (projectiveBundleπ X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').hom = yoneda.map
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v) ≫ v}))) :
    haveI := isQuasicoherent_pointZariskiModule X E hE T u
    haveI := isQuasicoherent_pointZariskiModule X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) T' v
    haveI := isQuasicoherent_pointZariskiModule X E hE
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibre T' v) (yoneda.map
        (((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v) ≫ h) ≫ u)
    haveI := isQuasicoherent_pointZariskiModule X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibre T' v) (yoneda.map
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v) ≫ v)
    Quotient.mk (Stacks.Divisors.invertibleQuotientSetoid
        ((BigFppfOver.toScheme B S hS).obj ((projectiveBundleSituation X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb').relativeProjPoints.fibre T' v))
        (pointZariskiModule X E ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibre T' v) (yoneda.map
        (((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v) ≫ h) ≫ u)))
        ((Stacks.RelativeProj.tautologicalDatum (pointZariskiModule X'
        ((modulePullback B S hS g).obj E) T' v)).overQuotient
        (pointZariskiModule X E ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibre T' v) (yoneda.map
        (((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v) ≫ h) ≫ u))
        ((zariskiReadingFunctor ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibre T' v)).mapIso
        (pointTwoSpaceCompIso X E u g v h hvh ((projectiveBundleSituation X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb').relativeProjPoints.fibreHom T' v)) ≪≫
        (pointZariskiModuleBaseChangeIso X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) v
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v))) ((pointRelativeProjSection X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb' ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibre T' v) (yoneda.map
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v) ≫ v)
        (⟨(projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreToSpace T' v,
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.isPullback T' v).w⟩ :
        {w : yoneda.obj ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibre T' v) ⟶ (relativeProjSymmetricAlgebra X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb').1 // w ≫ (projectiveBundleπ X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').hom = yoneda.map
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v) ≫ v})).1 ≫
        (Stacks.RelativeProj.projectiveBundleBaseChange
        ((BigFppfOver.toScheme B S hS).map ((projectiveBundleSituation X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb').relativeProjPoints.fibreHom T' v))
        (pointZariskiModule X' ((modulePullback B S hS g).obj E) T' v)
        (pointZariskiModule X' ((modulePullback B S hS g).obj E)
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibre T' v) (yoneda.map
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v) ≫ v))
        (pointZariskiModuleBaseChangeIso X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) v
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v))))
        (pointBundleSection_comp_projectiveBundleBaseChange_comp_toBase X E u g v h hvh hE hb hb'))
        = Quotient.mk (Stacks.Divisors.invertibleQuotientSetoid
        ((BigFppfOver.toScheme B S hS).obj ((projectiveBundleSituation X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb').relativeProjPoints.fibre T' v))
        (pointZariskiModule X E ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibre T' v) (yoneda.map
        (((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v) ≫ h) ≫ u)))
        (zariskiReadingInvertibleQuotient (isQuasicoherentOnSite_pointPullback X E hE
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibre T' v) (yoneda.map
        (((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v) ≫ h) ≫ u))
        (Q₀.transport (pointTwoSpaceCompIso X E u g v h hvh
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v)))) := by
  have := isQuasicoherent_pointZariskiModule X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) T' v
  have := isQuasicoherent_pointZariskiModule X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
      ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').relativeProjPoints.fibre
      T' v) (yoneda.map ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
      hb').relativeProjPoints.fibreHom T' v) ≫ v)
  exact Quotient.sound (overQuotient_mapIso_trans_isEquivalent
      (Stacks.RelativeProj.tautologicalDatum (pointZariskiModule X'
      ((modulePullback B S hS g).obj E) T' v)) (isQuasicoherentOnSite_pointPullback X E hE
      ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').relativeProjPoints.fibre
      T' v) (yoneda.map (((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
      hb').relativeProjPoints.fibreHom T' v) ≫ h) ≫ u))
      (isQuasicoherentOnSite_pointPullback X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
      ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').relativeProjPoints.fibre
      T' v) (yoneda.map ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
      hb').relativeProjPoints.fibreHom T' v) ≫ v))
    (i₁ := isQuasicoherent_pointZariskiModule X E hE
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibre T' v) (yoneda.map
        (((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v) ≫ h) ≫ u))
    (i₂ := isQuasicoherent_pointZariskiModule X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibre T' v) (yoneda.map
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v) ≫ v))
    (pointTwoSpaceCompIso X E u g v h hvh ((projectiveBundleSituation X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb').relativeProjPoints.fibreHom T' v))
        (pointZariskiModuleBaseChangeIso X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) v
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v)) ((pointRelativeProjSection X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb' ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibre T' v) (yoneda.map
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v) ≫ v)
        (⟨(projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreToSpace T' v,
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.isPullback T' v).w⟩ :
        {w : yoneda.obj ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibre T' v) ⟶ (relativeProjSymmetricAlgebra X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb').1 // w ≫ (projectiveBundleπ X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').hom = yoneda.map
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v) ≫ v})).1 ≫
        (Stacks.RelativeProj.projectiveBundleBaseChange
        ((BigFppfOver.toScheme B S hS).map ((projectiveBundleSituation X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb').relativeProjPoints.fibreHom T' v))
        (pointZariskiModule X' ((modulePullback B S hS g).obj E) T' v)
        (pointZariskiModule X' ((modulePullback B S hS g).obj E)
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibre T' v) (yoneda.map
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v) ≫ v))
        (pointZariskiModuleBaseChangeIso X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) v
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v))))
        (pointBundleSection_comp_projectiveBundleBaseChange_comp_toBase X E u g v h hvh hE hb hb')
        Q₀
    (Quotient.exact (overQuotient_pointBundleSection_eq_zariskiReading X E u g v h hvh hE hb hb' Q₀
        hQ₀)))

end AlgebraicGeometry.Space

end
