module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionsConormalFibreTwoSpaceComparison.FibreQuotients
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionsConormalFibreTwoSpaceComparison.FibreQuotientTransport

/-!
# The comparison of fibres is the base change of projective bundles

The transported representative and the quotient carried by the comparison of fibres, read in
`𝐏((u^*ℰ)_Zar)`, agree with the quotient carried by the section of the fibre of `𝐏(g^*ℰ)`;
hence the comparison of fibres `𝐏(g^*ℰ)_{T'} ⟶ 𝐏(ℰ)_T` is the base change of projective bundles
along `h` (Tags 01O3, 01O4).
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

/-- The Zariski readings of `u`, `v`, and of `u` and `v` pulled back to the fibre are
quasi-coherent. -/
private theorem isQuasicoherent_pointZariskiModule_fibre :
    (pointZariskiModule X E T u).IsQuasicoherent ∧
    (pointZariskiModule X' ((modulePullback B S hS g).obj E) T' v).IsQuasicoherent ∧
    (pointZariskiModule X E ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').relativeProjPoints.fibre
      T' v) (yoneda.map (((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
      hb').relativeProjPoints.fibreHom T' v) ≫ h) ≫ u)).IsQuasicoherent ∧
    (pointZariskiModule X' ((modulePullback B S hS g).obj E)
      ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').relativeProjPoints.fibre
      T' v) (yoneda.map ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
      hb').relativeProjPoints.fibreHom T' v) ≫ v)).IsQuasicoherent :=
  ⟨isQuasicoherent_pointZariskiModule X E hE _ _,
    isQuasicoherent_pointZariskiModule X' _ (isQuasicoherentOnSite_modulePullback_projectiveBundle
      X E hE g) _ _,
    isQuasicoherent_pointZariskiModule X E hE _ _,
    isQuasicoherent_pointZariskiModule X' _ (isQuasicoherentOnSite_modulePullback_projectiveBundle
      X E hE g) _ _⟩

include u h hvh hE hb' in
/-- The transported representative read through `(u ∘ h ∘ f')^*ℰ ≅ (v ∘ f')^* g^*ℰ` and through the
comparison of Stacks 03LU at `v ∘ f'` have the same Zariski reading. -/
theorem zariskiReadingInvertibleQuotient_transport_pointTwoSpaceCompIso
    (Q₀ : InvertibleQuotient (yonedaSpace B S hS ((projectiveBundleSituation X'
    ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE
    g) hb').relativeProjPoints.fibre T' v)) ((modulePullback B S hS
    (pointHom (yoneda.map ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
    (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
    hb').relativeProjPoints.fibreHom T' v) ≫ v))).obj ((modulePullback B S hS g).obj E))) :
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
        hb').relativeProjPoints.fibreHom T' v)))) = Quotient.mk
        (Stacks.Divisors.invertibleQuotientSetoid ((BigFppfOver.toScheme B S hS).obj
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibre T' v)) (pointZariskiModule X E
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
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
        (Q₀.transport (eqToIso (congrArg (fun y => (modulePullback B S hS (pointHom y)).obj E)
        (yoneda_map_comp_point_twoSpace X u g v h hvh
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v)).symm) ≪≫ pointCompIso g E
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibre T' v) (yoneda.map
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v) ≫ v)))) := by
  have hq := isQuasicoherent_pointZariskiModule_fibre X E u g v h hE hb'
  have := hq.1
  have := hq.2.1
  have := hq.2.2.1
  have := hq.2.2.2
  exact congrArg (fun e => Quotient.mk (Stacks.Divisors.invertibleQuotientSetoid
      ((BigFppfOver.toScheme B S hS).obj ((projectiveBundleSituation X'
      ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
      hE g) hb').relativeProjPoints.fibre T' v)) (pointZariskiModule X E
      ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').relativeProjPoints.fibre
      T' v) (yoneda.map (((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
      hb').relativeProjPoints.fibreHom T' v) ≫ h) ≫ u)))
      (zariskiReadingInvertibleQuotient (isQuasicoherentOnSite_pointPullback X E hE
      ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').relativeProjPoints.fibre
      T' v) (yoneda.map (((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
      hb').relativeProjPoints.fibreHom T' v) ≫ h) ≫ u)) (Q₀.transport e)))
    (pointTwoSpaceCompIso_eq_pointCompIso X E u g v h hvh
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v))

include u h hvh hE hb hb' in
/-- The quotient carried by the comparison of fibres, read in `𝐏((u^*ℰ)_Zar)`, is the transported
Zariski reading of a representative of the class of the inclusion of the fibre of `𝐏(g^*ℰ)`. -/
theorem overQuotient_sectionFibreBaseChangeComparison
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
        ((Stacks.RelativeProj.tautologicalDatum (pointZariskiModule X E T u)).overQuotient
        (pointZariskiModule X E ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibre T' v) (yoneda.map
        (((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v) ≫ h) ≫ u))
        (pointZariskiModuleBaseChangeIso X E hE u (((projectiveBundleSituation X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb').relativeProjPoints.fibreHom T' v) ≫ h))
        ((BigFppfOver.toScheme B S hS).map (sectionFibreBaseChangeComparison X E hE hb g hb' u v h
        hvh) ≫ (pointFibreProjectiveBundleIso X E hE hb T u).hom)
        (sectionFibreBaseChangeComparison_comp_pointFibreProjectiveBundleIso_hom_comp_toBase X E u g
        v h hvh hE hb hb')) = Quotient.mk (Stacks.Divisors.invertibleQuotientSetoid
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
        (Q₀.transport (eqToIso (congrArg (fun y => (modulePullback B S hS (pointHom y)).obj E)
        (yoneda_map_comp_point_twoSpace X u g v h hvh
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v)).symm) ≪≫ pointCompIso g E
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibre T' v) (yoneda.map
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v) ≫ v)))) := by
  have hq := isQuasicoherent_pointZariskiModule_fibre X E u g v h hE hb'
  have := hq.1
  have := hq.2.1
  have := hq.2.2.1
  have := hq.2.2.2
  have P3 := (pointsEquivInvertibleQuotientClass_projectiveBundleBaseChange X E hE hb g hb'
    (yoneda.map ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
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
        hb').relativeProjPoints.fibreHom T' v) ≫ v})
        (yoneda.map (((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v) ≫ h) ≫ u)
        (yoneda_map_comp_point_twoSpace X u g v h hvh
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v)) (⟨(projectiveBundleSituation X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb').relativeProjPoints.fibreToSpace T' v ≫
        (projectiveBundleBaseChange X E hE hb g hb').hom,
        fibreToSpace_comp_projectiveBundleBaseChange_comp_π X E u g v h hvh hE hb hb'⟩ :
        {w : yoneda.obj ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibre T' v) ⟶ (relativeProjSymmetricAlgebra X E hE hb).1 // w ≫
        (projectiveBundleπ X E hE hb).hom = yoneda.map
        (((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v) ≫ h) ≫ u}) rfl).trans
      ((congrArg (invertibleQuotientTransportClass _) hQ₀.symm).trans
        (invertibleQuotientTransportClass_mk _ Q₀))
  exact (Quotient.sound (Stacks.RelativeProj.TautologicalDatum.overQuotient_isEquivalent_of_eq
      (Stacks.RelativeProj.tautologicalDatum (pointZariskiModule X E T u))
      (pointZariskiModule X E ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').relativeProjPoints.fibre
      T' v) (yoneda.map (((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
      hb').relativeProjPoints.fibreHom T' v) ≫ h) ≫ u))
      (pointZariskiModuleBaseChangeIso X E hE u (((projectiveBundleSituation X'
      ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
      hE g) hb').relativeProjPoints.fibreHom T' v) ≫ h))
    (pointBundleSection_twoSpace_comp_projectiveBundleBaseChange X E u g v h hvh hE hb hb').symm
        (sectionFibreBaseChangeComparison_comp_pointFibreProjectiveBundleIso_hom_comp_toBase X E u g
        v h hvh hE hb hb') (pointBundleSection_twoSpace_comp_projectiveBundleBaseChange_comp_toBase
        X E u g v h hvh hE hb hb'))).trans
    ((Stacks.RelativeProj.projectiveBundleSectionsEquiv_eq_overQuotient
        (pointZariskiModule X E ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibre T' v) (yoneda.map
        (((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v) ≫ h) ≫ u))
        (pointZariskiModuleBaseChangeIso X E hE u (((projectiveBundleSituation X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb').relativeProjPoints.fibreHom T' v) ≫ h))
        (pointRelativeProjSection X E hE hb ((projectiveBundleSituation X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb').relativeProjPoints.fibre T' v) (yoneda.map
        (((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v) ≫ h) ≫ u)
        (⟨(projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreToSpace T' v ≫
        (projectiveBundleBaseChange X E hE hb g hb').hom,
        fibreToSpace_comp_projectiveBundleBaseChange_comp_π X E u g v h hvh hE hb hb'⟩ :
        {w : yoneda.obj ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibre T' v) ⟶ (relativeProjSymmetricAlgebra X E hE hb).1 // w ≫
        (projectiveBundleπ X E hE hb).hom = yoneda.map
        (((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v) ≫ h) ≫ u}))
        (pointBundleSection_twoSpace_comp_projectiveBundleBaseChange_comp_toBase X E u g v h hvh hE
        hb hb')).symm.trans
      ((projectiveBundleSectionsEquiv_pointBundleSection X E hE hb
          ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
          hb').relativeProjPoints.fibre T' v) (yoneda.map
          (((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
          hb').relativeProjPoints.fibreHom T' v) ≫ h) ≫ u)
          (⟨(projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
          hb').relativeProjPoints.fibreToSpace T' v ≫
          (projectiveBundleBaseChange X E hE hb g hb').hom,
          fibreToSpace_comp_projectiveBundleBaseChange_comp_π X E u g v h hvh hE hb hb'⟩ :
          {w : yoneda.obj ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
          hb').relativeProjPoints.fibre T' v) ⟶ (relativeProjSymmetricAlgebra X E hE hb).1 // w ≫
          (projectiveBundleπ X E hE hb).hom = yoneda.map
          (((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
          hb').relativeProjPoints.fibreHom T' v) ≫ h) ≫ u})).trans
        ((congrArg (invertibleQuotientClassZariskiEquiv
            ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
            hb').relativeProjPoints.fibre T' v) _ (isQuasicoherentOnSite_pointPullback X E hE
            ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
            hb').relativeProjPoints.fibre T' v) (yoneda.map
            (((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
            hb').relativeProjPoints.fibreHom T' v) ≫ h) ≫ u))) P3).trans
          (invertibleQuotientClassZariskiEquiv_mk _ _ _))))

include hvh in
/-- **The comparison of fibres `𝐏(g^*ℰ)_{T'} ⟶ 𝐏(ℰ)_T` is the base change of projective bundles
along `h`**, through the identifications of the fibres with `𝐏((v^*g^*ℰ)_Zar)` and
`𝐏((u^*ℰ)_Zar)` and `(v^*g^*ℰ)_Zar ≅ h^*(u^*ℰ)_Zar`. -/
theorem pointFibreProjectiveBundleIso_hom_comp_projectiveBundleBaseChange_twoSpace :
    haveI := isQuasicoherent_pointZariskiModule X E hE T u
    haveI := isQuasicoherent_pointZariskiModule X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) T' v
    (pointFibreProjectiveBundleIso X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' T' v).hom ≫
        (Stacks.RelativeProj.projectiveBundleBaseChange ((BigFppfOver.toScheme B S hS).map h)
        (pointZariskiModule X E T u) (pointZariskiModule X' ((modulePullback B S hS g).obj E) T' v)
        (pointZariskiModuleTwoSpaceIso X E hE g u v h hvh)) =
        ((BigFppfOver.toScheme B S hS).map (sectionFibreBaseChangeComparison X E hE hb g hb' u v h
        hvh) ≫ (pointFibreProjectiveBundleIso X E hE hb T u).hom) := by
  have hq := isQuasicoherent_pointZariskiModule_fibre X E u g v h hE hb'
  have := hq.1
  have := hq.2.1
  have := hq.2.2.1
  have := hq.2.2.2
  obtain ⟨Q₀, hQ₀⟩ := Quotient.exists_rep (pointsEquivInvertibleQuotientClass X'
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
  exact Stacks.RelativeProj.eq_of_overQuotient_isEquivalent
      (pointZariskiModule X E ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').relativeProjPoints.fibre
      T' v) (yoneda.map (((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
      hb').relativeProjPoints.fibreHom T' v) ≫ h) ≫ u))
      (pointZariskiModuleBaseChangeIso X E hE u (((projectiveBundleSituation X'
      ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
      hE g) hb').relativeProjPoints.fibreHom T' v) ≫ h))
      ((pointFibreProjectiveBundleIso X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' T' v).hom ≫
      (Stacks.RelativeProj.projectiveBundleBaseChange ((BigFppfOver.toScheme B S hS).map h)
      (pointZariskiModule X E T u) (pointZariskiModule X' ((modulePullback B S hS g).obj E) T' v)
      (pointZariskiModuleTwoSpaceIso X E hE g u v h hvh)))
      ((BigFppfOver.toScheme B S hS).map (sectionFibreBaseChangeComparison X E hE hb g hb' u v h
      hvh) ≫ (pointFibreProjectiveBundleIso X E hE hb T u).hom)
      (pointFibreProjectiveBundleIso_hom_comp_projectiveBundleBaseChange_comp_toBase X E u g v h hvh
      hE hb hb')
      (sectionFibreBaseChangeComparison_comp_pointFibreProjectiveBundleIso_hom_comp_toBase X E u g v
      h hvh hE hb hb')
    (Quotient.exact ((overQuotient_comp_projectiveBundleBaseChange_twoSpace X E u g v h hvh hE hb
        hb').trans
      ((overQuotient_baseChange_tautologicalDatum_twoSpace X E u g v h hvh hE hb').trans
      ((overQuotient_pointFibreProjectiveBundleIso_eq_pointBundleSection X E u g v h hvh hE hb
          hb').trans
      ((overQuotient_pointBundleSection_twoSpace_transport X E u g v h hvh hE hb hb' Q₀ hQ₀).trans
      ((zariskiReadingInvertibleQuotient_transport_pointTwoSpaceCompIso X E u g v h hvh hE hb'
          Q₀).trans
        (overQuotient_sectionFibreBaseChangeComparison X E u g v h hvh hE hb hb' Q₀ hQ₀).symm))))))

end AlgebraicGeometry.Space

end
