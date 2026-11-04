module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionsConormalFibreTwoSpaceComparison.FibreSections

/-!
# Quotients carried by the fibre of `𝐏(g^*ℰ)` and its section

The invertible quotients carried by the base change of the fibre of `𝐏(g^*ℰ)` over `v`, by that
fibre for the base-changed tautological datum and by its section, and their comparison
(Tag 01O3).
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

/-- The Zariski readings along `u`, `v` and their restrictions along `k : Z ⟶ T'` are
quasi-coherent. -/
private theorem isQuasicoherent_pointZariskiModule_fibre_comp {Z : BigFppfOver B S hS}
    (k : Z ⟶ T') (hE : E.IsQuasicoherentOnSite) {P : Prop}
    (H : (pointZariskiModule X E T u).IsQuasicoherent →
      (pointZariskiModule X' ((modulePullback B S hS g).obj E) T' v).IsQuasicoherent →
      (pointZariskiModule X E Z (yoneda.map (k ≫ h) ≫ u)).IsQuasicoherent →
      (pointZariskiModule X' ((modulePullback B S hS g).obj E) Z
        (yoneda.map k ≫ v)).IsQuasicoherent → P) : P :=
  H (isQuasicoherent_pointZariskiModule X E hE T u)
    (isQuasicoherent_pointZariskiModule X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) T' v)
    (isQuasicoherent_pointZariskiModule X E hE Z _)
    (isQuasicoherent_pointZariskiModule X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) Z _)

include u h hvh hE hb hb' in
/-- The quotient carried by the base change of the fibre of `𝐏(g^*ℰ)` over `v` is the quotient
carried by that fibre for the base-changed tautological datum (Tag 01O3). -/
theorem overQuotient_comp_projectiveBundleBaseChange_twoSpace :
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
        ((pointFibreProjectiveBundleIso X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' T' v).hom ≫
        (Stacks.RelativeProj.projectiveBundleBaseChange ((BigFppfOver.toScheme B S hS).map h)
        (pointZariskiModule X E T u) (pointZariskiModule X' ((modulePullback B S hS g).obj E) T' v)
        (pointZariskiModuleTwoSpaceIso X E hE g u v h hvh)))
        (pointFibreProjectiveBundleIso_hom_comp_projectiveBundleBaseChange_comp_toBase X E u g v h
        hvh hE hb hb')) = Quotient.mk (Stacks.Divisors.invertibleQuotientSetoid
        ((BigFppfOver.toScheme B S hS).obj ((projectiveBundleSituation X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb').relativeProjPoints.fibre T' v))
        (pointZariskiModule X E ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibre T' v) (yoneda.map
        (((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v) ≫ h) ≫ u)))
        (((Stacks.RelativeProj.tautologicalDatum (pointZariskiModule X E T u)).baseChange
        ((BigFppfOver.toScheme B S hS).map h) (pointZariskiModule X E T u)
        (pointZariskiModule X' ((modulePullback B S hS g).obj E) T' v)
        (pointZariskiModuleTwoSpaceIso X E hE g u v h hvh)).overQuotient
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
        hb').relativeProjPoints.fibreHom T' v))) (pointFibreProjectiveBundleIso X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb' T' v).hom (pointFibreProjectiveBundleIso_hom_comp_projectiveBundleToBase X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb' T' v)) := by
  refine isQuasicoherent_pointZariskiModule_fibre_comp X E u g v h
    ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
      hb').relativeProjPoints.fibreHom T' v) hE fun _ _ _ _ => ?_
  exact Quotient.sound
      (Stacks.RelativeProj.TautologicalDatum.overQuotient_comp_projectiveBundleBaseChange_of_iso
    ((BigFppfOver.toScheme B S hS).map h) (pointZariskiModule X E T u)
        (pointZariskiModule X' ((modulePullback B S hS g).obj E) T' v)
        (pointZariskiModuleTwoSpaceIso X E hE g u v h hvh)
        (Stacks.RelativeProj.tautologicalDatum (pointZariskiModule X E T u))
        ((BigFppfOver.toScheme B S hS).map_comp ((projectiveBundleSituation X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb').relativeProjPoints.fibreHom T' v) h).symm
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
        hb').relativeProjPoints.fibreHom T' v))) (pointZariskiModuleBaseChangeIso X E hE u
        (((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v) ≫ h))
    (pointZariskiModuleBaseChangeIso_eq_twoSpace X E hE u g v h hvh
        ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v)) (pointFibreProjectiveBundleIso X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb' T' v).hom (pointFibreProjectiveBundleIso_hom_comp_projectiveBundleToBase X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb' T' v)
        (pointFibreProjectiveBundleIso_hom_comp_projectiveBundleBaseChange_comp_toBase X E u g v h
        hvh hE hb hb'))

include u h hvh hE hb' in
/-- For the fibre of `𝐏(g^*ℰ)` over `v`, the base-changed tautological datum and the tautological
datum of `𝐏((v^*g^*ℰ)_Zar)` carry the same quotient. -/
theorem overQuotient_baseChange_tautologicalDatum_twoSpace :
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
        (((Stacks.RelativeProj.tautologicalDatum (pointZariskiModule X E T u)).baseChange
        ((BigFppfOver.toScheme B S hS).map h) (pointZariskiModule X E T u)
        (pointZariskiModule X' ((modulePullback B S hS g).obj E) T' v)
        (pointZariskiModuleTwoSpaceIso X E hE g u v h hvh)).overQuotient
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
        hb').relativeProjPoints.fibreHom T' v))) (pointFibreProjectiveBundleIso X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb' T' v).hom (pointFibreProjectiveBundleIso_hom_comp_projectiveBundleToBase X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb' T' v)) = Quotient.mk (Stacks.Divisors.invertibleQuotientSetoid
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
        hb').relativeProjPoints.fibreHom T' v))) (pointFibreProjectiveBundleIso X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb' T' v).hom (pointFibreProjectiveBundleIso_hom_comp_projectiveBundleToBase X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb' T' v)) := by
  refine isQuasicoherent_pointZariskiModule_fibre_comp X E u g v h
    ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
      hb').relativeProjPoints.fibreHom T' v) hE fun _ _ _ _ => ?_
  exact Quotient.sound (Stacks.RelativeProj.TautologicalDatum.overQuotient_isEquivalent_of_univ
      ((Stacks.RelativeProj.tautologicalDatum (pointZariskiModule X E T u)).baseChange
          ((BigFppfOver.toScheme B S hS).map h) (pointZariskiModule X E T u)
          (pointZariskiModule X' ((modulePullback B S hS g).obj E) T' v)
          (pointZariskiModuleTwoSpaceIso X E hE g u v h hvh))
          (Stacks.RelativeProj.tautologicalDatum (pointZariskiModule X'
          ((modulePullback B S hS g).obj E) T' v))
      (Stacks.RelativeProj.tautologicalDatumTwistBaseChangeIso ((BigFppfOver.toScheme B S hS).map h)
          (pointZariskiModule X E T u) (pointZariskiModule X' ((modulePullback B S hS g).obj E) T'
          v) (pointZariskiModuleTwoSpaceIso X E hE g u v h hvh))
      (Stacks.RelativeProj.tautologicalDatum_baseChange_univ_comp_tautologicalDatumTwistBaseChangeIso_hom
        ((BigFppfOver.toScheme B S hS).map h) (pointZariskiModule X E T u)
            (pointZariskiModule X' ((modulePullback B S hS g).obj E) T' v)
            (pointZariskiModuleTwoSpaceIso X E hE g u v h hvh))
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
            ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle
            X E hE g) hb').relativeProjPoints.fibreHom T' v)) ≪≫
            (pointZariskiModuleBaseChangeIso X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) v
            ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
            hb').relativeProjPoints.fibreHom T' v)))
            (pointFibreProjectiveBundleIso X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' T' v).hom
            (pointFibreProjectiveBundleIso_hom_comp_projectiveBundleToBase X'
            ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle
            X E hE g) hb' T' v))

include u h hvh hE hb hb' in
/-- The quotient carried by the fibre of `𝐏(g^*ℰ)` over `v` is the quotient carried by its
section, base changed. -/
theorem overQuotient_pointFibreProjectiveBundleIso_eq_pointBundleSection :
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
        hb').relativeProjPoints.fibreHom T' v))) (pointFibreProjectiveBundleIso X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb' T' v).hom (pointFibreProjectiveBundleIso_hom_comp_projectiveBundleToBase X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb' T' v)) = Quotient.mk (Stacks.Divisors.invertibleQuotientSetoid
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
        (pointBundleSection_comp_projectiveBundleBaseChange_comp_toBase X E u g v h hvh hE hb
        hb')) := by
  refine isQuasicoherent_pointZariskiModule_fibre_comp X E u g v h
    ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
      hb').relativeProjPoints.fibreHom T' v) hE fun _ _ _ _ => ?_
  exact Quotient.sound (Stacks.RelativeProj.TautologicalDatum.overQuotient_isEquivalent_of_eq
      (Stacks.RelativeProj.tautologicalDatum (pointZariskiModule X'
      ((modulePullback B S hS g).obj E) T' v)) (pointZariskiModule X E
      ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').relativeProjPoints.fibre
      T' v) (yoneda.map (((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
      hb').relativeProjPoints.fibreHom T' v) ≫ h) ≫ u))
      ((zariskiReadingFunctor ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').relativeProjPoints.fibre
      T' v)).mapIso (pointTwoSpaceCompIso X E u g v h hvh
      ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
      hb').relativeProjPoints.fibreHom T' v)) ≪≫ (pointZariskiModuleBaseChangeIso X'
      ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
      hE g) v ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
      hb').relativeProjPoints.fibreHom T' v)))
    (pointFibreProjectiveBundleIso_hom_eq_pointBundleSection_comp X E u g v h hE hb')
        (pointFibreProjectiveBundleIso_hom_comp_projectiveBundleToBase X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb' T' v) (pointBundleSection_comp_projectiveBundleBaseChange_comp_toBase X E u g v h
        hvh hE hb hb'))

end AlgebraicGeometry.Space

end
