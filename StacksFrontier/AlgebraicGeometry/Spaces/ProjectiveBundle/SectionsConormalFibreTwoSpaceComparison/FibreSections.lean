module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.OverQuotientBaseChangeOfIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionsConormalFibreTwoSpaceCompat

/-!
# Sections of the fibres of `𝐏(g^*ℰ)` and `𝐏(ℰ)` and the base change of projective bundles

For `g : X' ⟶ X`, scheme points `u : T ⟶ X`, `v : T' ⟶ X'` and `h : T' ⟶ T` with
`v ≫ g = u ∘ h`, this file identifies `(u ∘ h ∘ f')^*ℰ ≅ (v ∘ f')^* g^*ℰ` with the comparison of
Stacks 03LU, and shows that the fibres, their sections and their base changes along the
projective bundle lie over the expected points.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The identification of inverse images along equal morphisms followed by the comparison of
Stacks 03LU, for two spellings of the source space. -/
theorem eqToHom_comp_modulePullbackCompIso_app_symm_hom_heq {Y Y₀ X₁ X₀ : AlgebraicSpaces B S hS}
    (hY : Y = Y₀) (a : Y ⟶ X₁) (a₀ : Y₀ ⟶ X₁) (ha : a ≍ a₀) (c : X₁ ⟶ X₀)
    (M : Modules.{u, u} B S hS X₀.1 X₀.2) {N : Modules.{u, u} B S hS Y.1 Y.2}
    {N₀ : Modules.{u, u} B S hS Y₀.1 Y₀.2} (hN : N ≍ N₀)
    (p : N = (modulePullback B S hS (a ≫ c)).obj M)
    (p₀ : N₀ = (modulePullback B S hS (a₀ ≫ c)).obj M) :
    (eqToIso p ≪≫ ((modulePullbackCompIso B S hS a c).app M).symm).hom ≍
      (eqToIso p₀ ≪≫ ((modulePullbackCompIso B S hS a₀ c).app M).symm).hom := by
  subst hY
  obtain rfl := eq_of_heq ha
  obtain rfl := eq_of_heq hN
  obtain rfl : p₀ = p := Subsingleton.elim _ _
  rfl

/-- Transporting the identification of the module along the Zariski reading of an isomorphism
`N₁ ≅ N₂` preserves the equivalence of the quotient carried by `k` with the Zariski reading of an
invertible quotient. -/
theorem overQuotient_mapIso_trans_isEquivalent {T : BigFppfOver B S hS} {Y : Scheme.{u}}
    {F : Y.Modules} [F.IsQuasicoherent] {f : (BigFppfOver.toScheme B S hS).obj T ⟶ Y}
    (D : Stacks.RelativeProj.TautologicalDatum Y F)
    {N₁ N₂ : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)}
    (hN₁ : N₁.IsQuasicoherentOnSite) (hN₂ : N₂.IsQuasicoherentOnSite)
    [i₁ : ((zariskiReadingFunctor T).obj N₁).IsQuasicoherent]
    [i₂ : ((zariskiReadingFunctor T).obj N₂).IsQuasicoherent]
    (φ : N₁ ≅ N₂) (e : (zariskiReadingFunctor T).obj N₂ ≅ (Scheme.Modules.pullback f).obj F)
    (k : (BigFppfOver.toScheme B S hS).obj T ⟶ Stacks.RelativeProj.projectiveBundle Y F)
    (hk : k ≫ Stacks.RelativeProj.projectiveBundleToBase Y F = f)
    (Q₀ : InvertibleQuotient (yonedaSpace B S hS T) N₂)
    (H : (D.overQuotient _ e k hk).IsEquivalent (zariskiReadingInvertibleQuotient hN₂ Q₀)) :
    (D.overQuotient _ ((zariskiReadingFunctor T).mapIso φ ≪≫ e) k hk).IsEquivalent
      (zariskiReadingInvertibleQuotient hN₁ (Q₀.transport φ)) := by
  obtain ⟨α, hα⟩ := H
  exact ⟨α, (Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans hα)).trans
      ((zariskiReadingFunctor T).map_comp _ _).symm))⟩

variable (X : AlgebraicSpaces B S hS) (E : SheafOfModules.{u} (structureRingSheaf B S hS X))
  {T : BigFppfOver B S hS} (u : yoneda.obj T ⟶ X.1)
  {X' : AlgebraicSpaces B S hS} (g : X' ⟶ X) {T' : BigFppfOver B S hS}
  (v : yoneda.obj T' ⟶ X'.1) (h : T' ⟶ T) (hvh : v ≫ g.hom = yoneda.map h ≫ u)

include hvh in
/-- **The identification `(u ∘ h ∘ f')^*ℰ ≅ (v ∘ f')^* g^*ℰ` is the comparison of Stacks 03LU at
the point `v ∘ f'` of `X'`**, after the identification along `u ∘ h ∘ f' = g ∘ v ∘ f'`. -/
theorem pointTwoSpaceCompIso_eq_pointCompIso {Z : BigFppfOver B S hS} (f' : Z ⟶ T') :
    pointTwoSpaceCompIso X E u g v h hvh f' =
      eqToIso (congrArg (fun y => (modulePullback B S hS (pointHom y)).obj E)
        (yoneda_map_comp_point_twoSpace X u g v h hvh f').symm) ≪≫
        pointCompIso g E Z (yoneda.map f' ≫ v) := by
  refine Iso.ext (eq_of_heq ?_)
  rw [pointTwoSpaceCompIso_eq X E u g v h hvh f']
  refine eqToHom_comp_modulePullbackCompIso_app_symm_hom_heq ?_ _ _ ?_ _ _ ?_ _ _
  · exact rfl
  · exact HEq.rfl
  · exact HEq.rfl

variable (hE : E.IsQuasicoherentOnSite) (hb : SymmetricAlgebraBounded X E)
  (hb' : SymmetricAlgebraBounded X' ((modulePullback B S hS g).obj E))

include hvh in
/-- The image of the fibre of `𝐏(g^*ℰ)` over `v` in `𝐏(ℰ)` lies over `u ∘ h ∘ f'`. -/
theorem fibreToSpace_comp_projectiveBundleBaseChange_comp_π :
    ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreToSpace T' v ≫
        (projectiveBundleBaseChange X E hE hb g hb').hom) ≫
        (projectiveBundleπ X E hE hb).hom = yoneda.map
            (((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
            hb').relativeProjPoints.fibreHom T' v) ≫ h) ≫ u :=
  ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    (projectiveBundleBaseChange_hom_comp_projectiveBundleπ_hom X E hE hb g hb')).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ g.hom)
      ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
          hb').relativeProjPoints.isPullback T' v).w).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) hvh).trans (Category.assoc _ _ _).symm)))))).trans
    (congrArg (· ≫ u) (yoneda.map_comp _ _).symm)


include u h hvh hE hb hb' in
/-- The base change of the fibre of `𝐏(g^*ℰ)` over `v`, read in `𝐏((u^*ℰ)_Zar)`, lies over
`f' ≫ h`. -/
theorem pointFibreProjectiveBundleIso_hom_comp_projectiveBundleBaseChange_comp_toBase :
    haveI := isQuasicoherent_pointZariskiModule X E hE T u
    haveI := isQuasicoherent_pointZariskiModule X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) T' v
    ((pointFibreProjectiveBundleIso X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' T' v).hom ≫
        (Stacks.RelativeProj.projectiveBundleBaseChange ((BigFppfOver.toScheme B S hS).map h)
        (pointZariskiModule X E T u) (pointZariskiModule X' ((modulePullback B S hS g).obj E) T' v)
        (pointZariskiModuleTwoSpaceIso X E hE g u v h hvh))) ≫
        Stacks.RelativeProj.projectiveBundleToBase _ (pointZariskiModule X E T u) =
        (BigFppfOver.toScheme B S hS).map (((projectiveBundleSituation X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb').relativeProjPoints.fibreHom T' v) ≫ h) := by
  have := isQuasicoherent_pointZariskiModule X E hE T u
  have := isQuasicoherent_pointZariskiModule X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) T' v
  exact (Category.assoc _ _ _).trans ((congrArg ((pointFibreProjectiveBundleIso X'
      ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
      hE g) hb' T' v).hom ≫ ·)
    (Stacks.RelativeProj.projectiveBundleBaseChange_comp_projectiveBundleToBase
        ((BigFppfOver.toScheme B S hS).map h) (pointZariskiModule X E T u)
        (pointZariskiModule X' ((modulePullback B S hS g).obj E) T' v)
        (pointZariskiModuleTwoSpaceIso X E hE g u v h hvh))).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (BigFppfOver.toScheme B S hS).map h)
        (pointFibreProjectiveBundleIso_hom_comp_projectiveBundleToBase X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb' T' v)).trans
      ((BigFppfOver.toScheme B S hS).map_comp _ _).symm)))

include u h hvh hE hb hb' in
/-- The comparison of fibres, read in `𝐏((u^*ℰ)_Zar)`, lies over `f' ≫ h`. -/
theorem sectionFibreBaseChangeComparison_comp_pointFibreProjectiveBundleIso_hom_comp_toBase :
    haveI := isQuasicoherent_pointZariskiModule X E hE T u
    haveI := isQuasicoherent_pointZariskiModule X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) T' v
    ((BigFppfOver.toScheme B S hS).map (sectionFibreBaseChangeComparison X E hE hb g hb' u v h hvh)
        ≫ (pointFibreProjectiveBundleIso X E hE hb T u).hom) ≫
        Stacks.RelativeProj.projectiveBundleToBase _ (pointZariskiModule X E T u) =
        (BigFppfOver.toScheme B S hS).map (((projectiveBundleSituation X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb').relativeProjPoints.fibreHom T' v) ≫ h) := by
  exact (Category.assoc _ _ _).trans ((congrArg ((BigFppfOver.toScheme B S hS).map
      (sectionFibreBaseChangeComparison X E hE hb g hb' u v h hvh) ≫ ·)
    (pointFibreProjectiveBundleIso_hom_comp_projectiveBundleToBase X E hE hb T u)).trans
    (((BigFppfOver.toScheme B S hS).map_comp _ _).symm.trans
        (congrArg (BigFppfOver.toScheme B S hS).map
      (sectionFibreBaseChangeComparison_comp_fibreHom X E hE hb g hb' u v h hvh))))

include u h hE hb' in
/-- The identification of the fibre of `𝐏(g^*ℰ)` over `v` with `𝐏((v^*g^*ℰ)_Zar)` is the
section of the fibre given by its inclusion, followed by the base change of projective bundles. -/
theorem pointFibreProjectiveBundleIso_hom_eq_pointBundleSection_comp :
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
    (pointFibreProjectiveBundleIso X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' T' v).hom =
        (pointRelativeProjSection X' ((modulePullback B S hS g).obj E)
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
        hb').relativeProjPoints.fibreHom T' v))) := by
  have := isQuasicoherent_pointZariskiModule X E hE T' (yoneda.map h ≫ u)
  exact ((Category.id_comp _).symm.trans (congrArg
      (· ≫ (pointFibreProjectiveBundleIso X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' T' v).hom)
      ((BigFppfOver.toScheme B S hS).map_id _).symm)).trans
    (pointBundleSection_comp_projectiveBundleBaseChange X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' v
        (𝟙 ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibre T' v)) ((projectiveBundleSituation X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb').relativeProjPoints.fibreHom T' v)
      (Category.id_comp _) (⟨(projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
          hb').relativeProjPoints.fibreToSpace T' v,
          ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
          hb').relativeProjPoints.isPullback T' v).w⟩ :
          {w : yoneda.obj ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
          hb').relativeProjPoints.fibre T' v) ⟶ (relativeProjSymmetricAlgebra X'
          ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X
          E hE g) hb').1 // w ≫ (projectiveBundleπ X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').hom = yoneda.map
          ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
          hb').relativeProjPoints.fibreHom T' v) ≫ v})
      ((congrArg (· ≫ _) (CategoryTheory.Functor.map_id yoneda _)).trans (Category.id_comp _))).symm

include u h hvh hE hb hb' in
/-- The section of the fibre of `𝐏(g^*ℰ)` over `v`, base changed, lies over `f'`. -/
theorem pointBundleSection_comp_projectiveBundleBaseChange_comp_toBase :
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
    ((pointRelativeProjSection X' ((modulePullback B S hS g).obj E)
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
        hb').relativeProjPoints.fibreHom T' v)))) ≫ Stacks.RelativeProj.projectiveBundleToBase _
        (pointZariskiModule X' ((modulePullback B S hS g).obj E) T' v) =
        (BigFppfOver.toScheme B S hS).map ((projectiveBundleSituation X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb').relativeProjPoints.fibreHom T' v) := by
  have := isQuasicoherent_pointZariskiModule X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) T' v
  exact (congrArg (· ≫ Stacks.RelativeProj.projectiveBundleToBase _
      (pointZariskiModule X' ((modulePullback B S hS g).obj E) T' v))
      (pointFibreProjectiveBundleIso_hom_eq_pointBundleSection_comp X E u g v h hE hb').symm).trans
      (pointFibreProjectiveBundleIso_hom_comp_projectiveBundleToBase X'
      ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
      hE g) hb' T' v)

include u h hvh hE hb hb' in
/-- The section of the fibre over `u ∘ h ∘ f'` given by the comparison of fibres, base changed,
is the comparison of fibres read in `𝐏((u^*ℰ)_Zar)`. -/
theorem pointBundleSection_twoSpace_comp_projectiveBundleBaseChange :
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
        hb').relativeProjPoints.fibreHom T' v) ≫ h) ≫ u})).1 ≫
        (Stacks.RelativeProj.projectiveBundleBaseChange
        ((BigFppfOver.toScheme B S hS).map (((projectiveBundleSituation X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb').relativeProjPoints.fibreHom T' v) ≫ h)) (pointZariskiModule X E T u)
        (pointZariskiModule X E ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibre T' v) (yoneda.map
        (((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v) ≫ h) ≫ u))
        (pointZariskiModuleBaseChangeIso X E hE u (((projectiveBundleSituation X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb').relativeProjPoints.fibreHom T' v) ≫ h))) =
        ((BigFppfOver.toScheme B S hS).map (sectionFibreBaseChangeComparison X E hE hb g hb' u v h
        hvh) ≫ (pointFibreProjectiveBundleIso X E hE hb T u).hom) := by
  exact pointBundleSection_comp_projectiveBundleBaseChange X E hE hb u
      (sectionFibreBaseChangeComparison X E hE hb g hb' u v h hvh)
      (((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
      hb').relativeProjPoints.fibreHom T' v) ≫ h)
    (sectionFibreBaseChangeComparison_comp_fibreHom X E hE hb g hb' u v h hvh)
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
        hb').relativeProjPoints.fibreHom T' v) ≫ h) ≫ u})
    (map_sectionFibreBaseChangeComparison_comp_fibreToSpace X E hE hb g hb' u v h hvh)

include u h hvh hE hb hb' in
/-- The section of the fibre over `u ∘ h ∘ f'`, base changed, lies over `f' ≫ h`. -/
theorem pointBundleSection_twoSpace_comp_projectiveBundleBaseChange_comp_toBase :
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
    ((pointRelativeProjSection X E hE hb ((projectiveBundleSituation X'
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
        hb').relativeProjPoints.fibreHom T' v) ≫ h) ≫ u})).1 ≫
        (Stacks.RelativeProj.projectiveBundleBaseChange
        ((BigFppfOver.toScheme B S hS).map (((projectiveBundleSituation X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb').relativeProjPoints.fibreHom T' v) ≫ h)) (pointZariskiModule X E T u)
        (pointZariskiModule X E ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibre T' v) (yoneda.map
        (((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v) ≫ h) ≫ u))
        (pointZariskiModuleBaseChangeIso X E hE u (((projectiveBundleSituation X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb').relativeProjPoints.fibreHom T' v) ≫ h)))) ≫
        Stacks.RelativeProj.projectiveBundleToBase _ (pointZariskiModule X E T u) =
        (BigFppfOver.toScheme B S hS).map (((projectiveBundleSituation X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E
        hE g) hb').relativeProjPoints.fibreHom T' v) ≫ h) := by
  have := isQuasicoherent_pointZariskiModule X E hE T u
  exact (congrArg (· ≫ Stacks.RelativeProj.projectiveBundleToBase _ (pointZariskiModule X E T u))
      (pointBundleSection_twoSpace_comp_projectiveBundleBaseChange X E u g v h hvh hE hb hb')).trans
      (sectionFibreBaseChangeComparison_comp_pointFibreProjectiveBundleIso_hom_comp_toBase X E u g v
      h hvh hE hb hb')

end AlgebraicGeometry.Space

end
