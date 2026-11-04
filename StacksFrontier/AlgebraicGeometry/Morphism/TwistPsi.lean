module

public import StacksFrontier.AlgebraicGeometry.Morphism.TwistMulProof
public import StacksFrontier.AlgebraicGeometry.SectionRingBaseChange.SectionPullRestrict
public import StacksFrontier.AlgebraicGeometry.ProjTwistTheta.DegreeSection
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ThetaChartLaws

/-!
# Tag 07ZG: the maps on twists on the homogeneous sections

Let `ψ : A ⟶ B` be a homomorphism of quasi-coherent graded `𝒪_S`-algebras, `r_ψ : U(ψ) ⟶ Proj_S(A)`
the morphism of [Stacks, Tag 07ZG] and `θ_d : r_ψ^* 𝒪(d) ⟶ 𝒪(d)|_{U(ψ)}` its map on twists
(`Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistMap`). For a homogeneous section `a` of
`A_d` over an open `V` of the base, `θ_d` carries the inverse image of the section `ψ_A(a)` of
`𝒪_{Proj_S(A)}(d)` attached to `a` ([Stacks, Tag 01NR]) to the restriction of the section
`ψ_B(ψ(a))` of `𝒪_{Proj_S(B)}(d)`. This is part (1) of [Stacks, Tag 01MY] read through the charts.

## Main results

* `Stacks.AlgebraicGeometry.TwistMulLeg.legIso_hom_app_unitApp`: the leg identification on the
  inverse image of a section.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.chartSourceIso_unitApp_psiU`,
  `…chartTargetIso_unitApp_psiU`, `…pullback_twistMap_degreeSection`: the three factors of `θ_d`
  over a piece of `U(ψ)`, on the section attached to a homogeneous element, and
  `…piece_chase`, the chase that assembles them.

## References

* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.SectionRingBaseChange (unitApp unitApp_naturality unitApp_map
  hom_app_map map_map_homOfLE iso_hom_app_map_inv_app iso_inv_app_map_hom_app)
open Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul (hom_app_inv_app)

universe u

namespace Stacks.AlgebraicGeometry.TwistMulLeg

variable {W Z Y T V : Scheme.{u}}

/-- The value of a composite of morphisms of modules on a section. Stated once in general, so that
its instances are checked by unification rather than by unfolding the composite. -/
theorem app_comp_apply {X : Scheme.{u}} {M N K : X.Modules} (f : M ⟶ N) (g : N ⟶ K)
    (O : X.Opens) (x : Γ(M, O)) : (f ≫ g).app O x = g.app O (f.app O x) := rfl

/-- `⊤ ≤ ρ⁻¹(m⁻¹(⊤))`, as a constant: its uses are then checked without reducing the preimages. -/
theorem top_le_preimage₂ (ρ : W ⟶ T) (m : T ⟶ V) : (⊤ : W.Opens) ≤ ρ ⁻¹ᵁ m ⁻¹ᵁ (⊤ : V.Opens) := by
  simp

/-- **Transport along an equality of morphisms, on the inverse image of a section.** -/
theorem pullbackCongr_hom_app_unitApp {f f' : W ⟶ Y} (e : f = f') (M : Y.Modules) (O : Y.Opens)
    (s : Γ(M, O)) :
    ((Scheme.Modules.pullbackCongr e).hom.app M).app (f ⁻¹ᵁ O) (unitApp f M O s) =
      ((Scheme.Modules.pullback f').obj M).presheaf.map (homOfLE (by rw [e])).op
        (unitApp f' M O s) := by
  subst e
  have : (homOfLE (le_refl (f ⁻¹ᵁ O))).op = 𝟙 _ := Subsingleton.elim _ _
  rw [this, CategoryTheory.Functor.map_id]
  rfl

/-- **The pseudofunctoriality isomorphism of the inverse image, on the inverse image of a
section.** -/
theorem pullbackComp_hom_app_unitApp (f : W ⟶ Z) (g : Z ⟶ Y) (M : Y.Modules) (O : Y.Opens)
    (s : Γ(M, O)) :
    ((Scheme.Modules.pullbackComp f g).hom.app M).app (f ⁻¹ᵁ g ⁻¹ᵁ O)
        (unitApp f ((Scheme.Modules.pullback g).obj M) (g ⁻¹ᵁ O) (unitApp g M O s)) =
      unitApp (f ≫ g) M O s := by
  have key : ((Scheme.Modules.pullbackComp f g).inv.app M).app ((f ≫ g) ⁻¹ᵁ O)
      (unitApp (f ≫ g) M O s) =
      unitApp f ((Scheme.Modules.pullback g).obj M) (g ⁻¹ᵁ O) (unitApp g M O s) :=
    Scheme.Modules.pullbackComp_inv_unit f g M O s
  rw [← key]
  exact hom_app_inv_app ((Scheme.Modules.pullbackComp f g).app M) _ _

/-- **The leg identification on the inverse image of a section.** For `k ≫ h = ρ ≫ hU ≫ c` and
`χ : c^* M ≅ N` carrying the inverse image of `s` to `t`, the leg identification carries the
inverse image of `s` along `k ≫ h` to the inverse image of `t` along `ρ ≫ hU`. -/
theorem legIso_hom_app_unitApp (k : W ⟶ Z) (h : Z ⟶ Y) (ρ : W ⟶ T) (hU : T ⟶ V) (c : V ⟶ Y)
    (e : k ≫ h = ρ ≫ hU ≫ c) {M : Y.Modules} {N : V.Modules}
    (χ : (Scheme.Modules.pullback c).obj M ≅ N) (O : Y.Opens) (s : Γ(M, O))
    (t : Γ(N, c ⁻¹ᵁ O)) (ht : χ.hom.app (c ⁻¹ᵁ O) (unitApp c M O s) = t) :
    (legIso k h ρ hU c e χ).hom.app (k ⁻¹ᵁ h ⁻¹ᵁ O)
        (unitApp k ((Scheme.Modules.pullback h).obj M) (h ⁻¹ᵁ O) (unitApp h M O s)) =
      ((Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback hU).obj N)).presheaf.map
        (homOfLE (by
          change (k ≫ h) ⁻¹ᵁ O ≤ (ρ ≫ hU ≫ c) ⁻¹ᵁ O
          rw [e])).op
        (unitApp ρ ((Scheme.Modules.pullback hU).obj N) (hU ⁻¹ᵁ c ⁻¹ᵁ O)
          (unitApp hU N (c ⁻¹ᵁ O) t)) := by
  have hΦ : ((Scheme.Modules.pullbackComp hU c).inv.app M ≫
        (Scheme.Modules.pullback hU).map χ.hom).app ((hU ≫ c) ⁻¹ᵁ O) (unitApp (hU ≫ c) M O s) =
      unitApp hU N (c ⁻¹ᵁ O) t := by
    rw [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply]
    have e1 := Scheme.Modules.pullbackComp_inv_unit hU c M O s
    refine (congrArg (fun z => ((Scheme.Modules.pullback hU).map χ.hom).app _ z) e1).trans ?_
    refine (unitApp_naturality hU χ.hom (c ⁻¹ᵁ O) _).trans ?_
    exact congrArg (unitApp hU N (c ⁻¹ᵁ O)) ht
  have s1 := pullbackComp_hom_app_unitApp k h M O s
  have s2 := pullbackCongr_hom_app_unitApp e M O s
  have s3 := hom_app_map ((Scheme.Modules.pullbackComp ρ (hU ≫ c)).inv.app M)
    (show (k ≫ h) ⁻¹ᵁ O ≤ (ρ ≫ hU ≫ c) ⁻¹ᵁ O by rw [e]) (unitApp (ρ ≫ hU ≫ c) M O s)
  have s4 := Scheme.Modules.pullbackComp_inv_unit ρ (hU ≫ c) M O s
  have s5 := hom_app_map ((Scheme.Modules.pullback ρ).map
    ((Scheme.Modules.pullbackComp hU c).inv.app M ≫ (Scheme.Modules.pullback hU).map χ.hom))
    (show (k ≫ h) ⁻¹ᵁ O ≤ (ρ ≫ hU ≫ c) ⁻¹ᵁ O by rw [e])
    (unitApp ρ ((Scheme.Modules.pullback (hU ≫ c)).obj M) ((hU ≫ c) ⁻¹ᵁ O)
      (unitApp (hU ≫ c) M O s))
  have s6 := unitApp_naturality ρ
    ((Scheme.Modules.pullbackComp hU c).inv.app M ≫ (Scheme.Modules.pullback hU).map χ.hom)
    ((hU ≫ c) ⁻¹ᵁ O) (unitApp (hU ≫ c) M O s)
  let Φ' := (Scheme.Modules.pullback ρ).map
    ((Scheme.Modules.pullbackComp hU c).inv.app M ≫ (Scheme.Modules.pullback hU).map χ.hom)
  let C3 := (Scheme.Modules.pullbackComp ρ (hU ≫ c)).inv.app M
  let C2 := (Scheme.Modules.pullbackCongr e).hom.app M
  have hle : (k ≫ h) ⁻¹ᵁ O ≤ (ρ ≫ hU ≫ c) ⁻¹ᵁ O := by rw [e]
  show Φ'.app ((k ≫ h) ⁻¹ᵁ O) (C3.app ((k ≫ h) ⁻¹ᵁ O) (C2.app ((k ≫ h) ⁻¹ᵁ O)
      (((Scheme.Modules.pullbackComp k h).hom.app M).app (k ⁻¹ᵁ h ⁻¹ᵁ O)
        (unitApp k ((Scheme.Modules.pullback h).obj M) (h ⁻¹ᵁ O) (unitApp h M O s))))) = _
  refine (congrArg (fun z => Φ'.app ((k ≫ h) ⁻¹ᵁ O) (C3.app ((k ≫ h) ⁻¹ᵁ O)
    (C2.app ((k ≫ h) ⁻¹ᵁ O) z))) s1).trans ?_
  refine (congrArg (fun z => Φ'.app ((k ≫ h) ⁻¹ᵁ O) (C3.app ((k ≫ h) ⁻¹ᵁ O) z)) s2).trans ?_
  refine (congrArg (fun z => Φ'.app ((k ≫ h) ⁻¹ᵁ O) z) s3).trans ?_
  refine (congrArg (fun z => Φ'.app ((k ≫ h) ⁻¹ᵁ O)
    (((Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback (hU ≫ c)).obj M)).presheaf.map
      (homOfLE hle).op z)) s4).trans ?_
  refine s5.trans ?_
  refine (congrArg (fun z =>
    ((Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback hU).obj N)).presheaf.map
      (homOfLE hle).op z) s6).trans ?_
  exact congrArg (fun z =>
    ((Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback hU).obj N)).presheaf.map
      (homOfLE hle).op (unitApp ρ ((Scheme.Modules.pullback hU).obj N) (hU ⁻¹ᵁ c ⁻¹ᵁ O) z)) hΦ

/-- **Sections agreeing after pulling back along an open immersion agree on its image.** -/
theorem eq_of_unitApp_restrict {C : Scheme.{u}} (k : C ⟶ Y) [IsOpenImmersion k] {N : Y.Modules}
    {W₀ : Y.Opens} (hO : k ''ᵁ ⊤ ≤ W₀) (hT : (⊤ : C.Opens) ≤ k ⁻¹ᵁ W₀) (z z' : Γ(N, W₀))
    (h : ((Scheme.Modules.pullback k).obj N).presheaf.map (homOfLE hT).op (unitApp k N W₀ z) =
      ((Scheme.Modules.pullback k).obj N).presheaf.map (homOfLE hT).op (unitApp k N W₀ z')) :
    N.presheaf.map (homOfLE hO).op z = N.presheaf.map (homOfLE hO).op z' := by
  have hW : k ''ᵁ (k ⁻¹ᵁ (k ''ᵁ ⊤)) = k ''ᵁ ⊤ := by rw [Scheme.Hom.preimage_image_eq]
  have hinj : Function.Injective (unitApp k N (k ''ᵁ ⊤)) :=
    (Stacks.AlgebraicGeometry.SectionRingBaseChange.bijective_pullbackUnit_of_isOpenImmersion k N
      (k ''ᵁ ⊤) hW).1
  have hT' : (⊤ : C.Opens) ≤ k ⁻¹ᵁ (k ''ᵁ ⊤) := by rw [Scheme.Hom.preimage_image_eq]
  have hres : Function.Injective (((Scheme.Modules.pullback k).obj N).presheaf.map
      (homOfLE hT').op) :=
    (Stacks.AlgebraicGeometry.SectionRingBaseChange.bijective_map_homOfLE_of_eq _ hT'
      le_top).1
  refine hinj ?_
  rw [unitApp_map, unitApp_map]
  refine hres ?_
  rw [map_map_homOfLE _ hT' (k.preimage_mono hO) hT, map_map_homOfLE _ hT' (k.preimage_mono hO) hT]
  exact h

/-- **A restriction chase along the pullback to a piece.** If, after pulling back along `k`,
`θ` carries the restriction of `p` to `Wa` to the restriction of `q` to `Wb`, then it carries `p`
to the restriction of `q` to `W₀`, read on all of the source of `k`. -/
theorem chase_restrict {C : Scheme.{u}} (k : C ⟶ Y) {M N : Y.Modules} (θ : M ⟶ N)
    {W₀ Wa Wb W₂ : Y.Opens} (p : Γ(M, W₀)) (q : Γ(N, W₂)) (ha : Wa ≤ W₀) (hb : Wb ≤ W₂)
    (h02 : W₀ ≤ W₂) (hTA : (⊤ : C.Opens) ≤ k ⁻¹ᵁ Wa) (hTB : (⊤ : C.Opens) ≤ k ⁻¹ᵁ Wb)
    (hT0 : (⊤ : C.Opens) ≤ k ⁻¹ᵁ W₀)
    (hpiece : ((Scheme.Modules.pullback k).obj N).presheaf.map (homOfLE hTA).op
        (((Scheme.Modules.pullback k).map θ).app (k ⁻¹ᵁ Wa)
          (unitApp k M Wa (M.presheaf.map (homOfLE ha).op p))) =
      ((Scheme.Modules.pullback k).obj N).presheaf.map (homOfLE hTB).op
        (unitApp k N Wb (N.presheaf.map (homOfLE hb).op q))) :
    ((Scheme.Modules.pullback k).obj N).presheaf.map (homOfLE hT0).op
        (unitApp k N W₀ (θ.app W₀ p)) =
      ((Scheme.Modules.pullback k).obj N).presheaf.map (homOfLE hT0).op
        (unitApp k N W₀ (N.presheaf.map (homOfLE h02).op q)) := by
  rw [unitApp_map k M ha p, hom_app_map ((Scheme.Modules.pullback k).map θ) (k.preimage_mono ha),
    map_map_homOfLE _ hTA (k.preimage_mono ha) hT0, unitApp_map k N hb q,
    map_map_homOfLE _ hTB (k.preimage_mono hb) (hTB.trans (k.preimage_mono hb))] at hpiece
  rw [← unitApp_naturality, unitApp_map k N h02 q,
    map_map_homOfLE _ hT0 (k.preimage_mono h02) (hT0.trans (k.preimage_mono h02))]
  exact hpiece

/-- A section is determined by its restrictions to the members of a covering. -/
theorem eq_of_restrict_cover {N : Y.Modules} {ι : Type u} {W₀ : Y.Opens} (Wk : ι → Y.Opens)
    (hk : ∀ k, Wk k ≤ W₀) (hcov : W₀ ≤ ⨆ k, Wk k) {z z' : Γ(N, W₀)}
    (h : ∀ k, N.presheaf.map (homOfLE (hk k)).op z = N.presheaf.map (homOfLE (hk k)).op z') :
    z = z' :=
  TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf N.isSheaf Wk hk hcov h

end Stacks.AlgebraicGeometry.TwistMulLeg

namespace Stacks.AlgebraicGeometry.Tag07ZGTwist

open Stacks.AlgebraicGeometry.RelativeProj Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain Stacks.AlgebraicGeometry.Tag07ZGMorphism
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap (psiU Otw twD)
open Stacks.AlgebraicGeometry.ProjShared (mapDomain)
open Stacks.AlgebraicGeometry.ProjTwistChain (mapHom)
open Stacks.AlgebraicGeometry.ProjTwistCompare (twistMap projMapData)
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf degreeSection)

variable {S : Scheme.{u}}

/-- **The chart identification of [Stacks, Tag 01NR] on the section attached to a homogeneous
element**: it carries the inverse image along the chart over `U` of `ψ_A(a)` to the restriction of
the degree section of `a` on `Proj Γ(U, A)`. -/
theorem chartTwistIso_hom_app_unitApp_psiU (A : SheafGradedAlgebra S) (d : ℕ) (U : S.affineOpens)
    (a : Γ(A.piece (d : ℤ), U.1)) :
    (chartTwistIso A d U).hom.app ((relativeProj A).chart U.1 U.2 ⁻¹ᵁ
        ((relativeProj A).toBase ⁻¹ᵁ U.1))
        (unitApp ((relativeProj A).chart U.1 U.2) (relativeTwist A d)
          ((relativeProj A).toBase ⁻¹ᵁ U.1) (psiU A d U.1 a)) =
      (twistingSheaf (A.grading U.1) d).val.map (homOfLE le_top).op
        (degreeSection (A.grading U.1) d
          ⟨DirectSum.of (A.sectionPieces U.1) d a, A.of_mem_grading U.1 a⟩) := by
  let c := (relativeProj A).chart U.1 U.2
  let O := (relativeProj A).toBase ⁻¹ᵁ U.1
  let e := (Scheme.Modules.restrictFunctorIsoPullback c).app (relativeTwist A d)
  have hu : unitApp c (relativeTwist A d) O (psiU A d U.1 a) =
      e.hom.app (c ⁻¹ᵁ O) ((relativeTwist A d).presheaf.map (homOfLE (c.image_preimage_le O)).op
        (psiU A d U.1 a)) :=
    (congrArg (fun φ => Scheme.Modules.Hom.app φ O (psiU A d U.1 a))
      (Stacks.AlgebraicGeometry.ProjTwistTheta.restrictUnit_comp_map_restrictFunctorIsoPullback c
        (relativeTwist A d))).symm
  have hcan : e.inv.app (c ⁻¹ᵁ O) (unitApp c (relativeTwist A d) O (psiU A d U.1 a)) =
      (relativeTwist A d).presheaf.map (homOfLE (c.image_preimage_le O)).op (psiU A d U.1 a) :=
    (congrArg (fun z => e.inv.app (c ⁻¹ᵁ O) z) hu).trans (hom_app_inv_app e.symm _ _)
  have h2 :=
    Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap.chartIso_hom_psiU
      U.1 U.2 d (c ⁻¹ᵁ O) a
  have h3 : (chartTwistIso A d U).hom.app (c ⁻¹ᵁ O)
      (unitApp c (relativeTwist A d) O (psiU A d U.1 a)) =
      ((twD A).chartData.chartIso U.1 U.2 d).hom.app (c ⁻¹ᵁ O)
        (e.inv.app (c ⁻¹ᵁ O) (unitApp c (relativeTwist A d) O (psiU A d U.1 a))) := by
    simp only [chartTwistIso]
    rfl
  exact h3.trans ((congrArg (fun z => ((twD A).chartData.chartIso U.1 U.2 d).hom.app (c ⁻¹ᵁ O) z)
    hcan).trans h2)

/-- **A leg identification over the chart over `U`, on the section attached to a homogeneous
element**, read on the whole source: the inverse image along `k ≫ h` of `ψ_X(x)` goes to the
inverse image along `ρ ≫ m` of the degree section of `x`. -/
theorem legIso_unitApp_psiU (X : SheafGradedAlgebra S) (d : ℕ) (U : S.affineOpens)
    (x : Γ(X.piece (d : ℤ), U.1)) {W Z T : Scheme.{u}} (k : W ⟶ Z)
    (h : Z ⟶ (relativeProj X).scheme) (ρ : W ⟶ T) (m : T ⟶ AlgebraicGeometry.Proj (X.grading U.1))
    (e : k ≫ h = ρ ≫ m ≫ (relativeProj X).chart U.1 U.2)
    (hT : (⊤ : W.Opens) ≤ k ⁻¹ᵁ h ⁻¹ᵁ ((relativeProj X).toBase ⁻¹ᵁ U.1)) :
    ((Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback m).obj
        (twistingSheaf (X.grading U.1) d))).presheaf.map (homOfLE hT).op
      ((TwistMulLeg.legIso k h ρ m ((relativeProj X).chart U.1 U.2) e
          (chartTwistIso X d U)).hom.app (k ⁻¹ᵁ h ⁻¹ᵁ ((relativeProj X).toBase ⁻¹ᵁ U.1))
        (unitApp k ((Scheme.Modules.pullback h).obj (relativeTwist X d))
          (h ⁻¹ᵁ ((relativeProj X).toBase ⁻¹ᵁ U.1))
          (unitApp h (relativeTwist X d) ((relativeProj X).toBase ⁻¹ᵁ U.1) (psiU X d U.1 x)))) =
      ((Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback m).obj
        (twistingSheaf (X.grading U.1) d))).presheaf.map
        (homOfLE (TwistMulLeg.top_le_preimage₂ ρ m)).op
        (unitApp ρ ((Scheme.Modules.pullback m).obj (twistingSheaf (X.grading U.1) d)) (m ⁻¹ᵁ ⊤)
          (unitApp m (twistingSheaf (X.grading U.1) d) ⊤
            (degreeSection (X.grading U.1) d
              ⟨DirectSum.of (X.sectionPieces U.1) d x, X.of_mem_grading U.1 x⟩))) := by
  let O := (relativeProj X).toBase ⁻¹ᵁ U.1
  let c := (relativeProj X).chart U.1 U.2
  let N := twistingSheaf (X.grading U.1) d
  let dS := degreeSection (X.grading U.1) d
    ⟨DirectSum.of (X.sectionPieces U.1) d x, X.of_mem_grading U.1 x⟩
  have ht := chartTwistIso_hom_app_unitApp_psiU X d U x
  have g1 := TwistMulLeg.legIso_hom_app_unitApp k h ρ m c e (chartTwistIso X d U) O
    (psiU X d U.1 x) _ ht
  have g2 := unitApp_map m N (le_top : c ⁻¹ᵁ O ≤ ⊤) dS
  have g3 := unitApp_map ρ ((Scheme.Modules.pullback m).obj N)
    (m.preimage_mono (le_top : c ⁻¹ᵁ O ≤ ⊤)) (unitApp m N ⊤ dS)
  have hle : (k ≫ h) ⁻¹ᵁ O ≤ (ρ ≫ m ≫ c) ⁻¹ᵁ O := by rw [e]
  refine (congrArg (fun z => ((Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback m).obj
      N)).presheaf.map (homOfLE hT).op z) g1).trans ?_
  refine (congrArg (fun z => ((Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback m).obj
      N)).presheaf.map (homOfLE hT).op (((Scheme.Modules.pullback ρ).obj
        ((Scheme.Modules.pullback m).obj N)).presheaf.map (homOfLE hle).op
        (unitApp ρ ((Scheme.Modules.pullback m).obj N) (m ⁻¹ᵁ c ⁻¹ᵁ O) z))) g2).trans ?_
  refine (congrArg (fun z => ((Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback m).obj
      N)).presheaf.map (homOfLE hT).op (((Scheme.Modules.pullback ρ).obj
        ((Scheme.Modules.pullback m).obj N)).presheaf.map (homOfLE hle).op z)) g3).trans ?_
  exact (map_map_homOfLE _ hT hle (hT.trans hle) _).trans
    (map_map_homOfLE _ (hT.trans hle) _ (TwistMulLeg.top_le_preimage₂ ρ m) _)

variable {A B : SheafGradedAlgebra S} (ψ : SheafGradedAlgebraHom A B)

/-- The inverse image of `θ_d` along the inclusion of a piece, on sections. -/
theorem pullback_relativeTwistMap_app (d : ℤ) (U : S.affineOpens)
    (W : (chartImage ψ U).toScheme.Opens)
    (x : Γ((Scheme.Modules.pullback (pieceIncl ψ U)).obj
      ((Scheme.Modules.pullback (relativeMapHom ψ)).obj (relativeTwist A d)), W)) :
    ((Scheme.Modules.pullback (pieceIncl ψ U)).map (relativeTwistMap ψ d)).app W x =
      (chartTargetIso ψ d U).inv.app W
        (((Scheme.Modules.pullback (chartDomainIso ψ U).inv).map
          (twistMap (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) d)).app W
          ((chartSourceIso ψ d U).hom.app W x)) :=
  (congrArg (fun φ => Scheme.Modules.Hom.app φ W x) (pullback_relativeTwistMap_eq_comp ψ d U)).trans
    ((TwistMulLeg.app_comp_apply _ _ W x).trans
      (TwistMulLeg.app_comp_apply _ _ W ((chartSourceIso ψ d U).hom.app W x)))

/-- The source identification of `θ_d` on the section attached to a homogeneous element. -/
theorem chartSourceIso_unitApp_psiU (d : ℕ) (U : S.affineOpens) (a : Γ(A.piece (d : ℤ), U.1))
    (hTA : (⊤ : (chartImage ψ U).toScheme.Opens) ≤
      pieceIncl ψ U ⁻¹ᵁ relativeMapHom ψ ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ U.1)) :
    ((Scheme.Modules.pullback (chartDomainIso ψ U).inv).obj ((Scheme.Modules.pullback
        (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))).obj
          (twistingSheaf (A.grading U.1) d))).presheaf.map (homOfLE hTA).op
      ((chartSourceIso ψ d U).hom.app
        (pieceIncl ψ U ⁻¹ᵁ relativeMapHom ψ ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ U.1))
        (unitApp (pieceIncl ψ U) ((Scheme.Modules.pullback (relativeMapHom ψ)).obj
            (relativeTwist A d)) (relativeMapHom ψ ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ U.1))
          (unitApp (relativeMapHom ψ) (relativeTwist A d)
          ((relativeProj A).toBase ⁻¹ᵁ U.1) (psiU A d U.1 a)))) =
      ((Scheme.Modules.pullback (chartDomainIso ψ U).inv).obj ((Scheme.Modules.pullback
        (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))).obj
          (twistingSheaf (A.grading U.1) d))).presheaf.map
        (homOfLE (TwistMulLeg.top_le_preimage₂ (chartDomainIso ψ U).inv
          (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)))).op
        (unitApp (chartDomainIso ψ U).inv ((Scheme.Modules.pullback
          (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))).obj
            (twistingSheaf (A.grading U.1) d))
          ((mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)) ⁻¹ᵁ ⊤)
          (unitApp (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))
            (twistingSheaf (A.grading U.1) d) ⊤ (degreeSection (A.grading U.1) d
              ⟨DirectSum.of (A.sectionPieces U.1) d a, A.of_mem_grading U.1 a⟩))) :=
  by
  rw [chartSourceIso_eq_legIso]
  exact legIso_unitApp_psiU A d U a (pieceIncl ψ U) (relativeMapHom ψ) (chartDomainIso ψ U).inv
    (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))
    (pieceIncl_comp_relativeMapHom ψ U) hTA

/-- The target identification of `θ_d` on the section attached to a homogeneous element. -/
theorem chartTargetIso_unitApp_psiU (d : ℕ) (U : S.affineOpens) (b : Γ(B.piece (d : ℤ), U.1))
    (hTB : (⊤ : (chartImage ψ U).toScheme.Opens) ≤
      pieceIncl ψ U ⁻¹ᵁ ψ.relativeMapDomain.ι ⁻¹ᵁ ((relativeProj B).toBase ⁻¹ᵁ U.1)) :
    ((Scheme.Modules.pullback (chartDomainIso ψ U).inv).obj ((Scheme.Modules.pullback
        (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι).obj
          (twistingSheaf (B.grading U.1) d))).presheaf.map (homOfLE hTB).op
      ((chartTargetIso ψ d U).hom.app
        (pieceIncl ψ U ⁻¹ᵁ ψ.relativeMapDomain.ι ⁻¹ᵁ ((relativeProj B).toBase ⁻¹ᵁ U.1))
        (unitApp (pieceIncl ψ U) ((Scheme.Modules.pullback ψ.relativeMapDomain.ι).obj
            (relativeTwist B d)) (ψ.relativeMapDomain.ι ⁻¹ᵁ ((relativeProj B).toBase ⁻¹ᵁ U.1))
          (unitApp ψ.relativeMapDomain.ι (relativeTwist B d)
          ((relativeProj B).toBase ⁻¹ᵁ U.1) (psiU B d U.1 b)))) =
      ((Scheme.Modules.pullback (chartDomainIso ψ U).inv).obj ((Scheme.Modules.pullback
        (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι).obj
          (twistingSheaf (B.grading U.1) d))).presheaf.map
        (homOfLE (TwistMulLeg.top_le_preimage₂ (chartDomainIso ψ U).inv
          (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι)).op
        (unitApp (chartDomainIso ψ U).inv ((Scheme.Modules.pullback
          (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι).obj
            (twistingSheaf (B.grading U.1) d))
          ((mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι ⁻¹ᵁ ⊤)
          (unitApp (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι
            (twistingSheaf (B.grading U.1) d) ⊤ (degreeSection (B.grading U.1) d
              ⟨DirectSum.of (B.sectionPieces U.1) d b, B.of_mem_grading U.1 b⟩))) :=
  by
  rw [chartTargetIso_eq_legIso]
  exact legIso_unitApp_psiU B d U b (pieceIncl ψ U) ψ.relativeMapDomain.ι (chartDomainIso ψ U).inv
    (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι (pieceIncl_comp_ι ψ U) hTB

/-- The middle factor of `θ_d` over a piece, on the degree section of a homogeneous element:
part (1) of [Stacks, Tag 01MY]. -/
theorem pullback_twistMap_degreeSection (d : ℕ) (U : S.affineOpens)
    (a : Γ(A.piece (d : ℤ), U.1)) :
    ((Scheme.Modules.pullback (chartDomainIso ψ U).inv).map
        (twistMap (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) d)).app ⊤
      (((Scheme.Modules.pullback (chartDomainIso ψ U).inv).obj ((Scheme.Modules.pullback
        (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))).obj
          (twistingSheaf (A.grading U.1) d))).presheaf.map
        (homOfLE (TwistMulLeg.top_le_preimage₂ (chartDomainIso ψ U).inv
          (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)))).op
        (unitApp (chartDomainIso ψ U).inv ((Scheme.Modules.pullback
          (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))).obj
            (twistingSheaf (A.grading U.1) d))
          ((mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)) ⁻¹ᵁ ⊤)
          (unitApp (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))
            (twistingSheaf (A.grading U.1) d) ⊤ (degreeSection (A.grading U.1) d
              ⟨DirectSum.of (A.sectionPieces U.1) d a, A.of_mem_grading U.1 a⟩)))) =
      ((Scheme.Modules.pullback (chartDomainIso ψ U).inv).obj ((Scheme.Modules.pullback
        (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι).obj
          (twistingSheaf (B.grading U.1) d))).presheaf.map
        (homOfLE (TwistMulLeg.top_le_preimage₂ (chartDomainIso ψ U).inv
          (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι)).op
        (unitApp (chartDomainIso ψ U).inv ((Scheme.Modules.pullback
          (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι).obj
            (twistingSheaf (B.grading U.1) d))
          ((mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι ⁻¹ᵁ ⊤)
          (unitApp (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι
            (twistingSheaf (B.grading U.1) d) ⊤ (degreeSection (B.grading U.1) d
              ⟨DirectSum.of (B.sectionPieces U.1) d ((ψ.app (d : ℤ)).app U.1 a),
                B.of_mem_grading U.1 _⟩))) := by
  let ρ := (chartDomainIso ψ U).inv
  let mH := mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)
  let mD := (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι
  let NA := twistingSheaf (A.grading U.1) d
  let NB := twistingSheaf (B.grading U.1) d
  let tM := twistMap (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) d
  let G := (Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback mD).obj NB)
  let dSA := degreeSection (A.grading U.1) d
    ⟨DirectSum.of (A.sectionPieces U.1) d a, A.of_mem_grading U.1 a⟩
  let dSB := degreeSection (B.grading U.1) d
    ⟨DirectSum.of (B.sectionPieces U.1) d ((ψ.app (d : ℤ)).app U.1 a), B.of_mem_grading U.1 _⟩
  have hdS : (⟨ψ.sectionHom U.1 (DirectSum.of (A.sectionPieces U.1) d a),
      (ψ.sectionHom U.1).map_mem (A.of_mem_grading U.1 a)⟩ : B.grading U.1 d) =
      ⟨DirectSum.of (B.sectionPieces U.1) d ((ψ.app (d : ℤ)).app U.1 a),
        B.of_mem_grading U.1 _⟩ :=
    Subtype.ext (SheafGradedAlgebraHom.sectionHom_of ψ U.1 a)
  have hD : tM.app (mH ⁻¹ᵁ ⊤) (unitApp mH NA ⊤ dSA) = unitApp mD NB ⊤ dSB :=
    (Stacks.AlgebraicGeometry.ProjTwistTheta.twistMap_degreeSection (A.grading U.1)
      (B.grading U.1) (ψ.sectionHom U.1) d
      ⟨DirectSum.of (A.sectionPieces U.1) d a, A.of_mem_grading U.1 a⟩).trans
      (congrArg (fun q => unitApp mD NB ⊤ (degreeSection (B.grading U.1) d q)) hdS)
  refine (hom_app_map ((Scheme.Modules.pullback ρ).map tM)
    (TwistMulLeg.top_le_preimage₂ ρ mH) _).trans ?_
  refine (congrArg (fun t => G.presheaf.map (homOfLE (TwistMulLeg.top_le_preimage₂ ρ mH)).op t)
    (unitApp_naturality ρ tM (mH ⁻¹ᵁ ⊤) (unitApp mH NA ⊤ dSA))).trans ?_
  exact congrArg (fun t => G.presheaf.map (homOfLE (TwistMulLeg.top_le_preimage₂ ρ mH)).op
    (unitApp ρ ((Scheme.Modules.pullback mD).obj NB) (mH ⁻¹ᵁ ⊤) t)) hD

/-- The chase assembling the factors of `θ_d` over a piece, with every module, morphism and
section free, so that it is checked on atoms. -/
theorem piece_chase {X : Scheme.{u}} {Mx Tm F G : X.Modules} (θ : Mx ⟶ Tm) (Src : Mx ⟶ F)
    (mid : F ⟶ G) (Tgt : Tm ≅ G) {Wa Wb : X.Opens} (hTA : ⊤ ≤ Wa) (hTB : ⊤ ≤ Wb)
    (x : Γ(Mx, Wa)) (y : Γ(Tm, Wb)) (u : Γ(F, ⊤)) (v : Γ(G, ⊤))
    (e0 : θ.app Wa x = Tgt.inv.app Wa (mid.app Wa (Src.app Wa x)))
    (hsrc : F.presheaf.map (homOfLE hTA).op (Src.app Wa x) = u) (hmid : mid.app ⊤ u = v)
    (htgt : G.presheaf.map (homOfLE hTB).op (Tgt.hom.app Wb y) = v) :
    Tm.presheaf.map (homOfLE hTA).op (θ.app Wa x) = Tm.presheaf.map (homOfLE hTB).op y := by
  calc Tm.presheaf.map (homOfLE hTA).op (θ.app Wa x)
      = Tm.presheaf.map (homOfLE hTA).op (Tgt.inv.app Wa (mid.app Wa (Src.app Wa x))) := by
        rw [e0]
    _ = Tgt.inv.app ⊤ (G.presheaf.map (homOfLE hTA).op (mid.app Wa (Src.app Wa x))) :=
        (hom_app_map Tgt.inv hTA _).symm
    _ = Tgt.inv.app ⊤ (mid.app ⊤ (F.presheaf.map (homOfLE hTA).op (Src.app Wa x))) := by
        rw [hom_app_map mid hTA]
    _ = Tgt.inv.app ⊤ v := by rw [hsrc, hmid]
    _ = Tgt.inv.app ⊤ (Tgt.hom.app ⊤ (Tm.presheaf.map (homOfLE hTB).op y)) := by
        rw [← htgt, hom_app_map Tgt.hom hTB]
    _ = Tm.presheaf.map (homOfLE hTB).op y := hom_app_inv_app Tgt.symm ⊤ _

/-- **`θ_d` over a piece of `U(ψ)`, on the section attached to a homogeneous element**: after
pulling back to the piece over an affine open `U` of the base, `θ_d` carries the inverse image of
`ψ_A(a)` to the inverse image of `ψ_B(ψ(a))`. -/
theorem pullback_pieceIncl_relativeTwistMap_unitApp_psiU (d : ℕ) (U : S.affineOpens)
    (a : Γ(A.piece (d : ℤ), U.1))
    (hTA : (⊤ : (chartImage ψ U).toScheme.Opens) ≤
      pieceIncl ψ U ⁻¹ᵁ relativeMapHom ψ ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ U.1))
    (hTB : (⊤ : (chartImage ψ U).toScheme.Opens) ≤
      pieceIncl ψ U ⁻¹ᵁ ψ.relativeMapDomain.ι ⁻¹ᵁ ((relativeProj B).toBase ⁻¹ᵁ U.1)) :
    ((Scheme.Modules.pullback (pieceIncl ψ U)).obj ((Scheme.Modules.pullback
        ψ.relativeMapDomain.ι).obj (relativeTwist B d))).presheaf.map (homOfLE hTA).op
      (((Scheme.Modules.pullback (pieceIncl ψ U)).map (relativeTwistMap ψ d)).app
        (pieceIncl ψ U ⁻¹ᵁ relativeMapHom ψ ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ U.1))
        (unitApp (pieceIncl ψ U) ((Scheme.Modules.pullback (relativeMapHom ψ)).obj
            (relativeTwist A d)) (relativeMapHom ψ ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ U.1))
          (unitApp (relativeMapHom ψ) (relativeTwist A d)
          ((relativeProj A).toBase ⁻¹ᵁ U.1) (psiU A d U.1 a)))) =
    ((Scheme.Modules.pullback (pieceIncl ψ U)).obj ((Scheme.Modules.pullback
        ψ.relativeMapDomain.ι).obj (relativeTwist B d))).presheaf.map (homOfLE hTB).op
      (unitApp (pieceIncl ψ U) ((Scheme.Modules.pullback ψ.relativeMapDomain.ι).obj
            (relativeTwist B d)) (ψ.relativeMapDomain.ι ⁻¹ᵁ ((relativeProj B).toBase ⁻¹ᵁ U.1))
          (unitApp ψ.relativeMapDomain.ι (relativeTwist B d)
          ((relativeProj B).toBase ⁻¹ᵁ U.1) (psiU B d U.1 ((ψ.app (d : ℤ)).app U.1 a)))) := by
  have e0 := pullback_relativeTwistMap_app ψ d U
    (pieceIncl ψ U ⁻¹ᵁ relativeMapHom ψ ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ U.1))
    (unitApp (pieceIncl ψ U) ((Scheme.Modules.pullback (relativeMapHom ψ)).obj
            (relativeTwist A d)) (relativeMapHom ψ ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ U.1))
          (unitApp (relativeMapHom ψ) (relativeTwist A d)
          ((relativeProj A).toBase ⁻¹ᵁ U.1) (psiU A d U.1 a)))
  have hsrc := chartSourceIso_unitApp_psiU ψ d U a hTA
  have hmid := pullback_twistMap_degreeSection ψ d U a
  have htgt := chartTargetIso_unitApp_psiU ψ d U ((ψ.app (d : ℤ)).app U.1 a) hTB
  exact piece_chase (θ := (Scheme.Modules.pullback (pieceIncl ψ U)).map (relativeTwistMap ψ d))
    (Src := (chartSourceIso ψ d U).hom)
    (mid := (Scheme.Modules.pullback (chartDomainIso ψ U).inv).map
      (twistMap (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) d))
    (Tgt := chartTargetIso ψ d U)
    (Wa := pieceIncl ψ U ⁻¹ᵁ relativeMapHom ψ ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ U.1))
    (Wb := pieceIncl ψ U ⁻¹ᵁ ψ.relativeMapDomain.ι ⁻¹ᵁ ((relativeProj B).toBase ⁻¹ᵁ U.1)) hTA hTB
    (unitApp (pieceIncl ψ U) ((Scheme.Modules.pullback (relativeMapHom ψ)).obj
            (relativeTwist A d)) (relativeMapHom ψ ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ U.1))
          (unitApp (relativeMapHom ψ) (relativeTwist A d)
          ((relativeProj A).toBase ⁻¹ᵁ U.1) (psiU A d U.1 a)))
    (unitApp (pieceIncl ψ U) ((Scheme.Modules.pullback ψ.relativeMapDomain.ι).obj
            (relativeTwist B d)) (ψ.relativeMapDomain.ι ⁻¹ᵁ ((relativeProj B).toBase ⁻¹ᵁ U.1))
          (unitApp ψ.relativeMapDomain.ι (relativeTwist B d)
          ((relativeProj B).toBase ⁻¹ᵁ U.1) (psiU B d U.1 ((ψ.app (d : ℤ)).app U.1 a))))
    (((Scheme.Modules.pullback (chartDomainIso ψ U).inv).obj ((Scheme.Modules.pullback
        (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))).obj
          (twistingSheaf (A.grading U.1) d))).presheaf.map
        (homOfLE (TwistMulLeg.top_le_preimage₂ (chartDomainIso ψ U).inv
          (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)))).op
        (unitApp (chartDomainIso ψ U).inv ((Scheme.Modules.pullback
          (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))).obj
            (twistingSheaf (A.grading U.1) d))
          ((mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)) ⁻¹ᵁ ⊤)
          (unitApp (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))
            (twistingSheaf (A.grading U.1) d) ⊤ (degreeSection (A.grading U.1) d
              ⟨DirectSum.of (A.sectionPieces U.1) d a, A.of_mem_grading U.1 a⟩))))
    (((Scheme.Modules.pullback (chartDomainIso ψ U).inv).obj ((Scheme.Modules.pullback
        (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι).obj
          (twistingSheaf (B.grading U.1) d))).presheaf.map
        (homOfLE (TwistMulLeg.top_le_preimage₂ (chartDomainIso ψ U).inv
          (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι)).op
        (unitApp (chartDomainIso ψ U).inv ((Scheme.Modules.pullback
          (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι).obj
            (twistingSheaf (B.grading U.1) d))
          ((mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι ⁻¹ᵁ ⊤)
          (unitApp (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι
            (twistingSheaf (B.grading U.1) d) ⊤ (degreeSection (B.grading U.1) d
              ⟨DirectSum.of (B.sectionPieces U.1) d ((ψ.app (d : ℤ)).app U.1 a),
                B.of_mem_grading U.1 ((ψ.app (d : ℤ)).app U.1 a)⟩))))
    e0 hsrc hmid htgt

/-- `r_ψ` lies over the base: the inverse image under `r_ψ` of the part of `Proj_S(A)` over `V` is
the part of `U(ψ)` over `V`. -/
theorem relativeMapHom_preimage_toBase (V : S.Opens) :
    relativeMapHom ψ ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V) =
      ψ.relativeMapDomain.ι ⁻¹ᵁ ((relativeProj B).toBase ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage, relativeMapHom_comp_toBase, Scheme.Hom.comp_preimage]

omit ψ in
/-- **The inverse image of the section attached to a restricted homogeneous element** is the
restriction of the inverse image of the section attached to the element. -/
theorem unitApp_psiU_map (A : SheafGradedAlgebra S) {Y : Scheme.{u}}
    (k : Y ⟶ (relativeProj A).scheme) (d : ℕ) {U V : S.Opens} (h : U ≤ V)
    (a : Γ(A.piece (d : ℤ), V)) :
    unitApp k (relativeTwist A d) ((relativeProj A).toBase ⁻¹ᵁ U)
        (psiU A d U ((A.piece (d : ℤ)).presheaf.map (homOfLE h).op a)) =
      ((Scheme.Modules.pullback k).obj (relativeTwist A d)).presheaf.map
        (homOfLE (k.preimage_mono ((relativeProj A).toBase.preimage_mono h))).op
        (unitApp k (relativeTwist A d) ((relativeProj A).toBase ⁻¹ᵁ V) (psiU A d V a)) := by
  have e : psiU A d U ((A.piece (d : ℤ)).presheaf.map (homOfLE h).op a) =
      (relativeTwist A d).presheaf.map (homOfLE ((relativeProj A).toBase.preimage_mono h)).op
        (psiU A d V a) :=
    hom_app_map ((twD A).ψ d) h a
  rw [e]
  exact unitApp_map k (relativeTwist A d) ((relativeProj A).toBase.preimage_mono h) _

/-- The piece over an affine open `U ⊆ V` lies over `U`, read on `U(ψ)`. -/
theorem top_le_pieceIncl_preimage (U : S.affineOpens) {V : S.Opens} (hUV : U.1 ≤ V) :
    (⊤ : (chartImage ψ U).toScheme.Opens) ≤
      pieceIncl ψ U ⁻¹ᵁ ψ.relativeMapDomain.ι ⁻¹ᵁ ((relativeProj B).toBase ⁻¹ᵁ V) := by
  have e : pieceIncl ψ U ⁻¹ᵁ ψ.relativeMapDomain.ι ⁻¹ᵁ ((relativeProj B).toBase ⁻¹ᵁ V) =
      (chartImage ψ U).ι ⁻¹ᵁ ((relativeProj B).toBase ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, Scheme.homOfLE_ι]
  rw [e]
  intro x _
  exact (relativeProj B).toBase.preimage_mono hUV ((chartImage_eq_inf ψ U).le x.2).2

/-- **`θ_d` on the section attached to a homogeneous element** ([Stacks, Tag 07ZG] read through
[Stacks, Tag 01MY] (1)): `θ_d` carries the inverse image along `r_ψ` of `ψ_A(a)`, for `a`
homogeneous of degree `d` over an open `V` of the base, to the restriction of `ψ_B(ψ(a))`. -/
theorem relativeTwistMap_unitApp_psiU (d : ℕ) (V : S.Opens) (a : Γ(A.piece (d : ℤ), V)) :
    (relativeTwistMap ψ d).app (relativeMapHom ψ ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V))
        (unitApp (relativeMapHom ψ) (relativeTwist A d) ((relativeProj A).toBase ⁻¹ᵁ V)
          (psiU A d V a)) =
      ((Scheme.Modules.pullback ψ.relativeMapDomain.ι).obj (relativeTwist B d)).presheaf.map
        (homOfLE (relativeMapHom_preimage_toBase ψ V).le).op
        (unitApp ψ.relativeMapDomain.ι (relativeTwist B d) ((relativeProj B).toBase ⁻¹ᵁ V)
          (psiU B d V ((ψ.app (d : ℤ)).app V a))) := by
  have hcov : relativeMapHom ψ ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V) ≤
      ⨆ k : {U : S.affineOpens // U.1 ≤ V}, pieceIncl ψ k.1 ''ᵁ ⊤ := by
    intro x hx
    rw [relativeMapHom_preimage_toBase] at hx
    obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset
      (show (relativeProj B).toBase.base (ψ.relativeMapDomain.ι.base x) ∈ V from hx)
    let U' : S.affineOpens := ⟨U, hU⟩
    have hxc : ψ.relativeMapDomain.ι.base x ∈ chartImage ψ U' :=
      (chartImage_eq_inf ψ U').ge ⟨x.2, hxU⟩
    have h1 : pieceIncl ψ U' ''ᵁ ⊤ = ψ.relativeMapDomain.ι ⁻¹ᵁ chartImage ψ U' := by
      rw [Scheme.Hom.image_top_eq_opensRange, opensRange_homOfLE]
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U', hUV⟩, h1.ge hxc⟩
  have hTop : ∀ (U : S.affineOpens) {W : S.Opens}, U.1 ≤ W → (⊤ : (chartImage ψ U).toScheme.Opens) ≤
      pieceIncl ψ U ⁻¹ᵁ relativeMapHom ψ ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ W) := fun U W h => by
    rw [relativeMapHom_preimage_toBase]
    exact top_le_pieceIncl_preimage ψ U h
  refine TwistMulLeg.eq_of_restrict_cover (fun k : {U : S.affineOpens // U.1 ≤ V} =>
    pieceIncl ψ k.1 ''ᵁ ⊤) (fun k => le_trans (Scheme.Hom.image_mono (pieceIncl ψ k.1)
      (hTop k.1 k.2)) ((pieceIncl ψ k.1).image_preimage_le _)) hcov fun k => ?_
  obtain ⟨U, hUV⟩ := k
  have hTB := top_le_pieceIncl_preimage ψ U (le_refl U.1)
  have hTA := hTop U (le_refl U.1)
  have hT0 := hTop U hUV
  refine TwistMulLeg.eq_of_unitApp_restrict (pieceIncl ψ U) _ hT0 _ _ ?_
  refine TwistMulLeg.chase_restrict (pieceIncl ψ U) (relativeTwistMap ψ d)
    (unitApp (relativeMapHom ψ) (relativeTwist A d) ((relativeProj A).toBase ⁻¹ᵁ V)
      (psiU A d V a))
    (unitApp ψ.relativeMapDomain.ι (relativeTwist B d) ((relativeProj B).toBase ⁻¹ᵁ V)
      (psiU B d V ((ψ.app (d : ℤ)).app V a)))
    (Wa := relativeMapHom ψ ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ U.1))
    (Wb := ψ.relativeMapDomain.ι ⁻¹ᵁ ((relativeProj B).toBase ⁻¹ᵁ U.1))
    ((relativeMapHom ψ).preimage_mono ((relativeProj A).toBase.preimage_mono hUV))
    (ψ.relativeMapDomain.ι.preimage_mono ((relativeProj B).toBase.preimage_mono hUV))
    (relativeMapHom_preimage_toBase ψ V).le hTA hTB hT0 ?_
  have piece := pullback_pieceIncl_relativeTwistMap_unitApp_psiU ψ d U
    ((A.piece (d : ℤ)).presheaf.map (homOfLE hUV).op a) hTA hTB
  have e1 := unitApp_psiU_map A (relativeMapHom ψ) d hUV a
  have eψ : (ψ.app (d : ℤ)).app U.1 ((A.piece (d : ℤ)).presheaf.map (homOfLE hUV).op a) =
      (B.piece (d : ℤ)).presheaf.map (homOfLE hUV).op ((ψ.app (d : ℤ)).app V a) :=
    hom_app_map (ψ.app (d : ℤ)) hUV a
  have e2 := unitApp_psiU_map B ψ.relativeMapDomain.ι d hUV ((ψ.app (d : ℤ)).app V a)
  refine (congrArg (fun z => ((Scheme.Modules.pullback (pieceIncl ψ U)).obj
      ((Scheme.Modules.pullback ψ.relativeMapDomain.ι).obj (relativeTwist B d))).presheaf.map
      (homOfLE hTA).op (((Scheme.Modules.pullback (pieceIncl ψ U)).map (relativeTwistMap ψ d)).app
        (pieceIncl ψ U ⁻¹ᵁ relativeMapHom ψ ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ U.1))
        (unitApp (pieceIncl ψ U) ((Scheme.Modules.pullback (relativeMapHom ψ)).obj
          (relativeTwist A d)) (relativeMapHom ψ ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ U.1)) z)))
    e1).symm.trans (piece.trans ?_)
  refine congrArg (fun z => ((Scheme.Modules.pullback (pieceIncl ψ U)).obj
      ((Scheme.Modules.pullback ψ.relativeMapDomain.ι).obj (relativeTwist B d))).presheaf.map
      (homOfLE hTB).op (unitApp (pieceIncl ψ U) ((Scheme.Modules.pullback
        ψ.relativeMapDomain.ι).obj (relativeTwist B d))
        (ψ.relativeMapDomain.ι ⁻¹ᵁ ((relativeProj B).toBase ⁻¹ᵁ U.1)) z)) ?_
  exact (congrArg (fun b => unitApp ψ.relativeMapDomain.ι (relativeTwist B d)
    ((relativeProj B).toBase ⁻¹ᵁ U.1) (psiU B d U.1 b)) eψ).trans e2

end Stacks.AlgebraicGeometry.Tag07ZGTwist

end
