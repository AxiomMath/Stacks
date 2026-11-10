module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PointPsi
meta import StacksFrontier.Tactic.HEqCongr

/-!
# The compatibility of `ψ` of Stacks 084D with the base change to a scheme point

In Situation 0849 let `π : P = Proj_X(𝒜) ⟶ X` be the relative homogeneous spectrum of Stacks 084B,
`ψ_n : π^*𝒜_n ⟶ 𝒪_P(n)` the homomorphism of Stacks 084D
(`AlgebraicGeometry.Space.RelativeProjSituation.psiTwistHom`), and `f : T ⟶ X` a scheme point of
the base.  The base change clause of Stacks 084D identifies `(T ×_X P ⟶ P)^*𝒪_P(n)` with the twist
`𝒪(n)` of Stacks 01NR on `T ×_X P = Proj_T(f^*𝒜)`
(`AlgebraicGeometry.Space.RelativeProjSituation.exists_fibreToSpace_twistModule_iso`).  This file
proves that this identification carries the inverse image of `ψ_n` to `ψ` of Tag 01NR.

## Main results

* `…RelativeProjSituation.modulePullback_map_psiTwistHom_comp_eq_fibrePsiHom`: every
  isomorphism `e : (T ×_X P ⟶ P)^*𝒪_P(n) ≅ 𝒪(n)^a` which on the étale cover
  `T_U ×_T P' ⟶ T ×_X P` is the composite of the comparisons of twists carries
  `(T ×_X P ⟶ P)^*ψ_n` to `ψ` of Tag 01NR, read through the identification of the sources
  (`AlgebraicGeometry.Space.RelativeProjSituation.fibrePsiHom`).
* `AlgebraicGeometry.Space.RelativeProjSituation.exists_fibreToSpace_twistModule_iso_psi`: the
  base change clause of Stacks 084D with `ψ`: such an isomorphism exists, and it carries `ψ_n` to
  `ψ` of Tag 01NR.

## Implementation notes

The two morphisms are compared after inverse image along the atlas of `T ×_X P`, which is
injective on morphisms of quasi-coherent modules, and after the identification of the target on
the atlas.  Both sides then are chains of the squares
`AlgebraicGeometry.Space.RelativeProjSituation.pointPsi_*` of `ψ` on the atlases of `P` and of
`T ×_X P`.  These squares are stated with the objects and morphisms they mention spelled as their
own constructions produce them, and two spellings of the same morphism are expensive to compare
by unification.  The assembly `AlgebraicGeometry.Space.comp_comp_eq_of_psi_squares_of_heq`
therefore takes every square over its own objects and morphisms, glued by equations of objects
and heterogeneous equations of morphisms; these are proved by congruence
(`Stacks.HEqCongr.heqByCongr`), so that only objects and categories are compared, by the kernel.

## References

* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
-/

@[expose] public noncomputable section

universe u m

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Space

/-- **The assembly of the compatibility of `ψ` with the base change to a scheme point, every
square over its own objects**: the squares of
`AlgebraicGeometry.Space.comp_comp_eq_of_psi_squares`, each stated with its own objects and
morphisms, glued by equations of objects and heterogeneous equations of morphisms.  A square
instantiated at concrete modules then never has to share an object or a morphism with another one
by unification. -/
theorem comp_comp_eq_of_psi_squares_of_heq {C : Type*} [Category C]
    {S1 S2 Z Tt R1 S2_he Z_he Tt_he S2_hppc Tt_hppc Y2_hppc Y3_hppc Y4_hppc S1_hnat1 S2_hnat1
      Y2_hnat1 Y1_hnat1 Y1_hchart Y2_hchart Y3_hchart Y5_hchart Y5_hnat2 Y3_hnat2 Y4_hnat2 Y6_hnat2
      Y6_hbA Y4_hbA Tt_hbA K_hbA K0_hbA Y1_hG2A Y5_hG2A Y6_hG2A K_hG2A Y7_hG2A Y8_hG2A K1_hG2A
      K2_hG2A K3_hG2A S1_hpSH1 Y1_hpSH1 S7_hpSH1 Y7_hpSH1 Y7_hcA Y1_hcA S7_htr Y7_htr Y8_htr K1_htr
      S8_htr Z_hoyc Tt_hoyc R3_hoyc R1_hnat3 Z_hnat3 R3_hnat3 R4_hnat3 R4_hbB R3_hbB Tt_hbB K_hbB
      K0_hbB S1_hG2B R1_hG2B R4_hG2B K_hG2B S7_hG2B S8_hG2B K1_hG2B K2_hG2B K3_hG2B : C}
    {Lh : S1 ⟶ S2} {Le : S2 ⟶ Z} {oyc : Z ⟶ Tt} {Rσ : S1 ⟶ R1} {REψ : R1 ⟶ Z} {Le_he : S2_he ⟶ Z_he}
    {oyc_he : Z_he ⟶ Tt_he} {ppc_he : S2_he ⟶ Tt_he} {ppc_hppc : S2_hppc ⟶ Tt_hppc}
    {pSH2_hppc : S2_hppc ⟶ Y2_hppc} {Yκ_hppc : Y2_hppc ⟶ Y3_hppc} {m2_hppc : Y3_hppc ⟶ Y4_hppc}
    {EΘA_hppc : Y4_hppc ⟶ Tt_hppc} {Lh_hnat1 : S1_hnat1 ⟶ S2_hnat1}
    {pSH2_hnat1 : S2_hnat1 ⟶ Y2_hnat1} {pSH1_hnat1 : S1_hnat1 ⟶ Y1_hnat1}
    {Yψ_hnat1 : Y1_hnat1 ⟶ Y2_hnat1} {Yψ_hchart : Y1_hchart ⟶ Y2_hchart}
    {Yκ_hchart : Y2_hchart ⟶ Y3_hchart} {YσU_hchart : Y1_hchart ⟶ Y5_hchart}
    {YEψU_hchart : Y5_hchart ⟶ Y3_hchart} {YEψU_hnat2 : Y5_hnat2 ⟶ Y3_hnat2}
    {m2_hnat2 : Y3_hnat2 ⟶ Y4_hnat2} {m1_hnat2 : Y5_hnat2 ⟶ Y6_hnat2}
    {EψU_hnat2 : Y6_hnat2 ⟶ Y4_hnat2} {EψU_hbA : Y6_hbA ⟶ Y4_hbA} {EΘA_hbA : Y4_hbA ⟶ Tt_hbA}
    {EchA_hbA : Y6_hbA ⟶ K_hbA} {Ec2_hbA : K_hbA ⟶ K0_hbA} {Eψ2_hbA : K0_hbA ⟶ Tt_hbA}
    {YσU_hG2A : Y1_hG2A ⟶ Y5_hG2A} {m1_hG2A : Y5_hG2A ⟶ Y6_hG2A} {EchA_hG2A : Y6_hG2A ⟶ K_hG2A}
    {cA_hG2A : Y1_hG2A ⟶ Y7_hG2A} {c2A_hG2A : Y7_hG2A ⟶ Y8_hG2A} {trA_hG2A : Y8_hG2A ⟶ K1_hG2A}
    {b1_hG2A : K1_hG2A ⟶ K2_hG2A} {b2_hG2A : K2_hG2A ⟶ K3_hG2A} {b3_hG2A : K3_hG2A ⟶ K_hG2A}
    {pSH1_hpSH1 : S1_hpSH1 ⟶ Y1_hpSH1} {cH_hpSH1 : S1_hpSH1 ⟶ S7_hpSH1}
    {tr_hpSH1 : S7_hpSH1 ⟶ Y7_hpSH1} {cAinv_hpSH1 : Y7_hpSH1 ⟶ Y1_hpSH1}
    {cAinv_hcA : Y7_hcA ⟶ Y1_hcA} {cA_hcA : Y1_hcA ⟶ Y7_hcA} {tr_htr : S7_htr ⟶ Y7_htr}
    {c2A_htr : Y7_htr ⟶ Y8_htr} {trA_htr : Y8_htr ⟶ K1_htr} {c2B_htr : S7_htr ⟶ S8_htr}
    {trB_htr : S8_htr ⟶ K1_htr} {oyc_hoyc : Z_hoyc ⟶ Tt_hoyc} {m3_hoyc : Z_hoyc ⟶ R3_hoyc}
    {EΘB_hoyc : R3_hoyc ⟶ Tt_hoyc} {REψ_hnat3 : R1_hnat3 ⟶ Z_hnat3} {m3_hnat3 : Z_hnat3 ⟶ R3_hnat3}
    {m4_hnat3 : R1_hnat3 ⟶ R4_hnat3} {EψT_hnat3 : R4_hnat3 ⟶ R3_hnat3} {EψT_hbB : R4_hbB ⟶ R3_hbB}
    {EΘB_hbB : R3_hbB ⟶ Tt_hbB} {EchB_hbB : R4_hbB ⟶ K_hbB} {Ec2_hbB : K_hbB ⟶ K0_hbB}
    {Eψ2_hbB : K0_hbB ⟶ Tt_hbB} {Rσ_hG2B : S1_hG2B ⟶ R1_hG2B} {m4_hG2B : R1_hG2B ⟶ R4_hG2B}
    {EchB_hG2B : R4_hG2B ⟶ K_hG2B} {cH_hG2B : S1_hG2B ⟶ S7_hG2B} {c2B_hG2B : S7_hG2B ⟶ S8_hG2B}
    {trB_hG2B : S8_hG2B ⟶ K1_hG2B} {b1_hG2B : K1_hG2B ⟶ K2_hG2B} {b2_hG2B : K2_hG2B ⟶ K3_hG2B}
    {b3_hG2B : K3_hG2B ⟶ K_hG2B}
    (he : Le_he ≫ oyc_he = ppc_he)
    (hppc : ppc_hppc = pSH2_hppc ≫ Yκ_hppc ≫ m2_hppc ≫ EΘA_hppc)
    (hnat1 : Lh_hnat1 ≫ pSH2_hnat1 = pSH1_hnat1 ≫ Yψ_hnat1)
    (hchart : Yψ_hchart ≫ Yκ_hchart = YσU_hchart ≫ YEψU_hchart)
    (hnat2 : YEψU_hnat2 ≫ m2_hnat2 = m1_hnat2 ≫ EψU_hnat2)
    (hbA : EψU_hbA ≫ EΘA_hbA = EchA_hbA ≫ Ec2_hbA ≫ Eψ2_hbA)
    (hG2A : comp₂ YσU_hG2A (comp₂ m1_hG2A EchA_hG2A) =
      comp₂ (comp₂ cA_hG2A (comp₂ c2A_hG2A trA_hG2A)) (comp₂ b1_hG2A (comp₂ b2_hG2A b3_hG2A)))
    (hpSH1 : pSH1_hpSH1 = cH_hpSH1 ≫ tr_hpSH1 ≫ cAinv_hpSH1)
    (hcA : cAinv_hcA ≫ cA_hcA = 𝟙 Y7_hcA)
    (htr : tr_htr ≫ c2A_htr ≫ trA_htr = c2B_htr ≫ trB_htr)
    (hoyc : oyc_hoyc = m3_hoyc ≫ EΘB_hoyc)
    (hnat3 : REψ_hnat3 ≫ m3_hnat3 = m4_hnat3 ≫ EψT_hnat3)
    (hbB : EψT_hbB ≫ EΘB_hbB = EchB_hbB ≫ Ec2_hbB ≫ Eψ2_hbB)
    (hG2B : comp₂ Rσ_hG2B (comp₂ m4_hG2B EchB_hG2B) =
      comp₂ (comp₂ cH_hG2B (comp₂ c2B_hG2B trB_hG2B)) (comp₂ b1_hG2B (comp₂ b2_hG2B b3_hG2B)))
    (oS2_he : S2 = S2_he)
    (oZ_he : Z = Z_he)
    (oTt_he : Tt = Tt_he)
    (oS2_hppc : S2 = S2_hppc)
    (oTt_hppc : Tt = Tt_hppc)
    (oS1_hnat1 : S1 = S1_hnat1)
    (oS2_hnat1 : S2 = S2_hnat1)
    (oY2_hnat1 : Y2_hppc = Y2_hnat1)
    (oY1_hchart : Y1_hnat1 = Y1_hchart)
    (oY2_hchart : Y2_hppc = Y2_hchart)
    (oY3_hchart : Y3_hppc = Y3_hchart)
    (oY5_hnat2 : Y5_hchart = Y5_hnat2)
    (oY3_hnat2 : Y3_hppc = Y3_hnat2)
    (oY4_hnat2 : Y4_hppc = Y4_hnat2)
    (oY6_hbA : Y6_hnat2 = Y6_hbA)
    (oY4_hbA : Y4_hppc = Y4_hbA)
    (oTt_hbA : Tt = Tt_hbA)
    (oY1_hG2A : Y1_hnat1 = Y1_hG2A)
    (oY5_hG2A : Y5_hchart = Y5_hG2A)
    (oY6_hG2A : Y6_hnat2 = Y6_hG2A)
    (oK_hG2A : K_hbA = K_hG2A)
    (oS1_hpSH1 : S1 = S1_hpSH1)
    (oY1_hpSH1 : Y1_hnat1 = Y1_hpSH1)
    (oY7_hpSH1 : Y7_hG2A = Y7_hpSH1)
    (oY7_hcA : Y7_hG2A = Y7_hcA)
    (oY1_hcA : Y1_hnat1 = Y1_hcA)
    (oS7_htr : S7_hpSH1 = S7_htr)
    (oY7_htr : Y7_hG2A = Y7_htr)
    (oY8_htr : Y8_hG2A = Y8_htr)
    (oK1_htr : K1_hG2A = K1_htr)
    (oZ_hoyc : Z = Z_hoyc)
    (oTt_hoyc : Tt = Tt_hoyc)
    (oR1_hnat3 : R1 = R1_hnat3)
    (oZ_hnat3 : Z = Z_hnat3)
    (oR3_hnat3 : R3_hoyc = R3_hnat3)
    (oR4_hbB : R4_hnat3 = R4_hbB)
    (oR3_hbB : R3_hoyc = R3_hbB)
    (oTt_hbB : Tt = Tt_hbB)
    (oK_hbB : K_hbA = K_hbB)
    (oK0_hbB : K0_hbA = K0_hbB)
    (oS1_hG2B : S1 = S1_hG2B)
    (oR1_hG2B : R1 = R1_hG2B)
    (oR4_hG2B : R4_hnat3 = R4_hG2B)
    (oK_hG2B : K_hbA = K_hG2B)
    (oS7_hG2B : S7_hpSH1 = S7_hG2B)
    (oS8_hG2B : S8_htr = S8_hG2B)
    (oK1_hG2B : K1_hG2A = K1_hG2B)
    (oK2_hG2B : K2_hG2A = K2_hG2B)
    (oK3_hG2B : K3_hG2A = K3_hG2B)
    (gLe_he : HEq Le Le_he)
    (goyc_he : HEq oyc oyc_he)
    (gppc_hppc : HEq ppc_he ppc_hppc)
    (gLh_hnat1 : HEq Lh Lh_hnat1)
    (gpSH2_hnat1 : HEq pSH2_hppc pSH2_hnat1)
    (gYψ_hchart : HEq Yψ_hnat1 Yψ_hchart)
    (gYκ_hchart : HEq Yκ_hppc Yκ_hchart)
    (gYEψU_hnat2 : HEq YEψU_hchart YEψU_hnat2)
    (gm2_hnat2 : HEq m2_hppc m2_hnat2)
    (gEψU_hbA : HEq EψU_hnat2 EψU_hbA)
    (gEΘA_hbA : HEq EΘA_hppc EΘA_hbA)
    (gYσU_hG2A : HEq YσU_hchart YσU_hG2A)
    (gm1_hG2A : HEq m1_hnat2 m1_hG2A)
    (gEchA_hG2A : HEq EchA_hbA EchA_hG2A)
    (gpSH1_hpSH1 : HEq pSH1_hnat1 pSH1_hpSH1)
    (gcAinv_hcA : HEq cAinv_hpSH1 cAinv_hcA)
    (gcA_hcA : HEq cA_hG2A cA_hcA)
    (gtr_htr : HEq tr_hpSH1 tr_htr)
    (gc2A_htr : HEq c2A_hG2A c2A_htr)
    (gtrA_htr : HEq trA_hG2A trA_htr)
    (goyc_hoyc : HEq oyc oyc_hoyc)
    (gREψ_hnat3 : HEq REψ REψ_hnat3)
    (gm3_hnat3 : HEq m3_hoyc m3_hnat3)
    (gEψT_hbB : HEq EψT_hnat3 EψT_hbB)
    (gEΘB_hbB : HEq EΘB_hoyc EΘB_hbB)
    (gEc2_hbB : HEq Ec2_hbA Ec2_hbB)
    (gEψ2_hbB : HEq Eψ2_hbA Eψ2_hbB)
    (gRσ_hG2B : HEq Rσ Rσ_hG2B)
    (gm4_hG2B : HEq m4_hnat3 m4_hG2B)
    (gEchB_hG2B : HEq EchB_hbB EchB_hG2B)
    (gcH_hG2B : HEq cH_hpSH1 cH_hG2B)
    (gc2B_hG2B : HEq c2B_htr c2B_hG2B)
    (gtrB_hG2B : HEq trB_htr trB_hG2B)
    (gb1_hG2B : HEq b1_hG2A b1_hG2B)
    (gb2_hG2B : HEq b2_hG2A b2_hG2B)
    (gb3_hG2B : HEq b3_hG2A b3_hG2B)
    :
    (Lh ≫ Le) ≫ oyc = (Rσ ≫ REψ) ≫ oyc := by
  subst oS2_he oZ_he oTt_he oS2_hppc oTt_hppc oS1_hnat1 oS2_hnat1 oY2_hnat1 oY1_hchart oY2_hchart
    oY3_hchart oY5_hnat2 oY3_hnat2 oY4_hnat2 oY6_hbA oY4_hbA oTt_hbA oY1_hG2A oY5_hG2A oY6_hG2A
    oK_hG2A oS1_hpSH1 oY1_hpSH1 oY7_hpSH1 oY7_hcA oY1_hcA oS7_htr oY7_htr oY8_htr oK1_htr oZ_hoyc
    oTt_hoyc oR1_hnat3 oZ_hnat3 oR3_hnat3 oR4_hbB oR3_hbB oTt_hbB oK_hbB oK0_hbB oS1_hG2B oR1_hG2B
    oR4_hG2B oK_hG2B oS7_hG2B oS8_hG2B oK1_hG2B oK2_hG2B oK3_hG2B
  subst gLe_he goyc_he gppc_hppc gLh_hnat1 gpSH2_hnat1 gYψ_hchart gYκ_hchart gYEψU_hnat2 gm2_hnat2
    gEψU_hbA gEΘA_hbA gYσU_hG2A gm1_hG2A gEchA_hG2A gpSH1_hpSH1 gcAinv_hcA gcA_hcA gtr_htr
    gc2A_htr gtrA_htr goyc_hoyc gREψ_hnat3 gm3_hnat3 gEψT_hbB gEΘB_hbB gEc2_hbB gEψ2_hbB gRσ_hG2B
    gm4_hG2B gEchB_hG2B gcH_hG2B gc2B_hG2B gtrB_hG2B gb1_hG2B gb2_hG2B gb3_hG2B
  exact comp_comp_eq_of_psi_squares (cH' := cH_hpSH1) (EΘB' := EΘB_hoyc) he hppc hnat1 hchart
    hnat2 hbA hG2A hpSH1 rfl hcA htr hoyc rfl hnat3 hbB hG2B

namespace RelativeProjSituation

variable (s : RelativeProjSituation.{u, m})
  (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)
  (T : BigFppfOver s.site s.base s.containsBase) (f : yoneda.obj T ⟶ s.space.1)

/-- **The base change clause of Stacks 084D for `ψ`, at a scheme point**: any isomorphism
`e : (T ×_X P ⟶ P)^*𝒪_P(n) ≅ 𝒪(n)^a` which on the étale cover `T_U ×_T P' ⟶ T ×_X P` is the
composite of the comparisons of twists of Tag 01O3 (the isomorphism of
`AlgebraicGeometry.Space.RelativeProjSituation.exists_fibreToSpace_twistModule_iso`) carries the
inverse image of `ψ_n : π^*𝒜_n ⟶ 𝒪_P(n)` to `ψ` of Tag 01NR on `T ×_X P = Proj_T(f^*𝒜)`, read
through the identification of the sources
(`AlgebraicGeometry.Space.RelativeProjSituation.fibrePsiHom`). -/
theorem modulePullback_map_psiTwistHom_comp_eq_fibrePsiHom (n : ℕ)
    (e : (modulePullback s.site s.base s.containsBase (s.fibreToSpaceHom T f)).obj
        (s.twistModule Px (n : ℤ)).obj ≅
        ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase
          (s.relativeProjPoints.fibre T f)).functor.obj (s.twistPieceQcoh T f (n : ℤ))).obj)
    (he : (modulePullback s.site s.base s.containsBase
          (presentationAtlas (Presentation.ofIsoYoneda (RelativeProjPoints.spacePresentation
            (B := s.site) (S := s.base) (hS := s.containsBase)
            (X := representedAlgebraicSpace s.site s.base s.containsBase T)
              (s.pullback (s.schemePointHom T f)).relativeProjPoints (Px.alongPoint f)
            (s.pullback (s.schemePointHom T f)).isAlgebraicSpace_relativeProjFunctor)
            (s.pointBaseChangeIso T f) (s.pointChartMap Px T f)
              (s.map_pointChartMap Px T f)))).map e.hom ≫
          (ofIsoYonedaChartIso (RelativeProjPoints.spacePresentation (B := s.site) (S := s.base)
            (hS := s.containsBase)
            (X := representedAlgebraicSpace s.site s.base s.containsBase T)
              (s.pullback (s.schemePointHom T f)).relativeProjPoints (Px.alongPoint f)
            (s.pullback (s.schemePointHom T f)).isAlgebraicSpace_relativeProjFunctor)
            (s.pointBaseChangeIso T f) (s.pointChartMap Px T f)
            (s.map_pointChartMap Px T f) (s.twistPieceQcoh T f (n : ℤ))
            (s.pointChartTwistComparison Px T f (n : ℤ))).hom =
        (presentationPullbackChartIso (Presentation.ofIsoYoneda
          (RelativeProjPoints.spacePresentation (B := s.site) (S := s.base) (hS := s.containsBase)
            (X := representedAlgebraicSpace s.site s.base s.containsBase T)
              (s.pullback (s.schemePointHom T f)).relativeProjPoints (Px.alongPoint f)
            (s.pullback (s.schemePointHom T f)).isAlgebraicSpace_relativeProjFunctor)
            (s.pointBaseChangeIso T f) (s.pointChartMap Px T f) (s.map_pointChartMap Px T f))
          (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor)
          (s.fibreToSpaceHom T f)
          (s.chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
            (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f))
          (s.presentationAtlas_ofIsoYoneda_comp_fibreToSpaceHom Px T f)
          (s.twistModule Px (n : ℤ)) (s.twistModuleChartIso Px (n : ℤ))
          (s.chartTwistComparison (s.schemePointHom T f) Px (Px.alongPoint f)
            (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f) (n : ℤ))).hom) :
    (modulePullback s.site s.base s.containsBase (s.fibreToSpaceHom T f)).map
        (s.psiTwistHom Px n) ≫ e.hom = s.fibrePsiHom T f n := by
  have i1 : ((modulePullback s.site s.base s.containsBase (s.fibreToSpaceHom T f)).obj
      (s.psiSourceQcoh (n : ℤ)).obj).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite s.site s.base s.containsBase _ _
      (s.psiSourceQcoh (n : ℤ)).property
  have i2 : (((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase
      (s.relativeProjPoints.fibre T f)).functor.obj
        (s.twistPieceQcoh T f (n : ℤ))).obj).IsQuasicoherentOnSite :=
    ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase
      (s.relativeProjPoints.fibre T f)).functor.obj (s.twistPieceQcoh T f (n : ℤ))).property
  -- inverse image along the atlas of `T ×_X P` is injective on morphisms of quasi-coherent modules
  refine @presentationAtlas_map_injective _ _ _ _ (Presentation.ofIsoYoneda
      (RelativeProjPoints.spacePresentation (B := s.site) (S := s.base) (hS := s.containsBase)
        (X := representedAlgebraicSpace s.site s.base s.containsBase T)
        (s.pullback (s.schemePointHom T f)).relativeProjPoints (Px.alongPoint f)
        (s.pullback (s.schemePointHom T f)).isAlgebraicSpace_relativeProjFunctor)
      (s.pointBaseChangeIso T f) (s.pointChartMap Px T f) (s.map_pointChartMap Px T f))
    _ _ i1 i2 _ _ ?_
  refine (Iso.cancel_iso_hom_right _ _ (ofIsoYonedaChartIso
    (RelativeProjPoints.spacePresentation (B := s.site) (S := s.base) (hS := s.containsBase)
      (X := representedAlgebraicSpace s.site s.base s.containsBase T)
      (s.pullback (s.schemePointHom T f)).relativeProjPoints (Px.alongPoint f)
      (s.pullback (s.schemePointHom T f)).isAlgebraicSpace_relativeProjFunctor)
    (s.pointBaseChangeIso T f) (s.pointChartMap Px T f) (s.map_pointChartMap Px T f)
    (s.twistPieceQcoh T f (n : ℤ)) (s.pointChartTwistComparison Px T f (n : ℤ)))).1 ?_
  -- the squares of `ψ` on the atlases of `P` and of `T ×_X P`
  have hppc := s.pointPsi_presentationPullbackChartIso_hom Px T f n
  have hnat1 := s.pointPsi_pullbackSquareHom_naturality Px T f n
  have hchart := s.pointPsi_chart_comp Px T f n
  have hnat2 := s.pointPsi_chart_naturality Px T f n
  have hbA := s.pointPsi_chart_baseChange Px T f n
  have hG2A := s.pointPsi_chart_source Px T f n
  have hpSH1 := s.pointPsi_pullbackSquareHom_eq_comp Px T f n
  have hcA := s.pointPsi_compInv_comp_compHom Px T f n
  have hG2B := s.pointPsi_point_source Px T f n
  have htr := s.pointPsi_transport Px T f n
  have hoyc := s.pointPsi_ofIsoYonedaChartIso_hom Px T f n
  have hnat3 := s.pointPsi_point_naturality Px T f n
  have hbB := s.pointPsi_point_baseChange Px T f n
  refine map_comp_comp_eq_of_eq _ ?_
  -- the two chains of squares, every square over its own objects
  refine comp_comp_eq_of_psi_squares_of_heq he hppc hnat1 hchart hnat2 hbA hG2A hpSH1 hcA htr hoyc
    hnat3 hbB hG2B
    ?oS2_he ?oZ_he ?oTt_he ?oS2_hppc ?oTt_hppc ?oS1_hnat1 ?oS2_hnat1 ?oY2_hnat1 ?oY1_hchart
    ?oY2_hchart ?oY3_hchart ?oY5_hnat2 ?oY3_hnat2 ?oY4_hnat2 ?oY6_hbA ?oY4_hbA ?oTt_hbA ?oY1_hG2A
    ?oY5_hG2A ?oY6_hG2A ?oK_hG2A ?oS1_hpSH1 ?oY1_hpSH1 ?oY7_hpSH1 ?oY7_hcA ?oY1_hcA ?oS7_htr
    ?oY7_htr ?oY8_htr ?oK1_htr ?oZ_hoyc ?oTt_hoyc ?oR1_hnat3 ?oZ_hnat3 ?oR3_hnat3 ?oR4_hbB ?oR3_hbB
    ?oTt_hbB ?oK_hbB ?oK0_hbB ?oS1_hG2B ?oR1_hG2B ?oR4_hG2B ?oK_hG2B ?oS7_hG2B ?oS8_hG2B ?oK1_hG2B
    ?oK2_hG2B ?oK3_hG2B ?gLe_he ?goyc_he ?gppc_hppc ?gLh_hnat1 ?gpSH2_hnat1 ?gYψ_hchart ?gYκ_hchart
    ?gYEψU_hnat2 ?gm2_hnat2 ?gEψU_hbA ?gEΘA_hbA ?gYσU_hG2A ?gm1_hG2A ?gEchA_hG2A ?gpSH1_hpSH1
    ?gcAinv_hcA ?gcA_hcA ?gtr_htr ?gc2A_htr ?gtrA_htr ?goyc_hoyc ?gREψ_hnat3 ?gm3_hnat3 ?gEψT_hbB
    ?gEΘB_hbB ?gEc2_hbB ?gEψ2_hbB ?gRσ_hG2B ?gm4_hG2B ?gEchB_hG2B ?gcH_hG2B ?gc2B_hG2B ?gtrB_hG2B
    ?gb1_hG2B ?gb2_hG2B ?gb3_hG2B
  -- the comparisons of Stacks 03LU, once as a named morphism and once as a component of the
  -- isomorphism: compared argument by argument by the unifier
  case gcA_hcA => congr
  case gcH_hG2B => congr
  -- every other identification is between the same morphisms or objects up to the spelling of the
  -- objects and categories they mention, checked by the kernel
  all_goals first
    | with_reducible rfl
    | (refine eq_of_heq ?_; heq_congr)
    | heq_congr

/-- **The base change clause of Stacks 084D, with `ψ`**: for every scheme point `f : T ⟶ X` and
every `n ≥ 0` there is an isomorphism `e : (T ×_X P ⟶ P)^*𝒪_P(n) ≅ 𝒪(n)^a` with the twist of
Stacks 01NR on `T ×_X P = Proj_T(f^*𝒜)`, which on the étale cover `T_U ×_T P' ⟶ T ×_X P` is the
composite of the comparisons of twists of Tag 01O3, and which carries the inverse image of
`ψ_n : π^*𝒜_n ⟶ 𝒪_P(n)` to `ψ` of Tag 01NR on `T ×_X P`, read through the identification of the
sources (`AlgebraicGeometry.Space.RelativeProjSituation.fibrePsiHom`). -/
theorem exists_fibreToSpace_twistModule_iso_psi (n : ℕ) :
    ∃ e : (modulePullback s.site s.base s.containsBase (s.fibreToSpaceHom T f)).obj
        (s.twistModule Px (n : ℤ)).obj ≅
        ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase
          (s.relativeProjPoints.fibre T f)).functor.obj (s.twistPieceQcoh T f (n : ℤ))).obj,
      ((modulePullback s.site s.base s.containsBase
            (presentationAtlas (Presentation.ofIsoYoneda (RelativeProjPoints.spacePresentation
              (B := s.site) (S := s.base) (hS := s.containsBase)
              (X := representedAlgebraicSpace s.site s.base s.containsBase T)
                (s.pullback (s.schemePointHom T f)).relativeProjPoints (Px.alongPoint f)
              (s.pullback (s.schemePointHom T f)).isAlgebraicSpace_relativeProjFunctor)
              (s.pointBaseChangeIso T f) (s.pointChartMap Px T f)
                (s.map_pointChartMap Px T f)))).map e.hom ≫
            (ofIsoYonedaChartIso (RelativeProjPoints.spacePresentation (B := s.site) (S := s.base)
              (hS := s.containsBase)
              (X := representedAlgebraicSpace s.site s.base s.containsBase T)
                (s.pullback (s.schemePointHom T f)).relativeProjPoints (Px.alongPoint f)
              (s.pullback (s.schemePointHom T f)).isAlgebraicSpace_relativeProjFunctor)
              (s.pointBaseChangeIso T f) (s.pointChartMap Px T f)
              (s.map_pointChartMap Px T f) (s.twistPieceQcoh T f (n : ℤ))
              (s.pointChartTwistComparison Px T f (n : ℤ))).hom =
          (presentationPullbackChartIso (Presentation.ofIsoYoneda
            (RelativeProjPoints.spacePresentation (B := s.site) (S := s.base) (hS := s.containsBase)
              (X := representedAlgebraicSpace s.site s.base s.containsBase T)
                (s.pullback (s.schemePointHom T f)).relativeProjPoints (Px.alongPoint f)
              (s.pullback (s.schemePointHom T f)).isAlgebraicSpace_relativeProjFunctor)
              (s.pointBaseChangeIso T f) (s.pointChartMap Px T f) (s.map_pointChartMap Px T f))
            (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor)
            (s.fibreToSpaceHom T f)
            (s.chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
              (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f))
            (s.presentationAtlas_ofIsoYoneda_comp_fibreToSpaceHom Px T f)
            (s.twistModule Px (n : ℤ)) (s.twistModuleChartIso Px (n : ℤ))
            (s.chartTwistComparison (s.schemePointHom T f) Px (Px.alongPoint f)
              (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f) (n : ℤ))).hom) ∧
      (modulePullback s.site s.base s.containsBase (s.fibreToSpaceHom T f)).map
        (s.psiTwistHom Px n) ≫ e.hom = s.fibrePsiHom T f n :=
  -- `Exists.imp` rather than `obtain`, which is far more expensive on this existential
  (s.exists_fibreToSpace_twistModule_iso Px T f (n : ℤ)).imp fun e he =>
    ⟨he, s.modulePullback_map_psiTwistHom_comp_eq_fibrePsiHom Px T f n e he⟩

end RelativeProjSituation

end AlgebraicGeometry.Space

end
