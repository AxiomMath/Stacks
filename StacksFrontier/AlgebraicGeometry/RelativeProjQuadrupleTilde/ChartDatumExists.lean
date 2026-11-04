module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.ClassifyingChart
public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.LaurentUnit
public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.LaurentNonvanishing
public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.LaurentVeronesePow
public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.ChartFactorCover
public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.ChartBase
public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.Datum
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Basic
public import StacksFrontier.AlgebraicGeometry.ProjPresentationCompare.Basic

/-!
# Chart data of the classifying morphism exist locally

For a quadruple `(f : T → S, d, L, ψ)` and the morphism `h : T ⟶ Proj_S(𝒜)` it classifies, every
point of `T` has an open neighbourhood `V` on which `(f, ψ, h)` restricted to `V` has a chart
datum: an affine open `U` of the base, a section `c` of `𝒜_d` over `U` with `ψ(c)` generating `L`
on `V`, the factorization `g` of `h` through `D₊(c)`, and the unit `w = ψ(c)` with
`ψ(a) = g^♯(a / c^i) · w^i`.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry Stacks.RingedSpace
open AlgebraicGeometry.Proj (degreeOpen)
open Stacks.AlgebraicGeometry.MorphismsIntoProj
open Stacks.AlgebraicGeometry.MorphismToProjUniversal
open Stacks.AlgebraicGeometry.ProjChartFromRatios
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.NonvanishingOpen (nonvanishingOpen)
open RingedSpaceModuleAdjunction
open Stacks.RelativeProj.Situation.QuadrupleChart Stacks.RelativeProj.Situation
open Stacks.TensorPowers (natTensorPow)
open Stacks.TensorPowerTrivialize (resTop)

universe u

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
attribute [local instance] LaurentSections.gcommRing

namespace Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde

attribute [local instance] Quadruple.isInvertibleModule_situation

/-- A global section restricted to the whole scheme is itself. -/
theorem resTop_top {X : Scheme.{u}} (M : X.Modules) (u : Γ(M, ⊤)) :
    Stacks.TensorPowerTrivialize.resTop M u ⊤ = u := by
  show M.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op u = u
  rw [show (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 _ from Subsingleton.elim _ _,
    M.presheaf.map_id]
  rfl

section Unit

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {d : ℕ}
  {Y : Scheme.{u}} {L : SheafOfModules.{u} (structureRingSheaf Y.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf (isSheafStruct Y) L]

attribute [local instance] LaurentSections.isInvertibleModule_of_isInvertible
attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-- **An everywhere nonvanishing Veronese section `ψ(f)` is a unit of the Laurent sections**, with
inverse homogeneous of degree `-1`. -/
theorem exists_unit_of_nonvanishing (ψ : VeroneseSections 𝒜 d L) {f : A} (hf : f ∈ 𝒜 d)
    (h : nonvanishingOpen Y L (psiSection 𝒜 ψ ⟨f, hf⟩) = ⊤) :
    ∃ w : (LaurentSections.Ring L (op ⊤))ˣ, (w : LaurentSections.Ring L (op ⊤)) =
        DirectSum.of ((laurent L).sectionsPiece (op ⊤)) 1
          ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare L 1).hom.app ⊤ (ψ.pow hf 1)) ∧
      ∃ τ, ((w⁻¹ : (LaurentSections.Ring L (op ⊤))ˣ) : LaurentSections.Ring L (op ⊤)) =
        DirectSum.of _ (-1) τ := by
  have := LaurentSections.isIso_secHom_of_nonvanishingOpen_eq_top L _ h
  let eI : (show Y.Modules from L) ≅ (show Y.Modules from (laurent L).piece 1) :=
    (unitorPow L).symm ≪≫ Stacks.AlgebraicGeometry.CoherentMulSections.powCompare L 1
  have : @IsIso (SheafOfModules.{u} (structureRingSheaf Y.toRingedSpace)) _ L
      ((laurent L).piece 1) eI.hom := ⟨⟨eI.inv, eI.hom_inv_id, eI.inv_hom_id⟩⟩
  have hi := LaurentSections.isIso_secHom_of_isIso eI.hom (psiSection 𝒜 ψ ⟨f, hf⟩)
  have hu : (unitorPow L).inv.app ⊤ ((unitorPow L).hom.app ⊤ (ψ.pow hf 1)) = ψ.pow hf 1 :=
    congrArg (fun φ : (show Y.Modules from natTensorPow L 1) ⟶ natTensorPow L 1 =>
      φ.app ⊤ (ψ.pow hf 1)) (unitorPow L).hom_inv_id
  have hx : eI.hom.val.app (op ⊤) (psiSection 𝒜 ψ ⟨f, hf⟩) =
      (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare L 1).hom.app ⊤ (ψ.pow hf 1) :=
    congrArg (fun z => (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare L 1).hom.app ⊤ z)
      hu
  have hiso : IsIso (LaurentSections.secHom ((laurent L).piece 1)
      ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare L 1).hom.app ⊤ (ψ.pow hf 1))) :=
    hx ▸ hi
  exact LaurentSections.exists_unit_of_isIso_secHom _

end Unit

section Core

variable (s : Stacks.RelativeProj.Situation.{u}) {d : ℕ} (hd : 0 < d) {Y : Scheme.{u}}
  (U : s.base.affineOpens) (gU : Y ⟶ U.1.toScheme)
  (P : Quadruple (gU ≫ U.1.ι) s.algebra (d : ℤ))
  (ψ : VeroneseSections ((sheafGradedAlgebra s).grading U.1) d P.L)
  (hgen : ⨆ g : (sheafGradedAlgebra s).grading U.1 d,
    nonvanishingOpen Y P.L (psiSection ((sheafGradedAlgebra s).grading U.1) ψ g) = ⊤)
  (c : s.sectionPieces U.1 d)

/-- The section `c`, read in the graded ring of sections of the bridged algebra. -/
abbrev cA : (sheafGradedAlgebra s).sectionRing U.1 :=
  sectionGradedInv s ⟨U.1, U.2⟩ (cHom U.1 c)

/-- The section `cA s U c` is homogeneous of degree `d`. -/
theorem cA_mem : cA s U c ∈ (sheafGradedAlgebra s).grading U.1 d :=
  (sectionGradedInv s ⟨U.1, U.2⟩).map_mem (cHom_mem U.1 c)

/-- The test scheme lies over `U`. -/
theorem top_le_preimage : (⊤ : Y.Opens) ≤ (gU ≫ U.1.ι) ⁻¹ᵁ U.1 := fun y _ => (gU.base y).2

/-- **The morphism of [Stacks, Tag 01N8] attached to `ψ`, read into the chart `Proj 𝒜(U)` of the
situation.** -/
abbrev chartMor : Y ⟶ AlgebraicGeometry.Proj (s.sectionRingGrading U.1) :=
  toProj ((sheafGradedAlgebra s).grading U.1)
      (Stacks.AlgebraicGeometry.ProjTripleClassifying.classifyingHom
        ((sheafGradedAlgebra s).grading U.1) hd ψ hgen) ≫
    (situationChartIso s ⟨U.1, U.2⟩).hom

/-- The inverse image of `D₊(c)` under the chart morphism is the nonvanishing open of `ψ(c)`. -/
theorem chartMor_preimage :
    chartMor s hd U gU P ψ hgen ⁻¹ᵁ Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c) =
      nonvanishingOpen Y P.L
        (psiSection ((sheafGradedAlgebra s).grading U.1) ψ ⟨cA s U c, cA_mem s U c⟩) :=
  preimage_basicOpen_eq ((sheafGradedAlgebra s).grading U.1)
    (Stacks.AlgebraicGeometry.ProjTripleClassifying.isCompatible_classifyingPair
      ((sheafGradedAlgebra s).grading U.1) hd ψ hgen) ⟨cA s U c, cA_mem s U c⟩

/-- The section `a` of `𝒜_{id}` over `U`, read in the graded ring of sections of the bridged
algebra. -/
theorem sectionGradedInv_of (i : ℕ) (a : s.sectionPieces U.1 (i * d)) :
    sectionGradedInv s ⟨U.1, U.2⟩ (DirectSum.of (s.sectionPieces U.1) (i * d) a) =
      DirectSum.of ((sheafGradedAlgebra s).sectionPieces U.1) (i * d) a :=
  situationSectionRingEquiv_symm_of s.algebra s.mul_comm (vanishesInNegativeDegrees s)
    s.isQuasicoherent U.1 (i * d) a

/-- A section of degree `i * d` of the bridged algebra lies in the grading piece `i • d`. -/
private theorem of_mem_grading_smul (s : Stacks.RelativeProj.Situation.{u}) {d : ℕ}
    (U : s.base.affineOpens) (i : ℕ) (a : s.sectionPieces U.1 (i * d)) :
    DirectSum.of ((sheafGradedAlgebra s).sectionPieces U.1) (i * d) a ∈
      (sheafGradedAlgebra s).grading U.1 (i • d) := by
  simpa using (sheafGradedAlgebra s).of_mem_grading U.1 a

/-- **The function `g^♯(a / c^i)` of the chart datum, computed through the morphism of
[Stacks, Tag 01N8].** -/
theorem kappaSec_chartMor
    (hV : (⊤ : Y.Opens) ≤ toProj ((sheafGradedAlgebra s).grading U.1)
      (Stacks.AlgebraicGeometry.ProjTripleClassifying.classifyingHom
        ((sheafGradedAlgebra s).grading U.1) hd ψ hgen) ⁻¹ᵁ
        AlgebraicGeometry.Proj.basicOpen ((sheafGradedAlgebra s).grading U.1) (cA s U c))
    (hg : (⊤ : Y.Opens) ≤ chartMor s hd U gU P ψ hgen ⁻¹ᵁ
      Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c))
    (i : ℕ) (a : s.sectionPieces U.1 (i * d)) :
    kappaSec U c (chartMor s hd U gU P ψ hgen) hg i a =
      (toProj ((sheafGradedAlgebra s).grading U.1)
        (Stacks.AlgebraicGeometry.ProjTripleClassifying.classifyingHom
          ((sheafGradedAlgebra s).grading U.1) hd ψ hgen)).appLE _ ⊤ hV
        (AlgebraicGeometry.Proj.awayToSection _ (cA s U c)
          (HomogeneousLocalization.Away.mk _ (cA_mem s U c) i
            (DirectSum.of ((sheafGradedAlgebra s).sectionPieces U.1) (i * d) a)
            (by simpa using (sheafGradedAlgebra s).of_mem_grading U.1 a))) := by
  have e₁ : AlgebraicGeometry.Proj.basicOpen ((sheafGradedAlgebra s).grading U.1) (cA s U c) ≤
      (situationChartIso s ⟨U.1, U.2⟩).hom ⁻¹ᵁ
        Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c) := fun x hx => hx
  let : GradedRing ((sheafGradedAlgebra s).toGradedAlgebra.grading ⟨U.1, U.2⟩) :=
    (sheafGradedAlgebra s).toGradedAlgebra.gradedRing ⟨U.1, U.2⟩
  have h2 : AlgebraicGeometry.Proj.awayToSection (s.sectionRingGrading U.1) (cHom U.1 c) ≫
      (situationChartIso s ⟨U.1, U.2⟩).hom.appLE
        (Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c))
        (AlgebraicGeometry.Proj.basicOpen ((sheafGradedAlgebra s).grading U.1) (cA s U c)) e₁ =
      CommRingCat.ofHom (HomogeneousLocalization.Away.map (sectionGradedInv s ⟨U.1, U.2⟩)
        (cHom U.1 c)) ≫
        AlgebraicGeometry.Proj.awayToSection ((sheafGradedAlgebra s).grading U.1) (cA s U c) :=
    AlgebraicGeometry.Proj.awayToSection_comp_appLE _ _ (cHom_mem U.1 c)
  have hmk : ∀ (x y : (sheafGradedAlgebra s).sectionRing U.1) (_ : x = y)
      (hx : x ∈ (sheafGradedAlgebra s).grading U.1 (i • d))
      (hy : y ∈ (sheafGradedAlgebra s).grading U.1 (i • d)),
      HomogeneousLocalization.Away.mk ((sheafGradedAlgebra s).grading U.1) (cA_mem s U c) i x hx =
        HomogeneousLocalization.Away.mk ((sheafGradedAlgebra s).grading U.1) (cA_mem s U c) i y
          hy := by
    rintro x _ rfl _ _
    rfl
  have h3 := HomogeneousLocalization.Away.map_mk (sectionGradedInv s ⟨U.1, U.2⟩) (cHom U.1 c)
    (cHom_mem U.1 c) i (DirectSum.of (s.sectionPieces U.1) (i * d) a) ⟨a, rfl⟩
  have h4 := hmk _ _ (sectionGradedInv_of s U i a)
    (Graded.map_mem (sectionGradedInv s ⟨U.1, U.2⟩) ⟨a, rfl⟩)
    (of_mem_grading_smul s U i a)
  refine (congrArg (fun F => F (AlgebraicGeometry.Proj.awayToSection _ _ (algFrac U c i a)))
    (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ e₁ hV).symm).trans ?_
  refine congrArg (Scheme.Hom.appLE _ _ ⊤ hV) ?_
  refine (congrArg (fun F => F (algFrac U c i a)) h2).trans ?_
  exact congrArg (AlgebraicGeometry.Proj.awayToSection _ _) (h3.trans h4)

attribute [local instance] LaurentSections.isInvertibleModule_of_isInvertible

/-- **The chart identity for the morphism of [Stacks, Tag 01N8]**: `ψ(a) = g^♯(a / c^i) · w^i`
with `w = ψ(c)`. -/
theorem hCP_chartMor
    (hψ : HEq (veroneseSections (chartQuadruple s U.1 gU P).twisting) ψ)
    (hg : (⊤ : Y.Opens) ≤ chartMor s hd U gU P ψ hgen ⁻¹ᵁ
      Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c))
    (w : (LaurentSections.Ring P.L (op ⊤))ˣ)
    (hw1 : (w : LaurentSections.Ring P.L (op ⊤)) =
      DirectSum.of ((laurent P.L).sectionsPiece (op ⊤)) 1
        ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare P.L 1).hom.app ⊤
          (ψ.pow (cA_mem s U c) 1)))
    (i : ℕ) (a : s.sectionPieces U.1 (i * d)) :
    ((laurent P.L).piece i).val.map (homOfLE (top_le_preimage s U gU)).op
        (P.twisting.sectionHom i (op U.1) a) =
      (show (structureRingSheaf Y.toRingedSpace).obj.obj (op ⊤) from
        kappaSec U c (chartMor s hd U gU P ψ hgen) hg i a) • LaurentSections.pw w i := by
  have hV : (⊤ : Y.Opens) ≤ toProj ((sheafGradedAlgebra s).grading U.1)
      (Stacks.AlgebraicGeometry.ProjTripleClassifying.classifyingHom
        ((sheafGradedAlgebra s).grading U.1) hd ψ hgen) ⁻¹ᵁ
        AlgebraicGeometry.Proj.basicOpen ((sheafGradedAlgebra s).grading U.1) (cA s U c) :=
    fun t ht => hg ht
  have hk := kappaSec_chartMor s hd U gU P ψ hgen c hV hg i a
  have hp := LaurentSections.pw_natCast_eq_powCompare ψ (cA_mem s U c) w hw1 i
  have cl := (Stacks.AlgebraicGeometry.ProjTripleClassifying.isCompatible_classifyingPair
    ((sheafGradedAlgebra s).grading U.1) hd ψ hgen).2 ⟨cA s U c, cA_mem s U c⟩ ⊤ hV i
    (DirectSum.of ((sheafGradedAlgebra s).sectionPieces U.1) (i * d) a)
    (of_mem_grading_smul s U i a)
    ⟨DirectSum.of ((sheafGradedAlgebra s).sectionPieces U.1) (i * d) a,
      (sheafGradedAlgebra s).of_mem_grading U.1 a⟩ rfl
  rw [resTop_top, resTop_top] at cl
  have ht := toFun_eq_sectionHom s U.1 gU P ψ hψ i a (homOfLE (top_le_preimage s U gU)).op
  have e2 := congrArg
    (fun z => (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare P.L i).hom.app ⊤ z)
    (ht.symm.trans cl)
  rw [hk, hp]
  exact (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare_hom_app_inv_app P.L i _).symm.trans
    (e2.trans (Scheme.Modules.Hom.app_smul _ _ _))

/-- **A factorization of the classifying morphism through a standard open `D₊(c)` of a chart gives
a chart datum.** -/
theorem chartDatum_of_factor (g : Y ⟶ AlgebraicGeometry.Proj (s.sectionRingGrading U.1))
    (hfac : classifyingHom s (by exact_mod_cast hd) P = g ≫ relativeProjChart s U)
    (hg : (⊤ : Y.Opens) ≤ g ⁻¹ᵁ Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c)) :
    Nonempty (ChartDatum (gU ≫ U.1.ι) P.twisting (classifyingHom s (by exact_mod_cast hd) P)) := by
  obtain ⟨ψ, hψ, hgen, heq⟩ := exists_classifyingHom_eq s hd U.1 U.2 gU P
  have hgm : g = chartMor s hd U gU P ψ hgen :=
    (cancel_mono (relativeProjChart s U)).mp
      (hfac.symm.trans (heq.trans (Category.assoc _ _ _).symm))
  subst hgm
  have hnv : nonvanishingOpen Y P.L
      (psiSection ((sheafGradedAlgebra s).grading U.1) ψ ⟨cA s U c, cA_mem s U c⟩) = ⊤ :=
    (chartMor_preimage s hd U gU P ψ hgen c).symm.trans (top_unique hg)
  obtain ⟨w, hw1, τ, hτ⟩ := exists_unit_of_nonvanishing ψ (cA_mem s U c) hnv
  exact ⟨{
    U := U
    c := c
    hf := top_le_preimage s U gU
    g := chartMor s hd U gU P ψ hgen
    hg := hg
    hgf := hgf_of_fac U c hd (gU ≫ U.1.ι) (classifyingHom_comp_toBase s _ P) _ hfac _ hg
    w := w
    hCP := hCP_chartMor s hd U gU P ψ hgen c hψ hg w hw1
    hw := ⟨_, hw1⟩
    hw' := ⟨τ, hτ⟩
    fac := hfac }⟩

end Core

section Exists

variable (s : Stacks.RelativeProj.Situation.{u}) {d : ℕ} (hd : 0 < d)

/-- `chartDatum_of_factor` for a quadruple over any morphism equal to `gU ≫ U.ι`. -/
theorem chartDatum_of_factor' {Y : Scheme.{u}} (U : s.base.affineOpens) (gU : Y ⟶ U.1.toScheme)
    {f' : Y ⟶ s.base} (e : gU ≫ U.1.ι = f') (P : Quadruple f' s.algebra (d : ℤ))
    (c : s.sectionPieces U.1 d) (g : Y ⟶ AlgebraicGeometry.Proj (s.sectionRingGrading U.1))
    (hfac : classifyingHom s (by exact_mod_cast hd) P = g ≫ relativeProjChart s U)
    (hg : (⊤ : Y.Opens) ≤ g ⁻¹ᵁ Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c)) :
    Nonempty (ChartDatum f' P.twisting (classifyingHom s (by exact_mod_cast hd) P)) := by
  subst e
  exact chartDatum_of_factor s hd U gU P c g hfac hg

/-- **Chart data of the classifying morphism exist around every point**: every point of `T` has
an open neighbourhood `V` such that the restriction of `(f, ψ, h)` to `V` has a chart datum. -/
theorem exists_chartDatum {T : Scheme.{u}} (f : T ⟶ s.base) (P : Quadruple f s.algebra (d : ℤ))
    (t : T) :
    ∃ V : T.Opens, t ∈ V ∧ Nonempty (ChartDatum (V.ι ≫ f) (P.twisting.pullback V.ι)
      (V.ι ≫ classifyingHom s (by exact_mod_cast hd) P)) := by
  obtain ⟨V, htV, U, c, g, hVU, hfac, hg⟩ := exists_chart_factor s f hd P t
  have hr : Set.range (V.ι ≫ f).base ⊆ Set.range U.1.ι.base := by
    rintro _ ⟨v, rfl⟩
    exact ⟨⟨_, hVU v.2⟩, rfl⟩
  have e := IsOpenImmersion.lift_fac U.1.ι (V.ι ≫ f) hr
  have hfac' :
      classifyingHom s (by exact_mod_cast hd) (P.pullback V.ι) = g ≫ relativeProjChart s U :=
    (classifyingHom_pullback s _ P V.ι).trans hfac
  obtain ⟨D⟩ := chartDatum_of_factor' s hd U (IsOpenImmersion.lift U.1.ι (V.ι ≫ f) hr) e
    (P.pullback V.ι) c g hfac' hg
  refine ⟨V, htV, ⟨{ D with fac := ?_ }⟩⟩
  exact (classifyingHom_pullback s _ P V.ι).symm.trans D.fac

end Exists

end Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde

end
