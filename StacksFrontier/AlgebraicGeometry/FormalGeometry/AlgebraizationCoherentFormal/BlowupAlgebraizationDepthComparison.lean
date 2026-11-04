module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.BlowupAlgebraizationPullback
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk
public import StacksFrontier.RingTheory.AdicCompletion.IteratedMvPolynomial
public import StacksFrontier.RingTheory.AdicCompletion.CompletionMap
public import StacksFrontier.AlgebraicGeometry.F6Rank128.FiberResidueField
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionFormula
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.ClosedSubsetExistence
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ExtendedIntegers
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapTransport
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.CompletedStalkFinite
public import StacksFrontier.RingTheory.AdicCompletion.BlowupChartCompletionDepth

/-!
# Comparing completed stalks along the blowup, in the proof of Stacks 0EJK

In Situation [Stacks, Tag 0EHC] let `b : X' ⟶ X = Spec(A)` be the blowup of `I`, `U' = b⁻¹(U)`
and `(ℱₙ)` an object of `Coh(U, I𝒪_U)`. The proof of [Stacks, Tag 0EJK] compares, at a point
`y'` of `U'` lying on the exceptional divisor and a prime `𝔭'` of `𝒪_{X',y'}^∧` not containing
`I`, the depth of the completed stalk of the pullback `(b|_{U'}^*ℱₙ)` with the depth of the
completed stalk of `(ℱₙ)` at `y = b(y')` and the prime `𝔭` of `𝒪_{X,y}^∧` under `𝔭'`:
the inequalities (0EJL) and (0EJM) of the source,
`depth((ℱ_y^∧)_𝔭) + dim(𝒪_{X,y}^∧/𝔭) + δ^Y_Z(y) ≤
  depth((ℱ_{y'}^∧)_{𝔭'}) + dim(𝒪_{X',y'}^∧/𝔭') + δ^{Y'}_{Z'}(y') + (d - 1)` and
`dim(𝒪_{X',y'}^∧/𝔭') ≤ dim(𝒪_{X,y}^∧/𝔭)`, when the fibres of `b` have dimension `< d`.

A chart `Spec(A[I/a]) ⟶ X'` of the blowup through `y'` ([Stacks, Tag 0804]) identifies the local
ring of `U'` at `y'` with the localization `A[I/a]_Q` at the prime `Q` of `y'`, and the local ring
of `U` at `y` with `A_𝔮`, `𝔮 = Q ∩ A`; under these identifications the map of local rings induced
by `b` is the localization of `A → A[I/a]`, the stalks of `I𝒪_U` and `I𝒪_{U'}` are the
extensions of `I`, and the residue field extension `κ(y')/κ(y)` is `κ(Q)/κ(𝔮)`. The completed
local rings become `R = (A_𝔮)^∧` and `R' = (A[I/a]_Q)^∧`, on which the commutative algebra of
(0EJL) is `Stacks.Algebraization.depth_add_ringKrullDim_le_blowupChart` and
`Stacks.Algebraization.ringKrullDim_add_trdeg_le_blowupChart`. These are combined with
[Stacks, Tag 0EIZ] for `Y' ⟶ Y`, whose fibres have dimension `≤ d - 1`.

## Main definitions

* `Stacks.Algebraization.openImmersionStalkIso` — for an open immersion `g : Spec R ⟶ X`, an open
  `U ⊆ X` and a point `y` of `U` in the image of `p`, the identification `𝒪_{U,y} ≅ R_p`.
* `Stacks.Algebraization.BlowupChartPoint` — a chart of the blowup through a point of `U'`.
* `Stacks.Algebraization.BlowupChartPoint.baseCompletionEquiv`,
  `Stacks.Algebraization.BlowupChartPoint.chartCompletionEquiv` — `𝒪_{X,y}^∧ ≅ (A_𝔮)^∧` and
  `𝒪_{X',y'}^∧ ≅ (A[I/a]_Q)^∧`.
* `Stacks.Algebraization.BlowupChartPoint.CompletedStalkComparison` — the identification of the
  completed stalk of the pullback with `R' ⊗_R ℱ_y^∧`.

## Main results

* `Stacks.Algebraization.stalkMap_comp_openImmersionStalkIso` — the stalk map of a restricted
  morphism, read on charts, is a localization of the ring map of the charts.
* `Stacks.Algebraization.map_stalk_openImmersionStalkIso` — the stalk of an ideal sheaf, read on a
  chart, is the extension of its sections on the chart.
* `Stacks.Algebraization.nonempty_blowupChartPoint` — every point of `U'` lies on a chart.
* `Stacks.Algebraization.BlowupChartPoint.trdeg_residueField_eq` — the residue field extension.
* `Stacks.Algebraization.one_le_of_blowup_point` — a point of the exceptional divisor forces
  `d ≥ 1`.
* `Stacks.Algebraization.exists_depthAddDimAddDistance_le_blowup_of_comparison` — (0EJL) and
  (0EJM) at `y'`, along a chart on which the completed stalks compare.

## Implementation notes

The chart rings are those of `Stacks.Blowup.blowUpAffineChart` over the affine open `X` itself,
so the base ring is `Γ(X, 𝒪_X)` rather than `A`; the two are isomorphic, and a dualizing complex
on `A` gives one on `Γ(X, 𝒪_X)` since `X` is of finite type over itself.

## References

* [Stacks Project, Tag 0EJK](https://stacks.math.columbia.edu/tag/0EJK)
* [Stacks Project, Tag 0804](https://stacks.math.columbia.edu/tag/0804)
* [Stacks Project, Tag 0EIZ](https://stacks.math.columbia.edu/tag/0EIZ)
-/

/- The comparison `BlowupChartPoint.CompletedStalkComparison` (the "Details omitted" sentence of
the source) is proved in `BlowupAlgebraizationStalkComparison.lean`, which states
`Stacks.Algebraization.exists_depthAddDimAddDistance_le_blowup`. -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace Stacks.Algebraization

section StalkChart

/-- Two specialization maps of stalks compose to one. -/
theorem stalkSpecializes_comp_comp {C : Type*} [Category C] [Limits.HasColimits C]
    {T : TopCat} (F : TopCat.Presheaf C T) {a b c : T} (h₁ : b ⤳ a) (h₂ : c ⤳ b)
    (h₃ : c ⤳ a) {Z : C} (t : F.stalk c ⟶ Z) :
    F.stalkSpecializes h₁ ≫ F.stalkSpecializes h₂ ≫ t = F.stalkSpecializes h₃ ≫ t := by
  simp only [TopCat.Presheaf.stalkSpecializes_comp_assoc]

/-- Cancelling an isomorphism against its inverse in a composite. -/
theorem comp_comp_comp_inv_comp {C : Type*} [Category C] {a b c d e : C} (A : a ⟶ b) (B : b ⟶ c)
    (f : c ⟶ d) [IsIso f] (D : c ⟶ e) : (A ≫ B ≫ f) ≫ inv f ≫ D = A ≫ B ≫ D := by
  simp

/-- The stalk maps of two equal morphisms differ by a specialization map. -/
theorem stalkMap_eq_stalkSpecializes_comp {X Y : Scheme.{u}} {f g : X ⟶ Y} (hfg : f = g) (x : X)
    (h : g x ⤳ f x) : f.stalkMap x = Y.presheaf.stalkSpecializes h ≫ g.stalkMap x := by
  subst hfg
  rw [show h = specializes_refl _ from rfl, TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]

/-- The stalk maps of a commutative square of schemes, read between points related by
specialization. -/
theorem stalkMap_square_stalkSpecializes {X X' Z Z' : Scheme.{u}} (b : X' ⟶ X) (g : Z ⟶ X)
    (g' : Z' ⟶ X') (h : Z' ⟶ Z) (w : g' ≫ b = h ≫ g) (a : X) (x' : X') (z : Z')
    (h₁ : b x' ⤳ a) (h₂ : g' z ⤳ x') (h₃ : g (h z) ⤳ a) (hz : g' z = x') :
    X.presheaf.stalkSpecializes h₁ ≫ b.stalkMap x' ≫ X'.presheaf.stalkSpecializes h₂ ≫
        g'.stalkMap z =
      X.presheaf.stalkSpecializes h₃ ≫ g.stalkMap (h z) ≫ h.stalkMap z := by
  subst hz
  have hsp : (h ≫ g) z ⤳ (g' ≫ b) z := by rw [w]
  rw [show h₂ = specializes_refl _ from rfl, TopCat.Presheaf.stalkSpecializes_refl,
    Category.id_comp, ← Scheme.Hom.stalkMap_comp, stalkMap_eq_stalkSpecializes_comp w z hsp,
    Scheme.Hom.stalkMap_comp]
  exact stalkSpecializes_comp_comp _ _ _ _ _

/-- **Stalk maps of a restricted morphism against charts.** Let `b : X' ⟶ X`, `U ⊆ X` open, and
`g' ≫ b = h ≫ g` a commutative square with `g' z` the image of a point `y'` of `b⁻¹(U)`. Then
the stalk map of `b|_U` at `y'`, read through the inclusions of `U` and `b⁻¹(U)` and the charts,
is the stalk map of `h` at `z`. -/
theorem stalkMap_morphismRestrict_square {X X' Z Z' : Scheme.{u}} (b : X' ⟶ X) (U : X.Opens)
    (g : Z ⟶ X) (g' : Z' ⟶ X') (h : Z' ⟶ Z) (w : g' ≫ b = h ≫ g) (y' : (b ⁻¹ᵁ U).toScheme)
    (z : Z') (hz : g' z = (b ⁻¹ᵁ U).ι y') (h₁ : g (h z) ⤳ U.ι ((b ∣_ U) y'))
    (h₂ : g' z ⤳ (b ⁻¹ᵁ U).ι y') :
    (b ∣_ U).stalkMap y' ≫ inv ((b ⁻¹ᵁ U).ι.stalkMap y') ≫ X'.presheaf.stalkSpecializes h₂ ≫
        g'.stalkMap z =
      inv (U.ι.stalkMap ((b ∣_ U) y')) ≫ X.presheaf.stalkSpecializes h₁ ≫ g.stalkMap (h z) ≫
        h.stalkMap z := by
  have hsp : ((b ⁻¹ᵁ U).ι ≫ b) y' ⤳ (b ∣_ U ≫ U.ι) y' := by rw [morphismRestrict_ι]
  have hres := (Scheme.Hom.stalkMap_comp (b ∣_ U) U.ι y').symm.trans
    ((stalkMap_eq_stalkSpecializes_comp (morphismRestrict_ι b U) y' hsp).trans
      (congrArg _ (Scheme.Hom.stalkMap_comp _ _ y')))
  rw [IsIso.eq_inv_comp, ← Category.assoc, hres]
  refine (comp_comp_comp_inv_comp _ _ _ _).trans ?_
  exact stalkMap_square_stalkSpecializes b g g' h w _ _ z _ _ _ hz

variable {X : Scheme.{u}} {R : CommRingCat.{u}} (g : Spec R ⟶ X) [IsOpenImmersion g]

/-- **The local ring of an open subscheme at a point of a chart.** For an open immersion
`g : Spec R ⟶ X`, an open `U ⊆ X` and a point `y` of `U` which is the image of `p ∈ Spec R`, the
local ring `𝒪_{U,y}` is `R_p`. -/
def openImmersionStalkIso (U : X.Opens) (y : U.toScheme) (p : PrimeSpectrum R) (h : g p = U.ι y) :
    U.toScheme.presheaf.stalk y ≅ CommRingCat.of (Localization.AtPrime p.asIdeal) :=
  haveI : IsIso (g.stalkMap p) := (inferInstance : IsIso (g.stalkMap (show Spec R from p)))
  (asIso (U.ι.stalkMap y)).symm ≪≫ X.presheaf.stalkCongr (.of_eq h.symm) ≪≫ asIso (g.stalkMap p) ≪≫
    Spec.stalkIso R p

/-- **The stalk of an ideal sheaf, read on a chart.** Under `openImmersionStalkIso`, the stalk at
`y` of the restriction of `𝒥` to `U` is the extension of the global sections of `𝒥` on the chart
`Spec R`. -/
theorem map_stalk_openImmersionStalkIso (𝒥 : X.IdealSheafData) (U : X.Opens) (y : U.toScheme)
    (p : PrimeSpectrum R) (h : g p = U.ι y) :
    (IdealSheafData.stalk (𝒥.comap U.ι) y).map (openImmersionStalkIso g U y p h).hom.hom =
      (((𝒥.comap g).ideal ⟨⊤, isAffineOpen_top _⟩).map (Scheme.ΓSpecIso R).hom.hom).map
        (algebraMap R (Localization.AtPrime p.asIdeal)) := by
  have : IsIso (g.stalkMap p) := (inferInstance : IsIso (g.stalkMap (show Spec R from p)))
  rw [IdealSheafData.stalk_comap, Ideal.map_map, ← CommRingCat.hom_comp]
  simp only [openImmersionStalkIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
    IsIso.hom_inv_id_assoc]
  have key : ∀ (x : X) (hx : g p = x),
      (IdealSheafData.stalk 𝒥 x).map ((X.presheaf.stalkCongr (.of_eq hx.symm)).hom ≫
        g.stalkMap p ≫ (Spec.stalkIso R p).hom).hom =
      (((𝒥.comap g).ideal ⟨⊤, isAffineOpen_top _⟩).map (Scheme.ΓSpecIso R).hom.hom).map
        (algebraMap R (Localization.AtPrime p.asIdeal)) := by
    rintro x rfl
    have hg : Ideal.map (g.stalkMap p).hom (IdealSheafData.stalk 𝒥 (g p)) =
        IdealSheafData.stalk (𝒥.comap g) p := (IdealSheafData.stalk_comap 𝒥 g p).symm
    calc (IdealSheafData.stalk 𝒥 (g p)).map ((X.presheaf.stalkCongr (.of_eq rfl)).hom ≫
          g.stalkMap p ≫ (Spec.stalkIso R p).hom).hom
        = ((IdealSheafData.stalk 𝒥 (g p)).map (g.stalkMap p).hom).map
            (Spec.stalkIso R p).hom.hom := by
          simp [TopCat.Presheaf.stalkCongr_hom, Ideal.map_map]
      _ = (((𝒥.comap g).ideal ⟨⊤, isAffineOpen_top _⟩).map
            ((Spec R).presheaf.germ ⊤ p trivial).hom).map (Spec.stalkIso R p).hom.hom := by
          rw [hg,
            IdealSheafData.stalk_eq_map_germ (𝒥.comap g) p ⟨⊤, isAffineOpen_top _⟩ trivial]
      _ = ((𝒥.comap g).ideal ⟨⊤, isAffineOpen_top _⟩).map
            ((Spec R).presheaf.germ ⊤ p trivial ≫ (Spec.stalkIso R p).hom).hom := by
          rw [Ideal.map_map]
          rfl
      _ = _ := by
          rw [Spec.germ_stalkMapIso_hom (R := R) (x := p), CommRingCat.hom_comp, ← Ideal.map_map]
          rfl
  exact key (U.ι y) h

variable {X' : Scheme.{u}} (b : X' ⟶ X) (U : X.Opens) {R' : CommRingCat.{u}}
  (g' : Spec R' ⟶ X') [IsOpenImmersion g'] (θ : R ⟶ R') (hθ : g' ≫ b = Spec.map θ ≫ g)

include hθ in
/-- **Stalk maps of a restricted morphism on charts.** Let `b : X' ⟶ X`, let `U ⊆ X` be open and
let `g' ≫ b = Spec(θ) ≫ g` with open immersions `g`, `g'` from spectra. Under
`openImmersionStalkIso`, the stalk map of `b|_U` at a point `y'` of `b⁻¹(U)` coming from `Q` is the
localization `R_{θ⁻¹Q} → R'_Q` of `θ`. -/
theorem stalkMap_comp_openImmersionStalkIso (y' : (b ⁻¹ᵁ U).toScheme) (Q : PrimeSpectrum R')
    (hQ : g' Q = (b ⁻¹ᵁ U).ι y') (hq : g (PrimeSpectrum.comap θ.hom Q) = U.ι ((b ∣_ U) y')) :
    (b ∣_ U).stalkMap y' ≫ (openImmersionStalkIso g' (b ⁻¹ᵁ U) y' Q hQ).hom =
      (openImmersionStalkIso g U ((b ∣_ U) y') _ hq).hom ≫
        CommRingCat.ofHom (Localization.localRingHom _ Q.asIdeal θ.hom rfl) := by
  have hloc := Scheme.localRingHom_comp_stalkIso θ Q
  rw [← cancel_mono (Spec.stalkIso R' Q).inv]
  simp only [openImmersionStalkIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
    Category.assoc, Iso.hom_inv_id, Category.comp_id, hloc, TopCat.Presheaf.stalkCongr_hom]
  exact stalkMap_morphismRestrict_square b U g g' (Spec.map θ) hθ y' Q hQ _ _

end StalkChart

/-! ### A chart of the blowup through a point of `U'` -/

section Chart

variable (S : AlgebraizationSituation.{u})

/-- The ideal `I`, read on the global sections `Γ(X, 𝒪_X)` of `X = Spec(A)`: the ideal of the
affine blowup algebras `Γ(X, 𝒪_X)[I/a]` whose spectra are the charts of the blowup. -/
abbrev blowupCentreIdeal : Ideal Γ(S.X, ⊤) :=
  (Stacks.LocalCohomology.specIdealSheaf S.A S.I).ideal ⟨⊤, isAffineOpen_top _⟩

/-- **A chart of the blowup through a point `y'` of `U'`**: an element `a ∈ I` and a prime `Q` of
the affine blowup algebra `A[I/a]` whose image under the chart `Spec(A[I/a]) ⟶ X'` of
[Stacks, Tag 0804] is `y'`. -/
structure BlowupChartPoint (y' : (situationBlowUpU S).toScheme) where
  /-- The denominator of the chart. -/
  a : Γ(S.X, ⊤)
  ha : a ∈ blowupCentreIdeal S
  /-- The prime of the chart ring at `y'`. -/
  Q : PrimeSpectrum (affineBlowup (blowupCentreIdeal S) a)
  hQ : Stacks.Blowup.blowUpAffineChart (Stacks.LocalCohomology.specIdealSheaf S.A S.I)
    ⟨⊤, isAffineOpen_top _⟩ ha Q = (situationBlowUpU S).ι y'

/-- **Every point of `U'` lies on a chart of the blowup** ([Stacks, Tag 0804]). -/
theorem nonempty_blowupChartPoint (y' : (situationBlowUpU S).toScheme) :
    Nonempty (BlowupChartPoint S y') := by
  have h := Stacks.Blowup.iSup_opensRange_blowUpAffineChart
    (Stacks.LocalCohomology.specIdealSheaf S.A S.I) ⟨⊤, isAffineOpen_top _⟩
  have hmem : (situationBlowUpU S).ι y' ∈ ⨆ r : blowupCentreIdeal S,
      (Stacks.Blowup.blowUpAffineChart (Stacks.LocalCohomology.specIdealSheaf S.A S.I)
        ⟨⊤, isAffineOpen_top _⟩ r.2).opensRange := by
    rw [h]
    trivial
  obtain ⟨r, Q, hQ⟩ := TopologicalSpace.Opens.mem_iSup.mp hmem
  exact ⟨⟨r.1, r.2, Q, hQ⟩⟩

variable {S} {y' : (situationBlowUpU S).toScheme} (c : BlowupChartPoint S y')

/-- The chart ring `A[I/a]`. -/
abbrev BlowupChartPoint.ring : Type u := affineBlowup (blowupCentreIdeal S) c.a

/-- The chart `Spec(A[I/a]) ⟶ X'`. -/
abbrev BlowupChartPoint.chart : Spec (CommRingCat.of c.ring) ⟶ situationBlowUp S :=
  Stacks.Blowup.blowUpAffineChart (Stacks.LocalCohomology.specIdealSheaf S.A S.I)
    ⟨⊤, isAffineOpen_top _⟩ c.ha

/-- The chart, followed by the blowup, is `Spec` of the structure map `A → A[I/a]`. -/
theorem BlowupChartPoint.chart_comp_blowUpToBase :
    c.chart ≫ situationBlowUpToBase S =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S.X, ⊤) c.ring)) ≫
        (isAffineOpen_top S.X).fromSpec :=
  Stacks.Blowup.blowUpAffineChart_blowUpToBase _ _ c.ha

/-- The blowup map sends the image of `y'` in `X'` to the image of `y = b(y')` in `X`. -/
private theorem blowUpToBase_ι_apply (S : AlgebraizationSituation.{u})
    (y' : (situationBlowUpU S).toScheme) :
    situationBlowUpToBase S ((situationBlowUpU S).ι y') = S.U.ι (blowupRestrict S y') := by
  change ((situationBlowUpU S).ι ≫ situationBlowUpToBase S) y' = _
  rw [← morphismRestrict_ι]
  rfl

/-- The point of `Spec Γ(X, 𝒪_X)` under `y'` is the image of `y = b(y')`. -/
theorem BlowupChartPoint.fromSpec_comap :
    (isAffineOpen_top S.X).fromSpec
        (PrimeSpectrum.comap (CommRingCat.ofHom (algebraMap Γ(S.X, ⊤) c.ring)).hom c.Q) =
      S.U.ι (blowupRestrict S y') := by
  have h := congrArg (fun f => f c.Q) c.chart_comp_blowUpToBase
  refine Eq.trans h.symm ?_
  show situationBlowUpToBase S (c.chart c.Q) = _
  rw [c.hQ]
  exact blowUpToBase_ι_apply S y'

/-- **The local ring of `U` at `y = b(y')` is `A_𝔮`**, `𝔮 = Q ∩ A`. -/
def BlowupChartPoint.baseStalkEquiv :
    S.U.toScheme.presheaf.stalk (blowupRestrict S y') ≃+*
      Localization.AtPrime (c.Q.asIdeal.under Γ(S.X, ⊤)) :=
  (openImmersionStalkIso (isAffineOpen_top S.X).fromSpec S.U (blowupRestrict S y') _
    c.fromSpec_comap).commRingCatIsoToRingEquiv

/-- **The local ring of `U'` at `y'` is `A[I/a]_Q`.** -/
def BlowupChartPoint.chartStalkEquiv :
    (situationBlowUpU S).toScheme.presheaf.stalk y' ≃+* Localization.AtPrime c.Q.asIdeal :=
  (openImmersionStalkIso c.chart (situationBlowUpU S) y' c.Q c.hQ).commRingCatIsoToRingEquiv

/-- **The map of local rings induced by the blowup is the localization of `A → A[I/a]`.** -/
theorem BlowupChartPoint.chartStalkEquiv_stalkMap
    (x : S.U.toScheme.presheaf.stalk (blowupRestrict S y')) :
    c.chartStalkEquiv ((blowupRestrict S).stalkMap y' x) =
      Localization.localRingHom (c.Q.asIdeal.under Γ(S.X, ⊤)) c.Q.asIdeal
        (algebraMap Γ(S.X, ⊤) c.ring) rfl (c.baseStalkEquiv x) :=
  congrArg (fun f => f.hom x) (stalkMap_comp_openImmersionStalkIso
    (isAffineOpen_top S.X).fromSpec (situationBlowUpToBase S) S.U c.chart _
    c.chart_comp_blowUpToBase y' c.Q c.hQ c.fromSpec_comap)

/-- **The stalk of `I𝒪_U` at `y` is `I A_𝔮`.** -/
theorem BlowupChartPoint.map_stalk_idealOnOpen :
    (IdealSheafData.stalk (idealOnOpen S) (blowupRestrict S y')).map
        (c.baseStalkEquiv : _ →+* Localization.AtPrime (c.Q.asIdeal.under Γ(S.X, ⊤))) =
      (blowupCentreIdeal S).map
        (algebraMap Γ(S.X, ⊤) (Localization.AtPrime (c.Q.asIdeal.under Γ(S.X, ⊤)))) := by
  have h := map_stalk_openImmersionStalkIso (isAffineOpen_top S.X).fromSpec
    (Stacks.LocalCohomology.specIdealSheaf S.A S.I) S.U (blowupRestrict S y') _ c.fromSpec_comap
  have h2 : ((Stacks.LocalCohomology.specIdealSheaf S.A S.I).comap
      (isAffineOpen_top S.X).fromSpec).ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.map ((Scheme.ΓSpecIso Γ(S.X, ⊤)).inv).hom (blowupCentreIdeal S) :=
    Stacks.Blowup.ideal_comap_fromSpec_top _ ⟨⊤, isAffineOpen_top _⟩
  refine h.trans ?_
  rw [h2, Ideal.map_map, Ideal.map_map]
  congr 1
  refine RingHom.ext fun x => ?_
  simp only [RingHom.comp_apply, Iso.inv_hom_id_apply]
  rfl

/-- **The stalk of `I𝒪_{U'}` at `y'` is `I A[I/a]_Q`.** -/
theorem BlowupChartPoint.map_stalk_blowupIdealU :
    (IdealSheafData.stalk (blowupIdealU S) y').map
        (c.chartStalkEquiv : _ →+* Localization.AtPrime c.Q.asIdeal) =
      (blowupCentreIdeal S).map (algebraMap Γ(S.X, ⊤) (Localization.AtPrime c.Q.asIdeal)) := by
  have hcomp : (c.chartStalkEquiv : _ →+* Localization.AtPrime c.Q.asIdeal).comp
      ((blowupRestrict S).stalkMap y').hom =
      (Localization.localRingHom (c.Q.asIdeal.under Γ(S.X, ⊤)) c.Q.asIdeal
        (algebraMap Γ(S.X, ⊤) c.ring) rfl).comp
        (c.baseStalkEquiv : _ →+* Localization.AtPrime (c.Q.asIdeal.under Γ(S.X, ⊤))) :=
    RingHom.ext c.chartStalkEquiv_stalkMap
  have hloc : (Localization.localRingHom (c.Q.asIdeal.under Γ(S.X, ⊤)) c.Q.asIdeal
      (algebraMap Γ(S.X, ⊤) c.ring) rfl).comp
        (algebraMap Γ(S.X, ⊤) (Localization.AtPrime (c.Q.asIdeal.under Γ(S.X, ⊤)))) =
      algebraMap Γ(S.X, ⊤) (Localization.AtPrime c.Q.asIdeal) := by
    refine RingHom.ext fun x => ?_
    rw [RingHom.comp_apply, Localization.localRingHom_to_map]
    exact (IsScalarTower.algebraMap_apply Γ(S.X, ⊤) c.ring _ x).symm
  have e1 : IdealSheafData.stalk (blowupIdealU S) y' =
      (IdealSheafData.stalk (idealOnOpen S) (blowupRestrict S y')).map
        ((blowupRestrict S).stalkMap y').hom := by
    rw [← comap_idealOnOpen_blowupRestrict]
    exact IdealSheafData.stalk_comap _ _ _
  refine (congrArg (fun J => J.map (c.chartStalkEquiv : _ →+* Localization.AtPrime c.Q.asIdeal))
    e1).trans ?_
  simp only
  rw [Ideal.map_map, hcomp, ← Ideal.map_map]
  refine (congrArg (fun J => J.map (Localization.localRingHom (c.Q.asIdeal.under Γ(S.X, ⊤))
    c.Q.asIdeal (algebraMap Γ(S.X, ⊤) c.ring) rfl)) c.map_stalk_idealOnOpen).trans ?_
  exact (Ideal.map_map _ _).trans (congrArg (fun f => Ideal.map f (blowupCentreIdeal S)) hloc)

/-- **The completed local ring of `U` at `y` is `(A_𝔮)^∧`**, the `I`-adic completion. -/
def BlowupChartPoint.baseCompletionEquiv :
    completedLocalRing (idealOnOpen S) (blowupRestrict S y') ≃+*
      affineBlowupBaseCompletion (blowupCentreIdeal S) c.a c.Q.asIdeal :=
  letI : Algebra (S.U.toScheme.presheaf.stalk (blowupRestrict S y'))
      (Localization.AtPrime (c.Q.asIdeal.under Γ(S.X, ⊤))) := c.baseStalkEquiv.toRingHom.toAlgebra
  (AdicCompletion.congrAlgEquiv (AlgEquiv.ofRingEquiv
    (R := S.U.toScheme.presheaf.stalk (blowupRestrict S y'))
    (f := c.baseStalkEquiv) fun _ => rfl)
    c.map_stalk_idealOnOpen.symm).toRingEquiv

/-- **The completed local ring of `U'` at `y'` is `(A[I/a]_Q)^∧`**, the `I`-adic completion. -/
def BlowupChartPoint.chartCompletionEquiv :
    completedLocalRing (blowupIdealU S) y' ≃+*
      affineBlowupChartCompletion (blowupCentreIdeal S) c.a c.Q.asIdeal :=
  letI : Algebra ((situationBlowUpU S).toScheme.presheaf.stalk y')
      (Localization.AtPrime c.Q.asIdeal) := c.chartStalkEquiv.toRingHom.toAlgebra
  (AdicCompletion.congrAlgEquiv (AlgEquiv.ofRingEquiv
    (R := (situationBlowUpU S).toScheme.presheaf.stalk y')
    (f := c.chartStalkEquiv) fun _ => rfl)
    c.map_stalk_blowupIdealU.symm).toRingEquiv

/-- `BlowupChartPoint.baseCompletionEquiv` on the image of the local ring. -/
theorem BlowupChartPoint.baseCompletionEquiv_algebraMap
    (x : S.U.toScheme.presheaf.stalk (blowupRestrict S y')) :
    c.baseCompletionEquiv (algebraMap _ _ x) = algebraMap _ _ (c.baseStalkEquiv x) := by
  let : Algebra (S.U.toScheme.presheaf.stalk (blowupRestrict S y'))
      (Localization.AtPrime (c.Q.asIdeal.under Γ(S.X, ⊤))) := c.baseStalkEquiv.toRingHom.toAlgebra
  exact AdicCompletion.congrAlgEquiv_of (AlgEquiv.ofRingEquiv
    (R := S.U.toScheme.presheaf.stalk (blowupRestrict S y'))
    (f := c.baseStalkEquiv) fun _ => rfl)
    c.map_stalk_idealOnOpen.symm x

/-- `BlowupChartPoint.chartCompletionEquiv` on the image of the local ring. -/
theorem BlowupChartPoint.chartCompletionEquiv_algebraMap
    (x : (situationBlowUpU S).toScheme.presheaf.stalk y') :
    c.chartCompletionEquiv (algebraMap _ _ x) = algebraMap _ _ (c.chartStalkEquiv x) := by
  let : Algebra ((situationBlowUpU S).toScheme.presheaf.stalk y')
      (Localization.AtPrime c.Q.asIdeal) := c.chartStalkEquiv.toRingHom.toAlgebra
  exact AdicCompletion.congrAlgEquiv_of (AlgEquiv.ofRingEquiv
    (R := (situationBlowUpU S).toScheme.presheaf.stalk y')
    (f := c.chartStalkEquiv) fun _ => rfl)
    c.map_stalk_blowupIdealU.symm x

end Chart

/-! ### Residue field extensions -/

section ResidueField

/-- Two residue-field comparison maps compose to one. -/
theorem residueFieldCongr_comp_comp {X : Scheme.{u}} {a b c : X} (h₁ : a = b) (h₂ : b = c)
    (h₃ : a = c) {Z : CommRingCat.{u}} (t : X.residueField c ⟶ Z) :
    (X.residueFieldCongr h₁).hom ≫ (X.residueFieldCongr h₂).hom ≫ t =
      (X.residueFieldCongr h₃).hom ≫ t := by
  rw [Scheme.residueFieldCongr_trans_hom_assoc]

/-- The residue field maps of a commutative square of schemes, read between equal points. -/
theorem residueFieldMap_square {X X' Z Z' : Scheme.{u}} (b : X' ⟶ X) (g : Z ⟶ X)
    (g' : Z' ⟶ X') (h : Z' ⟶ Z) (w : g' ≫ b = h ≫ g) (a : X) (x' : X') (z : Z')
    (h₁ : a = b x') (h₂ : x' = g' z) (h₃ : a = g (h z)) :
    (X.residueFieldCongr h₁).hom ≫ b.residueFieldMap x' ≫ (X'.residueFieldCongr h₂).hom ≫
        g'.residueFieldMap z =
      (X.residueFieldCongr h₃).hom ≫ g.residueFieldMap (h z) ≫ h.residueFieldMap z := by
  subst h₂
  rw [Scheme.residueFieldCongr_refl, Iso.refl_hom, Category.id_comp, ← Scheme.residueFieldMap_comp,
    Scheme.Hom.residueFieldMap_congr w, Scheme.residueFieldMap_comp]
  exact residueFieldCongr_comp_comp _ _ _ _

/-- **Residue field extensions across two stacked squares.** -/
theorem trdeg_residueField_eq_of_squares {E Y X' X Z' Z : Scheme.{u}} (q : E ⟶ Y) (ι : E ⟶ X')
    (j : Y ⟶ X) (b : X' ⟶ X) (g' : Z' ⟶ X') (g : Z ⟶ X) (h : Z' ⟶ Z)
    (w₁ : q ≫ j = ι ≫ b) (w₂ : g' ≫ b = h ≫ g) [SurjectiveOnStalks ι] [SurjectiveOnStalks j]
    [IsOpenImmersion g'] [IsOpenImmersion g] (e : E) (z : Z') (hz : ι e = g' z) :
    letI := (q.residueFieldMap e).hom.toAlgebra
    letI := (h.residueFieldMap z).hom.toAlgebra
    Algebra.trdeg (Y.residueField (q e)) (E.residueField e) =
      Algebra.trdeg (Z.residueField (h z)) (Z'.residueField z) := by
  have pK : j (q e) = g (h z) := by
    rw [← Scheme.Hom.comp_apply, w₁, Scheme.Hom.comp_apply, hz, ← Scheme.Hom.comp_apply, w₂,
      Scheme.Hom.comp_apply]
  have : IsIso (j.residueFieldMap (q e)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (j.bijective_residueFieldMap (q e))
  have : IsIso (ι.residueFieldMap e) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (ι.bijective_residueFieldMap e)
  let eK : Y.residueField (q e) ≅ Z.residueField (h z) :=
    (asIso (j.residueFieldMap (q e))).symm ≪≫ X.residueFieldCongr pK ≪≫
      asIso (g.residueFieldMap (h z))
  let eL : E.residueField e ≅ Z'.residueField z :=
    (asIso (ι.residueFieldMap e)).symm ≪≫ X'.residueFieldCongr hz ≪≫ asIso (g'.residueFieldMap z)
  have hsq : q.residueFieldMap e ≫ eL.hom = eK.hom ≫ h.residueFieldMap z := by
    simp only [eK, eL, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, Category.assoc]
    rw [IsIso.eq_inv_comp, ← Category.assoc, ← Scheme.residueFieldMap_comp,
      Scheme.Hom.residueFieldMap_congr w₁, Scheme.residueFieldMap_comp]
    refine (comp_comp_comp_inv_comp _ _ _ _).trans ?_
    exact residueFieldMap_square b g g' h w₂ _ _ z _ hz _
  let := (q.residueFieldMap e).hom.toAlgebra
  let := (h.residueFieldMap z).hom.toAlgebra
  exact Algebra.trdeg_eq_of_ringEquiv eK.commRingCatIsoToRingEquiv eL.commRingCatIsoToRingEquiv
    fun a => congrArg (fun f => f.hom a) hsq

/-- **Residue field extensions of a morphism of affine schemes**: the residue field extension of
`Spec R' ⟶ Spec R` at `Q` is `κ(Q ∩ R) → κ(Q)`. -/
theorem trdeg_residueField_specMap {R R' : CommRingCat.{u}} (θ : R ⟶ R')
    (Q : PrimeSpectrum R') :
    letI := ((Spec.map θ).residueFieldMap (show Spec R' from Q)).hom.toAlgebra
    letI := (Ideal.ResidueField.map (Q.asIdeal.comap θ.hom) Q.asIdeal θ.hom rfl).toAlgebra
    Algebra.trdeg ((Spec R).residueField (Spec.map θ (show Spec R' from Q)))
        ((Spec R').residueField (show Spec R' from Q)) =
      Algebra.trdeg (Q.asIdeal.comap θ.hom).ResidueField Q.asIdeal.ResidueField := by
  let x : Spec R' := Q
  let eK : (Spec R).residueField (Spec.map θ x) ≃+* (Q.asIdeal.comap θ.hom).ResidueField :=
    (Scheme.Spec.residueFieldIso R (Spec.map θ x)).commRingCatIsoToRingEquiv
  let eL : (Spec R').residueField x ≃+* Q.asIdeal.ResidueField :=
    (Scheme.Spec.residueFieldIso R' x).commRingCatIsoToRingEquiv
  let := ((Spec.map θ).residueFieldMap x).hom.toAlgebra
  let := (Ideal.ResidueField.map (Q.asIdeal.comap θ.hom) Q.asIdeal θ.hom rfl).toAlgebra
  refine Algebra.trdeg_eq_of_ringEquiv eK eL fun t => ?_
  obtain ⟨s, rfl⟩ := (Spec R).residue_surjective (Spec.map θ x) t
  have h1 := congrArg (fun f => f.hom s) (Scheme.residue_residueFieldMap (Spec.map θ) x)
  have h2 := congrArg (fun f => f.hom s) (Scheme.localRingHom_comp_stalkIso θ Q)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h1 h2
  have h3 : (Spec.stalkIso R' Q).hom.hom (((Spec.map θ).stalkMap x).hom s) =
      Localization.localRingHom (Q.asIdeal.comap θ.hom) Q.asIdeal θ.hom rfl
        ((Spec.stalkIso R (PrimeSpectrum.comap θ.hom Q)).hom.hom s) :=
    (congrArg (Spec.stalkIso R' Q).hom.hom h2).symm.trans
      (Iso.inv_hom_id_apply (Spec.stalkIso R' Q) _)
  have := Localization.isLocalHom_localRingHom (Q.asIdeal.comap θ.hom) Q.asIdeal θ.hom rfl
  show eL (((Spec.map θ).residueFieldMap x).hom (((Spec R).residue _).hom s)) =
    Ideal.ResidueField.map (Q.asIdeal.comap θ.hom) Q.asIdeal θ.hom rfl (eK _)
  rw [h1]
  exact (congrArg (IsLocalRing.residue (Localization.AtPrime Q.asIdeal)) h3).trans
    (IsLocalRing.ResidueField.map_residue _ _).symm


/-- **The residue field extension of `Y' ⟶ Y` at a point of the chart** is `κ(𝔮) → κ(Q)`. -/
theorem BlowupChartPoint.trdeg_residueField_eq {S : AlgebraizationSituation.{u}}
    {y' : (situationBlowUpU S).toScheme} (c : BlowupChartPoint S y') (e' : situationExceptional S)
    (he' : situationExceptionalι S e' = (situationBlowUpU S).ι y') :
    letI := ((exceptionalToY S).residueFieldMap e').hom.toAlgebra
    letI := Ideal.ResidueField.algebraOfLiesOver (c.Q.asIdeal.under Γ(S.X, ⊤)) c.Q.asIdeal
    Algebra.trdeg (S.Y.residueField (exceptionalToY S e'))
        ((situationExceptional S).residueField e') =
      Algebra.trdeg (c.Q.asIdeal.under Γ(S.X, ⊤)).ResidueField c.Q.asIdeal.ResidueField := by
  have h1 := trdeg_residueField_eq_of_squares (exceptionalToY S) (situationExceptionalι S) S.Yι
    (situationBlowUpToBase S) c.chart (isAffineOpen_top S.X).fromSpec _ (exceptionalToY_Yι S)
    c.chart_comp_blowUpToBase e' c.Q (he'.trans c.hQ.symm)
  have h2 := trdeg_residueField_specMap
    (CommRingCat.ofHom (R := Γ(S.X, ⊤)) (algebraMap Γ(S.X, ⊤) c.ring)) c.Q
  exact h1.trans h2

end ResidueField

/-! ### The arithmetic, the fibres and the catenary hypothesis -/

section Arithmetic

/-- The sum of two integers in the extended integers. -/
theorem eint_coe_add (a b : ℤ) : ((a : ℤ) : EInt) + ((b : ℤ) : EInt) = ((a + b : ℤ) : EInt) :=
  (Stacks.Chow.coe_add_coe_eq_coe_add a b).symm

/-- **The arithmetic of (0EJL).** If `D + m ≤ D' + m' + t` and `δ + t ≤ δ' + e` with `m'` not
`⊥`, then `D + m + δ ≤ D' + m' + δ' + e`, all read in the extended integers; the quantities are
given through equations so that the inequality applies to any expressions for them. -/
theorem depth_dim_distance_combine {D₀ D D₀' D' t δ δ' : ℕ∞} {m₀ m m₀' m' : WithBot ℕ∞}
    {e : ℕ} {k : ℤ} (hD : D₀ = D) (hm : m₀ = m) (hD' : D₀' = D') (hm'' : m₀' = m')
    (hk : (e : ℤ) = k)
    (h₁ : enatToEInt D + krullDimToEInt m ≤ enatToEInt D' + krullDimToEInt m' + enatToEInt t)
    (h₂ : δ + t ≤ δ' + e) (hm' : m' ≠ ⊥) :
    enatToEInt D₀ + krullDimToEInt m₀ + enatToEInt δ ≤
      enatToEInt D₀' + krullDimToEInt m₀' + enatToEInt δ' + ((k : ℤ) : EInt) := by
  subst D₀ m₀ D₀' m₀' k
  cases m' using WithBot.recBotCoe with
  | bot => exact absurd rfl hm'
  | coe m' =>
  cases δ' using ENat.recTopCoe with
  | top =>
    cases D' using ENat.recTopCoe <;> cases m' using ENat.recTopCoe <;> exact le_top
  | coe n' =>
  cases D' using ENat.recTopCoe with
  | top => cases m' using ENat.recTopCoe <;> exact le_top
  | coe a' =>
  cases m' using ENat.recTopCoe with
  | top => exact le_top
  | coe k' =>
  cases t using ENat.recTopCoe with
  | top => simp at h₂
  | coe k =>
  cases δ using ENat.recTopCoe with
  | top => simp at h₂
  | coe j =>
  have h₂' : j + k ≤ n' + e := by exact_mod_cast h₂
  have hno : ¬ (⊤ : EInt) ≤ enatToEInt (a' : ℕ∞) + krullDimToEInt ((k' : ℕ∞) : WithBot ℕ∞) +
      enatToEInt (k : ℕ∞) := by
    change ¬ (⊤ : EInt) ≤ ((a' : ℤ) : EInt) + ((k' : ℤ) : EInt) + ((k : ℤ) : EInt)
    simp only [eint_coe_add, top_le_iff]
    exact WithBotTop.coe_ne_top _
  cases m using WithBot.recBotCoe with
  | bot => cases D using ENat.recTopCoe <;> exact bot_le
  | coe m =>
  cases D using ENat.recTopCoe with
  | top =>
    have hl : enatToEInt ⊤ + krullDimToEInt (m : WithBot ℕ∞) = ⊤ := by
      cases m using ENat.recTopCoe <;> rfl
    rw [hl] at h₁
    exact absurd h₁ hno
  | coe a =>
  cases m using ENat.recTopCoe with
  | top =>
    have hl : enatToEInt (a : ℕ∞) + krullDimToEInt ((⊤ : ℕ∞) : WithBot ℕ∞) = ⊤ := rfl
    rw [hl] at h₁
    exact absurd h₁ hno
  | coe mm =>
  change ((a : ℤ) : EInt) + ((mm : ℤ) : EInt) ≤ ((a' : ℤ) : EInt) + ((k' : ℤ) : EInt) +
    ((k : ℤ) : EInt) at h₁
  show ((a : ℤ) : EInt) + ((mm : ℤ) : EInt) + ((j : ℤ) : EInt) ≤
    ((a' : ℤ) : EInt) + ((k' : ℤ) : EInt) + ((n' : ℤ) : EInt) + ((e : ℤ) : EInt)
  simp only [eint_coe_add, WithBotTop.coe_le_coe] at h₁ ⊢
  omega

end Arithmetic

section Fibre

variable (S : AlgebraizationSituation.{u})

/-- **A point of the exceptional divisor forces `d ≥ 1`**: its fibre over `Y` is nonempty, so the
fibres of the blowup cannot all have dimension `< 0`. -/
theorem one_le_of_blowup_point (d : ℤ)
    (hfib : ∀ y : Spec (CommRingCat.of S.A), topologicalKrullDim ((AlgebraicGeometry.blowUpToBase
      (Stacks.LocalCohomology.specIdealSheaf S.A S.I)).fiber y) < ((d.toNat : ℕ) : WithBot ℕ∞))
    (e' : situationExceptional S) : 1 ≤ d := by
  have hne : Nonempty (TopologicalSpace.IrreducibleCloseds
      ((exceptionalToY S).fiber (exceptionalToY S e'))) := by
    obtain x := ((exceptionalToY S).fiberHomeo (exceptionalToY S e')).symm ⟨e', rfl⟩
    exact ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  have h0 : (0 : WithBot ℕ∞) ≤ topologicalKrullDim
      ((exceptionalToY S).fiber (exceptionalToY S e')) := Order.krullDim_nonneg
  have h := (h0.trans (topologicalKrullDim_fiber_exceptionalToY_le S _)).trans_lt
    (hfib (S.Yι (exceptionalToY S e')))
  have h' : (0 : ℕ) < d.toNat := by exact_mod_cast h
  omega

/-- The fibres of `Y' ⟶ Y` have dimension at most `d - 1` when those of the blowup have
dimension `< d`. -/
theorem topologicalKrullDim_fiber_exceptionalToY_le_pred (d : ℤ)
    (hfib : ∀ y : Spec (CommRingCat.of S.A), topologicalKrullDim ((AlgebraicGeometry.blowUpToBase
      (Stacks.LocalCohomology.specIdealSheaf S.A S.I)).fiber y) < ((d.toNat : ℕ) : WithBot ℕ∞))
    (y : S.Y) :
    topologicalKrullDim ((exceptionalToY S).fiber y) ≤ ((d.toNat - 1 : ℕ) : WithBot ℕ∞) := by
  have h := (topologicalKrullDim_fiber_exceptionalToY_le S y).trans_lt (hfib (S.Yι y))
  generalize topologicalKrullDim ((exceptionalToY S).fiber y) = x at h ⊢
  cases x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe x =>
  cases x using ENat.recTopCoe with
  | top => exact absurd h (not_lt.mpr (WithBot.coe_le_coe.mpr le_top))
  | coe k =>
  have hk : k < d.toNat := by exact_mod_cast h
  exact WithBot.coe_le_coe.mpr (ENat.coe_le_coe.mpr (show k ≤ d.toNat - 1 by omega))

/-- **`Y` is universally catenary** when `A` has a dualizing complex ([Stacks, Tag 0AWY] and
[Stacks, Tag 0A80]). -/
theorem isUniversallyCatenary_situationY
    (hdual : ∃ K : @DerivedCategory (ModuleCat.{u} S.A) _ _
      (HasDerivedCategory.standard (ModuleCat.{u} S.A)),
      @Dualizing.IsDualizingComplex S.A _ _ (HasDerivedCategory.standard (ModuleCat.{u} S.A)) K) :
    Scheme.IsUniversallyCatenary S.Y := by
  obtain ⟨K, hK⟩ := hdual
  let := HasDerivedCategory.standard (ModuleCat.{u} S.A)
  exact isUniversallyCatenary_of_locallyHasDualizingComplex _
    (locallyHasDualizingComplex_of_locallyOfFiniteType S.Yι K hK)

end Fibre

/-! ### The comparison on a chart -/

section Comparison

variable {S : AlgebraizationSituation.{u}} {y' : (situationBlowUpU S).toScheme}
  (c : BlowupChartPoint S y')

/-- `Γ(X, 𝒪_X)` is Noetherian, being isomorphic to `A`. -/
instance isNoetherianRing_situationGlobalSections (S : AlgebraizationSituation.{u}) :
    IsNoetherianRing Γ(S.X, ⊤) :=
  isNoetherianRing_of_ringEquiv S.A
    (Scheme.ΓSpecIso (CommRingCat.of S.A)).symm.commRingCatIsoToRingEquiv

/-- The completed stalk of `(ℱₙ)` at `y = b(y')`, as a module over `(A_𝔮)^∧`. -/
abbrev BlowupChartPoint.baseModule (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) :
    Module (affineBlowupBaseCompletion (blowupCentreIdeal S) c.a c.Q.asIdeal)
      (completedStalk (idealOnOpen S) F (blowupRestrict S y')) :=
  Module.compHom _ c.baseCompletionEquiv.symm.toRingHom

/-- `(A[I/a]_Q)^∧` as an algebra over `(A_𝔮)^∧`. -/
abbrev BlowupChartPoint.completionAlgebra :
    Algebra (affineBlowupBaseCompletion (blowupCentreIdeal S) c.a c.Q.asIdeal)
      (affineBlowupChartCompletion (blowupCentreIdeal S) c.a c.Q.asIdeal) :=
  (affineBlowupCompletionMap (blowupCentreIdeal S) c.a c.Q.asIdeal).toAlgebra

attribute [local instance] BlowupChartPoint.baseModule BlowupChartPoint.completionAlgebra

/-- **The comparison of completed stalks along the chart**: an additive identification of the
completed stalk `(b^*ℱ)^∧_{y'}` of the pullback with `(A[I/a]_Q)^∧ ⊗_{(A_𝔮)^∧} ℱ^∧_y`, semilinear
over `BlowupChartPoint.chartCompletionEquiv`. This is the identification
`(ℱ_y^∧)_𝔭 ⊗ (𝒪_{X',y'}^∧)_{𝔭'} = (ℱ_{y'}^∧)_{𝔭'}` of the proof of [Stacks, Tag 0EJK] before
localization. -/
def BlowupChartPoint.CompletedStalkComparison
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) : Prop :=
  ∃ Φ : completedStalk (blowupIdealU S) (blowupPullbackSystem S F) y' ≃+
      TensorProduct (affineBlowupBaseCompletion (blowupCentreIdeal S) c.a c.Q.asIdeal)
        (affineBlowupChartCompletion (blowupCentreIdeal S) c.a c.Q.asIdeal)
        (completedStalk (idealOnOpen S) F (blowupRestrict S y')),
    ∀ r x, Φ (r • x) = c.chartCompletionEquiv r • Φ x

/-- The completed stalk of `(ℱₙ)` at `y` is finite over `(A_𝔮)^∧`. -/
theorem BlowupChartPoint.finite_baseModule
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) :
    Module.Finite (affineBlowupBaseCompletion (blowupCentreIdeal S) c.a c.Q.asIdeal)
      (completedStalk (idealOnOpen S) F (blowupRestrict S y')) := by
  have := finite_completedStalk (idealOnOpen S) F (blowupRestrict S y')
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := completedLocalRing (idealOnOpen S)
    (blowupRestrict S y')) (M := completedStalk (idealOnOpen S) F (blowupRestrict S y'))
  refine ⟨⟨s, eq_top_iff.mpr fun x hx0 => ?_⟩⟩
  clear hx0
  have hx : x ∈ Submodule.span (completedLocalRing (idealOnOpen S) (blowupRestrict S y'))
      (s : Set _) := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x h => exact Submodule.subset_span h
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul r x _ hx =>
    have h : r • x = (c.baseCompletionEquiv r) • x := by
      show r • x = c.baseCompletionEquiv.symm (c.baseCompletionEquiv r) • x
      rw [RingEquiv.symm_apply_apply]
    rw [h]
    exact Submodule.smul_mem _ _ hx

/-- The image of `a ∈ Γ(X, 𝒪_X)` in `(A_𝔮)^∧`, read in the completed local ring of `U` at `y`. -/
theorem BlowupChartPoint.baseCompletionEquiv_symm_algebraMap (a : Γ(S.X, ⊤)) :
    c.baseCompletionEquiv.symm (algebraMap Γ(S.X, ⊤)
        (affineBlowupBaseCompletion (blowupCentreIdeal S) c.a c.Q.asIdeal) a) =
      algebraMap _ (completedLocalRing (idealOnOpen S) (blowupRestrict S y'))
        (c.baseStalkEquiv.symm (algebraMap Γ(S.X, ⊤) _ a)) := by
  apply c.baseCompletionEquiv.injective
  rw [RingEquiv.apply_symm_apply, c.baseCompletionEquiv_algebraMap, RingEquiv.apply_symm_apply]
  rfl

/-- The image of `a ∈ Γ(X, 𝒪_X)` in `(A[I/a]_Q)^∧`, read in the completed local ring of `U'` at
`y'`. -/
theorem BlowupChartPoint.chartCompletionEquiv_symm_algebraMap (a : Γ(S.X, ⊤)) :
    c.chartCompletionEquiv.symm (algebraMap Γ(S.X, ⊤)
        (affineBlowupChartCompletion (blowupCentreIdeal S) c.a c.Q.asIdeal) a) =
      algebraMap _ (completedLocalRing (blowupIdealU S) y')
        (c.chartStalkEquiv.symm (algebraMap Γ(S.X, ⊤) _ a)) := by
  apply c.chartCompletionEquiv.injective
  rw [RingEquiv.apply_symm_apply, c.chartCompletionEquiv_algebraMap, RingEquiv.apply_symm_apply]
  rfl

/-- `I𝒪_{X',y'}^∧ ⊆ 𝔭'` exactly when the image of `I` in `(A[I/a]_Q)^∧` lies in the
corresponding prime. -/
theorem BlowupChartPoint.completedLocalIdeal_le_of_map_le
    (p' : Ideal (completedLocalRing (blowupIdealU S) y'))
    (h : (blowupCentreIdeal S).map (algebraMap Γ(S.X, ⊤)
      (affineBlowupChartCompletion (blowupCentreIdeal S) c.a c.Q.asIdeal)) ≤
        p'.comap c.chartCompletionEquiv.symm.toRingHom) :
    completedLocalIdeal (blowupIdealU S) y' ≤ p' := by
  rw [completedLocalIdeal, Ideal.map_le_iff_le_comap]
  intro x hx
  have hx' : c.chartStalkEquiv x ∈ (blowupCentreIdeal S).map
      (algebraMap Γ(S.X, ⊤) (Localization.AtPrime c.Q.asIdeal)) := by
    rw [← c.map_stalk_blowupIdealU]
    exact Ideal.mem_map_of_mem _ hx
  have key : (blowupCentreIdeal S).map (algebraMap Γ(S.X, ⊤) (Localization.AtPrime c.Q.asIdeal)) ≤
      p'.comap ((algebraMap _ (completedLocalRing (blowupIdealU S) y')).comp
        c.chartStalkEquiv.symm.toRingHom) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    have := h (Ideal.mem_map_of_mem _ ha)
    simp only [Ideal.mem_comap, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingHom.comp_apply]
      at this ⊢
    rwa [c.chartCompletionEquiv_symm_algebraMap] at this
  simpa using key hx'


variable (P' : Ideal (affineBlowupChartCompletion (blowupCentreIdeal S) c.a c.Q.asIdeal))
  [P'.IsPrime]

/-- The prime of `𝒪_{X,y}^∧` under a prime of `(A[I/a]_Q)^∧`. -/
abbrev BlowupChartPoint.basePrime :
    PrimeSpectrum (completedLocalRing (idealOnOpen S) (blowupRestrict S y')) :=
  ⟨(P'.comap (affineBlowupCompletionMap (blowupCentreIdeal S) c.a c.Q.asIdeal)).comap
    c.baseCompletionEquiv.toRingHom, inferInstance⟩

/-- If the prime `P'` does not contain `I`, neither does the prime of `𝒪_{X,y}^∧` under it. -/
theorem BlowupChartPoint.not_completedLocalIdeal_le_basePrime
    (hP' : ¬ (blowupCentreIdeal S).map (algebraMap Γ(S.X, ⊤)
      (affineBlowupChartCompletion (blowupCentreIdeal S) c.a c.Q.asIdeal)) ≤ P') :
    ¬ completedLocalIdeal (idealOnOpen S) (blowupRestrict S y') ≤ (c.basePrime P').asIdeal := by
  intro h
  apply hP'
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  have hst : c.baseStalkEquiv.symm (algebraMap Γ(S.X, ⊤) _ a) ∈
      IdealSheafData.stalk (idealOnOpen S) (blowupRestrict S y') := by
    have hmem : algebraMap Γ(S.X, ⊤) (Localization.AtPrime (c.Q.asIdeal.under Γ(S.X, ⊤))) a ∈
        (IdealSheafData.stalk (idealOnOpen S) (blowupRestrict S y')).map
          (c.baseStalkEquiv : _ →+* Localization.AtPrime (c.Q.asIdeal.under Γ(S.X, ⊤))) := by
      rw [c.map_stalk_idealOnOpen]
      exact Ideal.mem_map_of_mem _ ha
    rwa [Ideal.map_comap_of_equiv] at hmem
  have h2 := h (Ideal.mem_map_of_mem (algebraMap _ _) hst)
  rw [← c.baseCompletionEquiv_symm_algebraMap] at h2
  change affineBlowupCompletionMap (blowupCentreIdeal S) c.a c.Q.asIdeal
    (c.baseCompletionEquiv (c.baseCompletionEquiv.symm (algebraMap Γ(S.X, ⊤) _ a))) ∈ P' at h2
  rwa [RingEquiv.apply_symm_apply, affineBlowupCompletionMap_algebraMap_base] at h2

/-- The depth of the completed stalk of `(ℱₙ)` at the prime under `P'`, read over `(A_𝔮)^∧`. -/
theorem BlowupChartPoint.completedStalkDepth_basePrime
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) :
    completedStalkDepth (idealOnOpen S) F (blowupRestrict S y') (c.basePrime P') =
      Module.depth (Localization.AtPrime
          (P'.comap (affineBlowupCompletionMap (blowupCentreIdeal S) c.a c.Q.asIdeal)))
        (maximalIdeal _) (LocalizedModule
          (P'.comap (affineBlowupCompletionMap (blowupCentreIdeal S) c.a c.Q.asIdeal)).primeCompl
          (completedStalk (idealOnOpen S) F (blowupRestrict S y'))) :=
  LocalizedModule.depth_atPrime_comap_eq_of_ringEquiv c.baseCompletionEquiv (AddEquiv.refl _)
    (fun r m => by
      show r • m = c.baseCompletionEquiv.symm (c.baseCompletionEquiv r) • m
      rw [RingEquiv.symm_apply_apply]) _

/-- The dimension of `𝒪_{X,y}^∧` modulo the prime under `P'`. -/
theorem BlowupChartPoint.ringKrullDim_basePrime :
    ringKrullDim (completedLocalRing (idealOnOpen S) (blowupRestrict S y') ⧸
        (c.basePrime P').asIdeal) =
      ringKrullDim (affineBlowupBaseCompletion (blowupCentreIdeal S) c.a c.Q.asIdeal ⧸
        P'.comap (affineBlowupCompletionMap (blowupCentreIdeal S) c.a c.Q.asIdeal)) :=
  ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ c.baseCompletionEquiv
    (Ideal.map_comap_of_surjective _ c.baseCompletionEquiv.surjective _).symm)

variable {P'}

/-- The depth of the completed stalk of the pullback, read over `(A[I/a]_Q)^∧` through a
comparison of the completed stalks. -/
theorem BlowupChartPoint.completedStalkDepth_of_comparison
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (p' : PrimeSpectrum (completedLocalRing (blowupIdealU S) y'))
    (hP'def : p'.asIdeal.comap c.chartCompletionEquiv.symm.toRingHom = P')
    (hc : c.CompletedStalkComparison F) :
    completedStalkDepth (blowupIdealU S) (blowupPullbackSystem S F) y' p' =
      Module.depth (Localization.AtPrime P') (maximalIdeal _)
        (LocalizedModule P'.primeCompl (TensorProduct
          (affineBlowupBaseCompletion (blowupCentreIdeal S) c.a c.Q.asIdeal)
          (affineBlowupChartCompletion (blowupCentreIdeal S) c.a c.Q.asIdeal)
          (completedStalk (idealOnOpen S) F (blowupRestrict S y')))) := by
  obtain ⟨Φ, hΦ⟩ := hc
  have key : ∀ (q : Ideal (completedLocalRing (blowupIdealU S) y')) [q.IsPrime],
      P'.comap (c.chartCompletionEquiv : _ →+* _) = q →
      Module.depth (Localization.AtPrime q) (maximalIdeal _) (LocalizedModule q.primeCompl
        (completedStalk (blowupIdealU S) (blowupPullbackSystem S F) y')) =
      Module.depth (Localization.AtPrime P') (maximalIdeal _)
        (LocalizedModule P'.primeCompl (TensorProduct
          (affineBlowupBaseCompletion (blowupCentreIdeal S) c.a c.Q.asIdeal)
          (affineBlowupChartCompletion (blowupCentreIdeal S) c.a c.Q.asIdeal)
          (completedStalk (idealOnOpen S) F (blowupRestrict S y')))) := by
    intro q _ hq
    subst hq
    exact LocalizedModule.depth_atPrime_comap_eq_of_ringEquiv c.chartCompletionEquiv Φ hΦ P'
  refine key p'.asIdeal ?_
  subst hP'def
  ext x
  simp

omit [P'.IsPrime] in
/-- The dimension of `𝒪_{X',y'}^∧` modulo a prime, read on `(A[I/a]_Q)^∧`. -/
theorem BlowupChartPoint.ringKrullDim_chartPrime
    (p' : PrimeSpectrum (completedLocalRing (blowupIdealU S) y'))
    (hP'def : p'.asIdeal.comap c.chartCompletionEquiv.symm.toRingHom = P') :
    ringKrullDim (completedLocalRing (blowupIdealU S) y' ⧸ p'.asIdeal) =
      ringKrullDim (affineBlowupChartCompletion (blowupCentreIdeal S) c.a c.Q.asIdeal ⧸ P') :=
  ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ c.chartCompletionEquiv
    (hP'def ▸ Ideal.comap_symm c.chartCompletionEquiv))

/-- **(0EJL) and (0EJM) on a chart, given the comparison of completed stalks.** Let `A` have a
dualizing complex, let the fibres of the blowup have dimension `< d`, and let `y'` be a point of
`U'` on the exceptional divisor with a prime `𝔭'` of `𝒪_{X',y'}^∧` not containing `I`. For a
chart through `y'` along which the completed stalk of the pullback is the base change of the
completed stalk at `y = b(y')`, the prime `𝔭` of `𝒪_{X,y}^∧` under `𝔭'` satisfies
`depth + dim + δ^Y_Z(y) ≤ depth' + dim' + δ^{Y'}_{Z'}(y') + (d - 1)` and `dim' ≤ dim`. -/
theorem exists_depthAddDimAddDistance_le_blowup_of_comparison (S : AlgebraizationSituation.{u})
    (hdual : ∃ K : @DerivedCategory (ModuleCat.{u} S.A) _ _
      (HasDerivedCategory.standard (ModuleCat.{u} S.A)),
      @Dualizing.IsDualizingComplex S.A _ _ (HasDerivedCategory.standard (ModuleCat.{u} S.A)) K)
    (d : ℤ)
    (hfib : ∀ y : Spec (CommRingCat.of S.A), topologicalKrullDim ((AlgebraicGeometry.blowUpToBase
      (Stacks.LocalCohomology.specIdealSheaf S.A S.I)).fiber y) < ((d.toNat : ℕ) : WithBot ℕ∞))
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (y' : (situationBlowUpU S).toScheme) (e' : situationExceptional S)
    (he' : situationExceptionalι S e' = (situationBlowUpU S).ι y')
    (p' : PrimeSpectrum (completedLocalRing (blowupIdealU S) y'))
    (hp' : ¬ completedLocalIdeal (blowupIdealU S) y' ≤ p'.asIdeal)
    (c : BlowupChartPoint S y') (hc : c.CompletedStalkComparison F) :
    ∃ (y : S.U.toScheme) (z : S.Y) (_ : S.U.ι.base y = S.Yι.base z)
      (p : PrimeSpectrum (completedLocalRing (idealOnOpen S) y)),
      ¬ completedLocalIdeal (idealOnOpen S) y ≤ p.asIdeal ∧
      depthAddDimAddDistance S F y z p ≤
        enatToEInt (completedStalkDepth (blowupIdealU S) (blowupPullbackSystem S F) y' p') +
          krullDimToEInt (ringKrullDim (completedLocalRing (blowupIdealU S) y' ⧸ p'.asIdeal)) +
          enatToEInt (exceptionalDistance S e') + ((d - 1 : ℤ) : EInt) ∧
      krullDimToEInt (ringKrullDim (completedLocalRing (blowupIdealU S) y' ⧸ p'.asIdeal)) ≤
        krullDimToEInt (ringKrullDim (completedLocalRing (idealOnOpen S) y ⧸ p.asIdeal)) := by
  have := c.finite_baseModule F
  obtain ⟨P', hP'def⟩ : ∃ P' : Ideal (affineBlowupChartCompletion (blowupCentreIdeal S) c.a
      c.Q.asIdeal), p'.asIdeal.comap c.chartCompletionEquiv.symm.toRingHom = P' := ⟨_, rfl⟩
  have : P'.IsPrime := hP'def ▸ Ideal.comap_isPrime _ _
  have hdual₀ : ∃ K : @DerivedCategory (ModuleCat.{u} Γ(S.X, ⊤)) _ _
      (HasDerivedCategory.standard _), @Dualizing.IsDualizingComplex Γ(S.X, ⊤) _ _
        (HasDerivedCategory.standard (ModuleCat.{u} Γ(S.X, ⊤))) K := by
    obtain ⟨K, hK⟩ := hdual
    let := HasDerivedCategory.standard (ModuleCat.{u} S.A)
    obtain ⟨ω, hω⟩ :=
      locallyHasDualizingComplex_of_locallyOfFiniteType (𝟙 S.X) K hK ⟨⊤, isAffineOpen_top _⟩
    exact ⟨ω, hω⟩
  have hP'not : ¬ (blowupCentreIdeal S).map (algebraMap Γ(S.X, ⊤)
      (affineBlowupChartCompletion (blowupCentreIdeal S) c.a c.Q.asIdeal)) ≤ P' :=
    fun h => hp' (c.completedLocalIdeal_le_of_map_le p'.asIdeal (hP'def ▸ h))
  refine ⟨blowupRestrict S y', exceptionalToY S e', ?_, c.basePrime P',
    c.not_completedLocalIdeal_le_basePrime P' hP'not, ?_, ?_⟩
  · have h1 := congrArg (fun f => f e') (exceptionalToY_Yι S)
    refine Eq.trans ?_ h1.symm
    show _ = situationBlowUpToBase S (situationExceptionalι S e')
    rw [he']
    exact (blowUpToBase_ι_apply S y').symm
  · have hA1 := depth_add_ringKrullDim_le_blowupChart hdual₀ c.ha
      (completedStalk (idealOnOpen S) F (blowupRestrict S y')) P' hP'not
    have hz := distanceToZ_add_trdeg_le_exceptional S (isUniversallyCatenary_situationY S hdual)
      (d.toNat - 1) (topologicalKrullDim_fiber_exceptionalToY_le_pred S d hfib) e'
    rw [c.trdeg_residueField_eq e' he'] at hz
    have hd := one_le_of_blowup_point S d hfib e'
    have hm' : ringKrullDim (affineBlowupChartCompletion (blowupCentreIdeal S) c.a c.Q.asIdeal ⧸
        P') ≠ ⊥ := by
      have : Nontrivial (affineBlowupChartCompletion (blowupCentreIdeal S) c.a c.Q.asIdeal ⧸ P') :=
        Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsPrime.ne_top inferInstance)
      exact ne_bot_of_le_ne_bot WithBot.zero_ne_bot ringKrullDim_nonneg_of_nontrivial
    exact depth_dim_distance_combine (c.completedStalkDepth_basePrime P' F)
      (c.ringKrullDim_basePrime P') (c.completedStalkDepth_of_comparison F p' hP'def hc)
      (c.ringKrullDim_chartPrime p' hP'def) (by omega) hA1 hz hm'
  · rw [c.ringKrullDim_basePrime P', c.ringKrullDim_chartPrime p' hP'def]
    have hA2 := ringKrullDim_add_trdeg_le_blowupChart hdual₀ c.ha P' hP'not
    refine le_trans (le_add_of_nonneg_right ?_) hA2
    exact (enatToEInt_mono (zero_le : (0 : ℕ∞) ≤ _) : enatToEInt 0 ≤ _)


end Comparison


end Stacks.Algebraization

end
