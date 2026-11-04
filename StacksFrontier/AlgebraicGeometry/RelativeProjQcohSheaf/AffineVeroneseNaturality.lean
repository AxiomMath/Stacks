module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjFunctorSurjective
public import StacksFrontier.AlgebraicGeometry.SectionRingProjTheta.PowerCompareAgreement
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineQuadrupleRoundTrip
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.QuadruplePullback
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.UnionFunctor

/-!
# Naturality in `T` of the Veronese family of a quadruple: the two halves

Let `S` be a scheme, `𝒜` a graded `𝒪_S`-algebra (Situation 01NN), `d > 0`, and let
`P = (d, f : T → S, L, ψ)` be a quadruple of Section 01NS. Section 01NU identifies the functor
`F_d` of strict equivalence classes of quadruples with the functor of *triples* of Section 01N4,
the identification being
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.veroneseSections`, and the bijection
`F_d(T) ≃ Mor(T, U_d)` that identification yields at a fixed `T` is
`...RelativeProjQcohSheaf.Quadruple.fdEquiv`. What stands between that bijection and the
representability of `F_d` is the **naturality in `T`** of the identification, i.e.

`veroneseSections (ψ.pullback g)
  = ProjTriplePullback.pullbackSections _ (veroneseSections ψ) g`

for a morphism `g : T' ⟶ T` of test schemes. That statement splits into two halves, **this
file proves both of them**, and
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/AffineFdRepresentable.lean` joins them and
concludes the representability.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.pullPowCompare_eq_powComparePull`: **the
  comparison `L ^⊗ n ≅ L^{⊗ n}` of [Stacks, Tag 01CU] commutes with pullback.** Reading the
  pullback of a section of `L ^⊗ n` through the comparison of the `ℕ`-indexed iterated powers
  with Tag 01CU's `ℤ`-indexed powers agrees with comparing first and pulling Tag 01CU's power
  back: `(g^*(L ^⊗ n) → (g^*L) ^⊗ n → (g^*L)^{⊗ n}) = (g^*(L ^⊗ n) → g^*(L^{⊗ n}) → (g^*L)^{⊗ n})`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.sectionHom_pullback` and
  `...Twisting.globalSectionHom_pullback`: **the pulled-back map `ψ` of a quadruple acts on
  sections by pulling back the original action.** The degree-`k` transposed map of `g^*ψ` on a
  section of `𝒜_{kd}` is the degree-`k` transposed map of `ψ` on it, carried along `g` by the
  unit of `g^* ⊣ g_*` and then by the comparison `g^*(L^{⊗ k}) ≅ (g^*L)^{⊗ k}` of Tag 01CU.

Auxiliary, and the shape of the proof of the square:

* `...RelativeProjQcohSheaf.powCompare_succIso` and `powCompare_succ`: **the successor law for
  `Stacks.AlgebraicGeometry.CoherentMulSections.powCompare`** — one more copy of `L` whiskered
  in, then Tag 01CU's successor comparison.
* `...RelativeProjQcohSheaf.eq_of_whiskerRight_rec`: two families of morphisms obeying the same
  whiskering recursion and agreeing in degree zero agree in every degree.

## What is here and what is not

The two halves above are the two the naturality statement splits into, and they are proved
unconditionally — no affineness of `S` and no quasi-coherence of `𝒜`. **The naturality statement
itself is not assembled here, and nothing below carries an attribute claiming it**: joining the
two halves needs one further identification that neither half supplies, namely that
`Stacks.RingedSpace.pullbackUnit` — the spelling in which `Twisting.sectionHom` carries a section
along `g`, the unit of the adjunction on sheaves of modules over a *ringed space* — is the
pullback of a global section in the `AlgebraicGeometry.Scheme.Modules` spelling that
`Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullSection` is built from
(`...Descent.SectionsPullbackComparison.pullbackSectionHom`, whose adjunction is
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction`). That identification is
`...RelativeProjQcohSheaf.pullbackSectionHom_top_eq_pullbackUnit`, and the naturality statement
and the `CategoryTheory.Functor.RepresentableBy` for `...RelativeProjQcohSheaf.Fd.functor` it
yields are `...RelativeProjQcohSheaf.veroneseSections_pullback` and
`...RelativeProjQcohSheaf.Fd.representableByDegreeOpen`, all three in
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/AffineFdRepresentable.lean`, which consumes
this file.

## Implementation notes

**Why the square is proved against `Stacks.SectionRingProjTheta.powIso` rather than against
`powCompare` directly.** `powCompare` is `Stacks.SheafOfModules.Invertible.tensorPowerCompare`,
whose successor clause
(`Stacks.SheafOfModules.Invertible.tensorPowerCompare_succ`) is stated with
`Stacks.SheafOfModules.tensorObjIso` and
`Stacks.SheafOfModules.Invertible.tensorPowerSuccIso` — the spellings of the tensor product
sheaf and of Tag 01CU's successor comparison belonging to
`Stacks.SheafOfModules.monoidalCategory`, which is not the monoidal structure a scheme's modules
carry here and whose instances are not available at that spelling. The repository's other
comparison of the same two families of powers, `Stacks.SectionRingProjTheta.powIso`, has a
successor clause `powIso_succ` that holds **by `rfl`** and is stated with
`AlgebraicGeometry.SheafOfModules.tensorIso` — which *is*
`Stacks.AmplePullbackPart1.tensorIsoTensorModules` — and with
`Stacks.SheafOfModules.TensorPower.tensorPowerSuccIso` — which *is*
`...RelativeProjQcohSheaf.LaurentPullback.succIso`, the spelling `laurentPullback_succIso` is
stated in. `Stacks.SectionRingProjTheta.powIso_eq_tensorPowerCompare` identifies the two
comparisons, so taking `powIso` as the route crosses all three spelling walls at once and no
coherence between the two monoidal structures is needed.

**Why the recursion and the rearrangement are separate generic lemmas.** A goal mentioning two
of the three monoidal structures on a scheme's sheaves of modules is not type-correct at the
`implicit` transparency `rw` and `simp` check their motives at, so neither tactic will touch
such a goal — the failure is reported as a missing pattern. `eq_of_whiskerRight_rec`,
`comp_whiskerRight_step` and `rec_step_of_squares` are therefore stated with **free variables in
an arbitrary category**, where every rewrite is checked once against nothing, and the concrete
proof is the application of each to its five commuting squares. Those applications are term
mode throughout, which checks the cross-structure definitional equalities at default
transparency, where they are immediate.

## References

* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
* [Stacks Project, Tag 01N4](https://stacks.math.columbia.edu/tag/01N4)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite MonoidalCategory
open AlgebraicGeometry Stacks.RingedSpace
open Stacks.AlgebraicGeometry.CoherentMulSections (powCompare hStruct)
open Stacks.AlgebraicGeometry.ProjChartPullbackCotensorator (pullbackCotensorator
  pullbackCotensorator_whiskerRight pullbackNatTensorPowIso_inv_succ pullbackTensorModules
  tensorModulesMap)
open Stacks.AlgebraicGeometry.ProjChartRatioPullback (pullbackNatTensorPowIso)
open Stacks.AmplePullbackPart1 (tensorIsoTensorModules)
open Stacks.TensorPowers (natTensorPow)
open Stacks.TensorSheafSpellingIso (pullbackCotensorator_comp_tensorIso
  tensorIsoTensorModules_naturality tensorSheafMap_id_right_eq_whiskerRight)
open RingedSpaceModuleAdjunction (opensMap)

universe u v

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-! ### A recursion principle in a monoidal category -/

section Recursion

variable {D : Type u} [Category.{v} D]

/-- Cancelling an inverse against its isomorphism at the end of a composite of three, with
free variables. The degree-zero case of the square below is this cancellation, and it is across
the `L ^⊗ 0 = 𝟙_` wall, where `Category.assoc` is not available to `rw` or `simp only`: the goal
is not type-correct at the transparency they check their motives at. -/
private theorem comp_inv_comp_hom {A B C E : D} (a : A ⟶ B) (e : C ≅ E) (b : B ⟶ E) :
    (a ≫ b ≫ e.inv) ≫ e.hom = a ≫ b := by
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

variable [MonoidalCategory D]

/-- The one step of monoidal algebra the recursion below needs, stated with free variables so
that it is checked once and never against a goal mentioning two monoidal structures. -/
theorem comp_whiskerRight_step {X₁ X₀ Z Y₀ Y₁ : D} (M : D) (u : X₁ ⟶ X₀ ⊗ M) (v : Y₀ ⊗ M ⟶ Y₁)
    (a : X₀ ⟶ Z) (b : Z ⟶ Y₀) :
    (u ≫ (a ▷ M)) ≫ ((b ▷ M) ≫ v) = u ≫ ((a ≫ b) ▷ M) ≫ v := by
  simp

omit [MonoidalCategory D] in
/-- The rearrangement the right-hand successor law below is, with every morphism a free
variable: three factorizations and three commuting squares composed into one. -/
theorem rec_step_of_squares {X₁ W₁ W₂ W₃ Y₁ C₀ C₁ C₂ C₃ C₄ : D}
    (pc1 : X₁ ⟶ W₃) (mw : X₁ ⟶ W₁) (mt : W₁ ⟶ W₂) (ms : W₂ ⟶ W₃) (lp1 : W₃ ⟶ Y₁)
    (ptc : W₂ ⟶ C₃) (lpbM : C₃ ⟶ C₄) (succM : C₄ ⟶ Y₁)
    (cotA : W₁ ⟶ C₁) (tisoA : C₁ ⟶ C₃) (tisoM : C₂ ⟶ C₄) (lpbw : C₁ ⟶ C₂)
    (cotN : X₁ ⟶ C₀) (mpcw : C₀ ⟶ C₁) (w : C₀ ⟶ C₂)
    (e1 : pc1 = mw ≫ mt ≫ ms) (e3 : ms ≫ lp1 = ptc ≫ lpbM ≫ succM)
    (e4 : cotA ≫ tisoA = mt ≫ ptc) (e5 : tisoA ≫ lpbM = lpbw ≫ tisoM)
    (e6 : mw ≫ cotA = cotN ≫ mpcw) (e7 : mpcw ≫ lpbw = w) :
    pc1 ≫ lp1 = cotN ≫ w ≫ (tisoM ≫ succM) := by
  subst e1 e7
  simp only [Category.assoc, e3, ← reassoc_of% e4, reassoc_of% e5, reassoc_of% e6]

/-- **Two families of morphisms obeying the same whiskering recursion agree.** -/
theorem eq_of_whiskerRight_rec {X Y : ℕ → D} {M : D} (Φ Θ : ∀ n, X n ⟶ Y n)
    (u : ∀ n, X (n + 1) ⟶ X n ⊗ M) (v : ∀ n, Y n ⊗ M ⟶ Y (n + 1)) (h0 : Φ 0 = Θ 0)
    (hΦ : ∀ n, Φ (n + 1) = u n ≫ (Φ n ▷ M) ≫ v n)
    (hΘ : ∀ n, Θ (n + 1) = u n ≫ (Θ n ▷ M) ≫ v n) : ∀ n, Φ n = Θ n
  | 0 => h0
  | n + 1 => (hΦ n).trans
      ((congrArg (fun w => u n ≫ (w ▷ M) ≫ v n)
        (eq_of_whiskerRight_rec Φ Θ u v h0 hΦ hΘ n)).trans (hΘ n).symm)

end Recursion

/-! ### The successor law for `powCompare` -/

section PowCompare

variable {T : Scheme.{u}} (L : T.Modules) [Stacks.Ample.IsInvertibleModule T L]

/-- **The successor law for the comparison `L ^⊗ n ≅ L^{⊗ n}` of [Stacks, Tag 01CU].** -/
theorem powCompare_succIso (n : ℕ) :
    powCompare L (n + 1)
      = whiskerRightIso (powCompare L n) L ≪≫
        tensorIsoTensorModules T ((laurent L).piece (n : ℤ)) L ≪≫
        LaurentPullback.succIso L (n : ℤ) :=
  ((Stacks.SectionRingProjTheta.powIso_eq_tensorPowerCompare
      T.presheaf (hStruct T) L (n + 1)).symm.trans
    (Stacks.SectionRingProjTheta.powIso_succ T.presheaf (hStruct T) L n)).trans
    (congrArg (fun e => whiskerRightIso e L ≪≫
        tensorIsoTensorModules T ((laurent L).piece (n : ℤ)) L ≪≫
        LaurentPullback.succIso L (n : ℤ))
      (Stacks.SectionRingProjTheta.powIso_eq_tensorPowerCompare T.presheaf (hStruct T) L n))

/-- **In degree zero the comparison is the comparison of the two unit objects.** -/
theorem powCompare_zero_eq : powCompare L 0 = Stacks.SectionRingGeometric.unitComparison T := rfl

/-- `powCompare_succIso` on the underlying morphism. -/
theorem powCompare_succ (n : ℕ) :
    (powCompare L (n + 1)).hom
      = ((powCompare L n).hom ▷ L) ≫
        (tensorIsoTensorModules T ((laurent L).piece (n : ℤ)) L).hom ≫
        (LaurentPullback.succIso L (n : ℤ)).hom :=
  congrArg Iso.hom (powCompare_succIso L n)

end PowCompare

/-! ### The square -/

section Square

variable {T' T : Scheme.{u}} (g : T' ⟶ T) (L : T.Modules)
  [Stacks.Ample.IsInvertibleModule T L]

/-- The left-hand family of the square: pull the iterated power back, then compare. -/
def pullPowCompare (n : ℕ) :
    (Scheme.Modules.pullback g).obj (natTensorPow L n) ⟶
      (laurent (LaurentPullback.pullbackModule g L)).piece (n : ℤ) :=
  (pullbackNatTensorPowIso g L n).inv ≫
    (powCompare (LaurentPullback.pullbackModule g L) n).hom

/-- The right-hand family of the square: compare, then pull Tag 01CU's power back. -/
def powComparePull (n : ℕ) :
    (Scheme.Modules.pullback g).obj (natTensorPow L n) ⟶
      (laurent (LaurentPullback.pullbackModule g L)).piece (n : ℤ) :=
  (Scheme.Modules.pullback g).map (powCompare L n).hom ≫ laurentPullback g L (n : ℤ)

/-- **The successor law for the left-hand family of the square.** Pulling the iterated power
back and then comparing in degree `n + 1` is the cotensorator, then the degree-`n` composite
whiskered by one more copy of `g^*L`, then Tag 01CU's successor comparison downstairs. The
first factor is `pullbackNatTensorPowIso_inv_succ` and the second `powCompare_succ`. -/
theorem pullPowCompare_succ (n : ℕ) :
    pullPowCompare g L (n + 1)
      = pullbackCotensorator g (natTensorPow L n) L ≫
        (pullPowCompare g L n ▷ LaurentPullback.pullbackModule g L) ≫
        ((tensorIsoTensorModules T'
            ((laurent (LaurentPullback.pullbackModule g L)).piece (n : ℤ))
            (LaurentPullback.pullbackModule g L)).hom ≫
          (LaurentPullback.succIso (LaurentPullback.pullbackModule g L) (n : ℤ)).hom) := by
  refine Eq.trans ?_ (comp_whiskerRight_step _ _ _ _ _)
  exact (congrArg (fun z => z ≫ (powCompare (LaurentPullback.pullbackModule g L) (n + 1)).hom)
      (pullbackNatTensorPowIso_inv_succ g L n)).trans
    (congrArg (fun z => (pullbackCotensorator g (natTensorPow L n) L ≫
        ((pullbackNatTensorPowIso g L n).inv ▷ LaurentPullback.pullbackModule g L)) ≫ z)
      (powCompare_succ (LaurentPullback.pullbackModule g L) n))

/-- **The successor law for the right-hand family of the square**, with the same right-hand
side. Five commuting squares compose into it, and `rec_step_of_squares` is that composition with
every morphism a free variable: the successor law `powCompare_succ` pushed through `g^*`
(`e1`), the successor law `laurentPullback_succIso` of the comparison of Tag 01CU's powers
(read through `tensorSheafMap_id_right_eq_whiskerRight`, which names the functorial action of
the tensor product sheaf in its first argument as a whiskering), the conjugation
`pullbackCotensorator_comp_tensorIso` of the cotensorator back to the comparison of Tag 01CD,
the naturality `tensorIsoTensorModules_naturality` of the comparison of the two tensor products
(`e5`), and the naturality `pullbackCotensorator_whiskerRight` of the cotensorator in its first
variable. -/
theorem powComparePull_succ (n : ℕ) :
    powComparePull g L (n + 1)
      = pullbackCotensorator g (natTensorPow L n) L ≫
        (powComparePull g L n ▷ LaurentPullback.pullbackModule g L) ≫
        ((tensorIsoTensorModules T'
            ((laurent (LaurentPullback.pullbackModule g L)).piece (n : ℤ))
            (LaurentPullback.pullbackModule g L)).hom ≫
          (LaurentPullback.succIso (LaurentPullback.pullbackModule g L) (n : ℤ)).hom) :=
  have e1 : (Scheme.Modules.pullback g).map (powCompare L (n + 1)).hom
      = (Scheme.Modules.pullback g).map ((powCompare L n).hom ▷ L) ≫
        (Scheme.Modules.pullback g).map
            (tensorIsoTensorModules T ((laurent L).piece (n : ℤ)) L).hom ≫
          (Scheme.Modules.pullback g).map (LaurentPullback.succIso L (n : ℤ)).hom :=
    (congrArg (fun z => (Scheme.Modules.pullback g).map z) (powCompare_succ L n)).trans
      (((Scheme.Modules.pullback g).map_comp _ _).trans
        (congrArg (fun z => (Scheme.Modules.pullback g).map ((powCompare L n).hom ▷ L) ≫ z)
          ((Scheme.Modules.pullback g).map_comp _ _)))
  have e5 : (tensorIsoTensorModules T' ((Scheme.Modules.pullback g).obj
          ((laurent L).piece (n : ℤ))) (LaurentPullback.pullbackModule g L)).hom ≫
        tensorModulesMap T' (laurentPullback g L (n : ℤ))
          (𝟙 (LaurentPullback.pullbackModule g L))
      = (@MonoidalCategoryStruct.whiskerRight T'.Modules _ _ _ _
            (laurentPullback g L (n : ℤ)) (LaurentPullback.pullbackModule g L)) ≫
        (tensorIsoTensorModules T' ((laurent (LaurentPullback.pullbackModule g L)).piece (n : ℤ))
          (LaurentPullback.pullbackModule g L)).hom :=
    (tensorIsoTensorModules_naturality T' (laurentPullback g L (n : ℤ))
        (𝟙 (LaurentPullback.pullbackModule g L))).symm.trans
      (congrArg (fun z => z ≫ (tensorIsoTensorModules T'
          ((laurent (LaurentPullback.pullbackModule g L)).piece (n : ℤ))
          (LaurentPullback.pullbackModule g L)).hom)
        (@MonoidalCategory.tensorHom_id T'.Modules _ _ _ _ (laurentPullback g L (n : ℤ))
          (LaurentPullback.pullbackModule g L)))
  rec_step_of_squares _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e1
    ((laurentPullback_succIso g L (n : ℤ)).trans
      (congrArg (fun z => Stacks.PullbackTensorCoherence.pullbackTensorComparison
            (ringedSpaceHom g) ((laurent L).piece (n : ℤ)) L ≫ z ≫
          (LaurentPullback.succIso (LaurentPullback.pullbackModule g L) (n : ℤ)).hom)
        (tensorSheafMap_id_right_eq_whiskerRight T'.toRingedSpace (laurentPullback g L (n : ℤ))
          (LaurentPullback.pullbackModule g L)).symm))
    (pullbackCotensorator_comp_tensorIso T g ((laurent L).piece (n : ℤ)) L) e5
    (pullbackCotensorator_whiskerRight g (powCompare L n).hom L)
    (MonoidalCategory.comp_whiskerRight _ _ _).symm

/-- **The square in degree zero.** Both sides are the comparison of the two unit objects
carried along `g`: the zeroth iterated power is the tensor unit and the zeroth power of
[Stacks, Tag 01CU] is the structure sheaf, so `powCompare` in degree zero is
`Stacks.SectionRingGeometric.unitComparison` (`powCompare_zero_eq`), the comparison of the
powers in degree zero is `Stacks.PullbackUnitSection.unitPullbackHom`
(`pullbackNatTensorPowIso_inv_zero`) and the comparison of Tag 01CU's powers in degree zero is
the structure-sheaf comparison of Tag 01CD (`laurentPullback_zero`). What is left is that
`unitPullbackHom` is that comparison conjugated by `unitComparison`, which is
`unitPullbackHom_eq_pullbackUnitComparison`. -/
theorem pullPowCompare_zero :
    pullPowCompare g L 0 = powComparePull g L 0 :=
  have h : Stacks.PullbackUnitSection.unitPullbackHom g ≫
        (Stacks.SectionRingGeometric.unitComparison T').hom
      = (Scheme.Modules.pullback g).map (Stacks.SectionRingGeometric.unitComparison T).hom ≫
        laurentPullback g L (0 : ℤ) :=
    (congrArg (fun z => z ≫ (Stacks.SectionRingGeometric.unitComparison T').hom)
        (Stacks.TensorSheafSpellingIso.unitPullbackHom_eq_pullbackUnitComparison T g)).trans
      ((comp_inv_comp_hom _ (Stacks.SectionRingGeometric.unitComparison T') _).trans
        (congrArg (fun z => (Scheme.Modules.pullback g).map
            (Stacks.SectionRingGeometric.unitComparison T).hom ≫ z)
          (laurentPullback_zero g L).symm))
  (congrArg (fun z => z ≫ (powCompare (LaurentPullback.pullbackModule g L) 0).hom)
    (Stacks.AlgebraicGeometry.ProjChartSectionPullback.pullbackNatTensorPowIso_inv_zero
      (j := g) (L := L))).trans h

/-- **The comparison `L ^⊗ n ≅ L^{⊗ n}` of [Stacks, Tag 01CU] commutes with pullback**, in
every non-negative degree and with no hypothesis beyond the invertibility of `L`.

This is the square the naturality in `T` of the Veronese family of a quadruple rests on: it says
that reading the pullback of a global section of `L ^⊗ n` in Tag 01CU's powers may be done in
either order. The induction is `eq_of_whiskerRight_rec` on the two successor laws
`pullPowCompare_succ` and `powComparePull_succ`, which have the same right-hand side, with
`pullPowCompare_zero` as its base. -/
theorem pullPowCompare_eq_powComparePull (n : ℕ) :
    pullPowCompare g L n = powComparePull g L n :=
  eq_of_whiskerRight_rec (pullPowCompare g L) (powComparePull g L)
    (fun n => pullbackCotensorator g (natTensorPow L n) L)
    (fun n => (tensorIsoTensorModules T'
        ((laurent (LaurentPullback.pullbackModule g L)).piece (n : ℤ))
        (LaurentPullback.pullbackModule g L)).hom ≫
      (LaurentPullback.succIso (LaurentPullback.pullbackModule g L) (n : ℤ)).hom)
    (pullPowCompare_zero g L) (pullPowCompare_succ g L) (powComparePull_succ g L) n

end Square

/-! ### The pulled-back twisting on sections -/

namespace Twisting

variable {T' T S : Scheme.{u}} {f : T ⟶ S}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}
  {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]

/-- **The pulled-back map `ψ` of a quadruple acts on sections by pulling back the original
action.** For a morphism `g : T' ⟶ T` of test schemes, an open `U ⊆ S` and a section `a` of
`𝒜_{kd}` over `U`, the degree-`k` transposed map of `g^*ψ` on `a` is the degree-`k` transposed
map of `ψ` on `a`, carried along `g` by the unit of `g^* ⊣ g_*` and then by the comparison
`g^*(L^{⊗ k}) ⟶ (g^*L)^{⊗ k}` of Tag 01CU.

Unconditional: no affineness of `S` and no quasi-coherence of `𝒜` is used.

Two inputs, both of them coherences of the unit of the adjunction on sheaves of modules.
`Twisting.pullbackApp` is the contraction `compComparison` of the iterated pullback followed by
`g^*` of the component of `ψ` followed by `laurentPullback`; the contraction carries the unit
image along `g ≫ f` to the iterated unit image
(`Stacks.PullbackCompMonoidal.comparison_pullbackUnit`) and the unit is natural in the module
(`Stacks.RingedSpace.pullbackUnit_naturality`), which moves the component of `ψ` past it. -/
theorem sectionHom_pullback (ψ : Twisting f A d L) (g : T' ⟶ T) (k : ℤ)
    (U : (Opens S.toRingedSpace.carrier)ᵒᵖ) (a : (A.piece (k * d)).val.obj U) :
    (ψ.pullback g).sectionHom k U a
      = (laurentPullback g L k).val.app
            ((opensMap (ringedSpaceHom g)).op.obj ((opensMap (ringedSpaceHom f)).op.obj U))
          (pullbackUnit (ringedSpaceHom g)
            ((laurent L).piece k) ((opensMap (ringedSpaceHom f)).op.obj U)
            (ψ.sectionHom k U a)) :=
  congrArg (fun z => (laurentPullback g L k).val.app
      ((opensMap (ringedSpaceHom (g ≫ f))).op.obj U) z)
    ((congrArg (fun z => ((pullbackFunctor (ringedSpaceHom g)).map (ψ.app k)).val.app
          ((opensMap (ringedSpaceHom (g ≫ f))).op.obj U) z)
        (Stacks.PullbackCompMonoidal.comparison_pullbackUnit
          (ringedSpaceHom f) (ringedSpaceHom g) (A.piece (k * d)) U a)).trans
      (pullbackUnit_naturality (f := ringedSpaceHom g) (ψ.app k)
        ((opensMap (ringedSpaceHom f)).op.obj U)
        (pullbackUnit (ringedSpaceHom f) (A.piece (k * d)) U a)))

/-- **`Twisting.sectionHom_pullback` over `U = S`**, i.e. on the global sections the degreewise
maps `A_{kd} → Γ(T, L^{⊗ k})` of Section 01N4 are built from. The transport along `f⁻¹⊤ = ⊤` that
`Twisting.globalSectionHom` carries is the identity on both sides, which is
`Twisting.globalSectionHom_eq_sectionHom`. -/
-- Beyond what this declaration proves, recorded here rather than in the attribute:
--   the degree-k transposed map of g^*psi is the degree-k transposed map of psi carried along g by
--   the unit of g^* -| g_* and then by the comparison g^*(L^{otimes k}) -> (g^*L)^{otimes k} of
--   Tag 01CU. Unconditional. This is NOT the naturality in T of veroneseSections: joining it to
--   the other half (pullPowCompare_eq_powComparePull) also needs Stacks.RingedSpace.pullbackUnit,
--   the spelling used here, identified with the Scheme.Modules-level pullback of a global section
--   that ProjChartRatioPullback.pullSection is built from, which is
--   pullbackSectionHom_top_eq_pullbackUnit of AffineFdRepresentable. The naturality
--   veroneseSections (psi.pullback g) =
--   ProjTriplePullback.pullbackSections _ (veroneseSections psi) g is veroneseSections_pullback
--   there, and the RepresentableBy for Fd.functor it yields is Fd.representableByDegreeOpen there
theorem globalSectionHom_pullback (ψ : Twisting f A d L) (g : T' ⟶ T) (k : ℤ)
    (a : (A.piece (k * d)).val.obj (op (⊤ : Opens S.toRingedSpace.carrier))) :
    (ψ.pullback g).globalSectionHom k a
      = (laurentPullback g L k).val.app (op (⊤ : Opens T'.toRingedSpace.carrier))
          (pullbackUnit (ringedSpaceHom g) ((laurent L).piece k)
            (op (⊤ : Opens T.toRingedSpace.carrier)) (ψ.globalSectionHom k a)) :=
  (globalSectionHom_eq_sectionHom (ψ.pullback g) k a).trans
    ((sectionHom_pullback ψ g k (op (⊤ : Opens S.toRingedSpace.carrier)) a).trans
      (congrArg (fun z => (laurentPullback g L k).val.app
          (op (⊤ : Opens T'.toRingedSpace.carrier))
          (pullbackUnit (ringedSpaceHom g) ((laurent L).piece k)
            (op (⊤ : Opens T.toRingedSpace.carrier)) z))
        (globalSectionHom_eq_sectionHom ψ k a).symm))

end Twisting

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
