module

public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceSectionsOverOpen
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceSystemIso
public import StacksFrontier.AlgebraicGeometry.Cohomology.FlatPushforwardSectionsHomotopyColimit
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaRight
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorLeftUnitor
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistencePerfectTensor
public import
  StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceSectionsBaseChange
public import StacksFrontier.AlgebraicGeometry.AffineDerivedBaseChangeGeneral

/-!
# The projection-formula square of Stacks 0CTG

In Situation [Stacks, Tag 0CTC], let `U ⊆ X` be a quasi-compact open, `ι : U ⟶ X` its inclusion,
`iₙ : Xₙ ⟶ X` the level closed immersion and `Uₙ = U ∩ Xₙ`. The proof of [Stacks, Tag 0CTG]
computes `RΓ(Uₙ, ℱₙ)` in two ways out of `RΓ_A(X, iₙ,* ℱₙ ⊗^𝐋 Rι_* 𝒪_U)`:

* through the projection formula along `ι` ([Stacks, Tag 08EU]) and restriction to `U`, which
  gives `RΓ_A(U, (iₙ,* ℱₙ)|_U) = RΓ_{Aₙ}(Uₙ, ℱₙ)`;
* through the level identification of [Stacks, Tag 0CTE] (1),
  `RΓ_A(X, iₙ,* ℱₙ ⊗^𝐋 E) = RΓ_{Aₙ}(Xₙ, ℱₙ ⊗^𝐋 Liₙ^* E)`, followed by flat base change
  `Liₙ^* Rι_* 𝒪_U = R(Uₙ ⟶ Xₙ)_* 𝒪_{Uₙ}` ([Stacks, Tag 08IB]), the projection formula along
  `Uₙ ⟶ Xₙ` and Leray.

This file proves that the two agree: `ExistenceSituation.projectionFormulaSquare`, the input
`ExistenceSituation.ProjectionFormulaSquare` of the 0CTG argument.

## Main results

* `AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.levelSectionsIso`: the isomorphism
  `RΓ_{Aₙ}(Xₙ, ℱₙ ⊗^𝐋 Liₙ^* Rι_* 𝒪_U) ≅ RΓ_{Aₙ}(Uₙ, ℱₙ)` of `D(Aₙ)`.
* `AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.levelSectionsSquare_eq`: the square.
* `AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.projectionFormulaSquare`.
* `AlgebraicGeometry.GrothendieckExistence.LevelSectionsSquare.sheaf_square`: the underlying
  chase in `D(𝒪_X)`, at variables: the projection formula along `iₙ` (Stacks 0B6B) against base
  change, transposed along `ι^* ⊣ Rι_*`, with the unit and commutativity constraints.
* `AlgebraicGeometry.GrothendieckExistence.LevelSectionsSquare.leray_square`: the compatibility of
  the Leray identifications around the square `Uₙ ⟶ U`, `Xₙ ⟶ X`, at variables.

## Implementation notes

The chases are carried out at variables (`sheaf_square`, `sheaf_square_mate`, `leray_square`,
`assembly'`) and instantiated once. At the concrete data the derived pushforward and pullback of
ringed spaces are spelled on `SheafOfModules (structureSheafRing _)`, the derived global sections
on `X.Modules`, and the derived tensor product on the ringed-site derived modules; a statement
mixing them is only affordable when every concrete hypothesis is produced in exactly the spelling
its variable form expects. So the base change maps are used as components of the `Mate`
construction, the transposition identity of the base change map is applied at variables, the
inverse of `derivedPullbackCompIsoLeft` is read through `derivedBaseChangeMap_adjoint_split`, and
the compatibility of the Leray identifications is a predicate (`LeraySquare`) elaborated from its
arguments alone.

All declarations that mention the derived pushforward, pullback or tensor product of ringed
spaces are at `HasDerivedCategory.standard`, scoped to the declaration, the model at which those
functors exist.

## References

* [Stacks Project, Tag 0CTG](https://stacks.math.columbia.edu/tag/0CTG)
* [Stacks Project, Tag 0B6B](https://stacks.math.columbia.edu/tag/0B6B)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Prod

namespace AlgebraicGeometry.GrothendieckExistence.LevelSectionsSquare

section Generic

variable {DX DXn DU DUn : Type*} [Category DX] [Category DXn] [Category DU] [Category DUn]
  {La : DX ⥤ DXn} {Ra : DXn ⥤ DX} (adja : La ⊣ Ra)
  {Lb : DX ⥤ DU} {Rb : DU ⥤ DX} (adjb : Lb ⊣ Rb)
  {La' : DU ⥤ DUn} {Ra' : DUn ⥤ DU} (adja' : La' ⊣ Ra')
  {Lb' : DXn ⥤ DUn} {Rb' : DUn ⥤ DXn} (adjb' : Lb' ⊣ Rb')
  (TX : DX ⥤ DX ⥤ DX) (TXn : DXn ⥤ DXn ⥤ DXn) (TU : DU ⥤ DU ⥤ DU) (TUn : DUn ⥤ DUn ⥤ DUn)
  (αa : Functor.uncurry.obj TX ⋙ La ⟶ La.prod La ⋙ Functor.uncurry.obj TXn)
  (αb : Functor.uncurry.obj TX ⋙ Lb ⟶ Lb.prod Lb ⋙ Functor.uncurry.obj TU)
  (αa' : Functor.uncurry.obj TU ⋙ La' ⟶ La'.prod La' ⋙ Functor.uncurry.obj TUn)
  (αb' : Functor.uncurry.obj TXn ⋙ Lb' ⟶ Lb'.prod Lb' ⋙ Functor.uncurry.obj TUn)

/-- The adjoint transpose of a map into `R G'` composed with `R` of a map: the counit form. -/
private lemma counit_comp {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) {A : C} {B B' : D} (x : A ⟶ R.obj B) (y : B ⟶ B') :
    L.map (x ≫ R.map y) ≫ adj.counit.app B' = (L.map x ≫ adj.counit.app B) ≫ y := by
  rw [Functor.map_comp, Category.assoc, Category.assoc]
  exact congrArg (L.map x ≫ ·) (adj.counit.naturality y)

/-- The right-handed projection-formula map, read at the curried bifunctors. -/
private lemma map_adjunctionTensorMap_swap_comp_counit {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D)
    (α : Functor.uncurry.obj TC ⋙ L ⟶ L.prod L ⋙ Functor.uncurry.obj TD) (W : D) (G : C) :
    L.map (adjunctionTensorMap adj (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj TC)
        (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj TD)
        (Stacks.Cohomology.DerivedProjectionFormula.comparisonSwap _ _ α) W G) ≫
      adj.counit.app ((CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj TD).obj (W, L.obj G)) =
    α.app (G, R.obj W) ≫ (TD.obj (L.obj G)).map (adj.counit.app W) := by
  have h := map_adjunctionTensorMap_comp_counit adj
    (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj TC)
    (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj TD)
    (Stacks.Cohomology.DerivedProjectionFormula.comparisonSwap _ _ α) W G
  refine h.trans ?_
  simp only [Stacks.Cohomology.DerivedProjectionFormula.comparisonSwap_app, Functor.comp_map,
    CategoryTheory.Prod.swap_map]
  rw [Stacks.Cohomology.DerivedProjectionFormula.uncurry_map_id_left]

/-- The left-handed projection-formula map, read at the curried bifunctors. -/
private lemma map_adjunctionTensorMap_comp_counit' {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D)
    (α : Functor.uncurry.obj TC ⋙ L ⟶ L.prod L ⋙ Functor.uncurry.obj TD) (W : D) (G : C) :
    L.map (adjunctionTensorMap adj (Functor.uncurry.obj TC) (Functor.uncurry.obj TD) α W G) ≫
      adj.counit.app ((Functor.uncurry.obj TD).obj (W, L.obj G)) =
    α.app (R.obj W, G) ≫ (TD.map (adj.counit.app W)).app (L.obj G) :=
  (map_adjunctionTensorMap_comp_counit adj (Functor.uncurry.obj TC) (Functor.uncurry.obj TD) α
    W G).trans (by rw [Stacks.Cohomology.DerivedProjectionFormula.uncurry_map_id_right])

/-- Naturality of the left-handed projection-formula map in the second variable, curried. -/
private lemma adjunctionTensorMap_natural_right' {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D)
    (α : Functor.uncurry.obj TC ⋙ L ⟶ L.prod L ⋙ Functor.uncurry.obj TD) (W : D)
    {H H' : C} (k : H ⟶ H') :
    (TC.obj (R.obj W)).map k ≫
        adjunctionTensorMap adj (Functor.uncurry.obj TC) (Functor.uncurry.obj TD) α W H' =
      adjunctionTensorMap adj (Functor.uncurry.obj TC) (Functor.uncurry.obj TD) α W H ≫
        R.map ((TD.obj W).map (L.map k)) := by
  have h := adjunctionTensorMap_natural adj (Functor.uncurry.obj TC) (Functor.uncurry.obj TD) α
    (𝟙 W) k
  rw [CategoryTheory.Functor.map_id, Stacks.Cohomology.DerivedProjectionFormula.uncurry_map_id_left,
    Stacks.Cohomology.DerivedProjectionFormula.uncurry_map_id_left] at h
  exact h

/-- Two maps into `R B` agree once their adjoint transposes do. -/
private lemma eq_of_counit {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) {A : C} {B : D} {x y : A ⟶ R.obj B}
    (h : L.map x ≫ adj.counit.app B = L.map y ≫ adj.counit.app B) : x = y := by
  apply (adj.homEquiv _ _).symm.injective
  simpa only [Adjunction.homEquiv_counit] using h

/-- The transpose of `η ≫ R w` is `w`. -/
private lemma unit_comp_counit {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) {A : C} {B : D} (w : L.obj A ⟶ B) :
    L.map (adj.unit.app A ≫ R.map w) ≫ adj.counit.app B = w := by
  rw [Functor.map_comp, Category.assoc]
  rw [show L.map (R.map w) ≫ adj.counit.app B = adj.counit.app (L.obj A) ≫ w from
    adj.counit.naturality w]
  simp

/-- A map into `R B` is the unit followed by `R` of its transpose. -/
private lemma eq_unit_comp {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) {A : C} {B : D} (x : A ⟶ R.obj B) :
    x = adj.unit.app A ≫ R.map (L.map x ≫ adj.counit.app B) := by
  have h := adj.homEquiv_unit A B ((adj.homEquiv A B).symm x)
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_counit] at h
  exact h

variable {M : DX} {G : DXn} {O : DU} {On : DUn} {Z : DUn}

/-- The transpose along `Lb ⊣ Rb` of `Ra y` followed by the comparison `Ra Rb' ⟶ Rb Ra'` is the
base change map followed by `Ra'` of the transpose of `y` along `Lb' ⊣ Rb'`. -/
private lemma transpose_cmp (cmp : Rb' ⋙ Ra ⟶ Ra' ⋙ Rb)
    (bc : ∀ K : DXn, Lb.obj (Ra.obj K) ⟶ Ra'.obj (Lb'.obj K))
    (hfac : ∀ K : DXn, Ra.map (adjb'.unit.app K) ≫ cmp.app (Lb'.obj K) =
      adjb.unit.app (Ra.obj K) ≫ Rb.map (bc K)) {K : DXn} (y : K ⟶ Rb'.obj Z) :
    Lb.map (Ra.map y ≫ cmp.app Z) ≫ adjb.counit.app (Ra'.obj Z) =
      bc K ≫ Ra'.map (Lb'.map y ≫ adjb'.counit.app Z) := by
  have e1 : Ra.map y ≫ cmp.app Z = adjb.unit.app (Ra.obj K) ≫
      Rb.map (bc K ≫ Ra'.map (Lb'.map y ≫ adjb'.counit.app Z)) := by
    conv_lhs => rw [eq_unit_comp adjb' y]
    rw [Functor.map_comp, Category.assoc]
    have hn : Ra.map (Rb'.map (Lb'.map y ≫ adjb'.counit.app Z)) ≫ cmp.app Z =
        cmp.app (Lb'.obj K) ≫ Rb.map (Ra'.map (Lb'.map y ≫ adjb'.counit.app Z)) :=
      cmp.naturality (Lb'.map y ≫ adjb'.counit.app Z)
    rw [hn, ← Category.assoc, hfac, Category.assoc, ← Functor.map_comp]
  exact (congrArg (fun t => Lb.map t ≫ adjb.counit.app (Ra'.obj Z)) e1).trans
    (unit_comp_counit adjb _)

/-- **The sheaf-level chase of the level sections square**, at variables. The four
projection-formula maps enter only through their adjoint transposes, the base change square of
Stacks 0B6B, a naturality and the unit coherence. -/
theorem sheaf_square (s : M ⟶ Ra.obj G)
    (bcO : La.obj (Rb.obj O) ⟶ Rb'.obj (La'.obj O)) (uO : La'.obj O ⟶ On)
    (ruN : (TUn.obj (Lb'.obj G)).obj On ⟶ Lb'.obj G) (bridge' : Lb'.obj G ⟶ Z)
    (cmp : Rb' ⋙ Ra ⟶ Ra' ⋙ Rb) (bc : ∀ K : DXn, Lb.obj (Ra.obj K) ⟶ Ra'.obj (Lb'.obj K))
    (hfac : ∀ K : DXn, Ra.map (adjb'.unit.app K) ≫ cmp.app (Lb'.obj K) =
      adjb.unit.app (Ra.obj K) ≫ Rb.map (bc K))
    (PFa : (TX.obj (Ra.obj G)).obj (Rb.obj O) ⟶ Ra.obj ((TXn.obj G).obj (La.obj (Rb.obj O))))
    (PFa' : ∀ H : DU, (TU.obj (Ra'.obj (Lb'.obj G))).obj H ⟶
      Ra'.obj ((TUn.obj (Lb'.obj G)).obj (La'.obj H)))
    (PFb : (TX.obj (Rb.obj O)).obj M ⟶ Rb.obj ((TU.obj O).obj (Lb.obj M)))
    (PFR : (TXn.obj G).obj (Rb'.obj (La'.obj O)) ⟶
      Rb'.obj ((TUn.obj (Lb'.obj G)).obj (La'.obj O)))
    (cE : Lb'.obj (La.obj (Rb.obj O)) ⟶ La'.obj (Lb.obj (Rb.obj O)))
    (h0B6B : Stacks.Cohomology.DerivedProjectionFormula.ProjectionFormulaBaseChangeSquare
      Ra Ra' La La' Lb Lb' (Functor.uncurry.obj TX) (Functor.uncurry.obj TXn)
      (Functor.uncurry.obj TU) (Functor.uncurry.obj TUn) αb αb' G (Rb.obj O) PFa
      (bc ((TXn.obj G).obj (La.obj (Rb.obj O)))) (bc G) cE (PFa' (Lb.obj (Rb.obj O))))
    (hPFb : Lb.map PFb ≫ adjb.counit.app ((TU.obj O).obj (Lb.obj M)) =
      αb.app (Rb.obj O, M) ≫ (TU.map (adjb.counit.app O)).app (Lb.obj M))
    (hPFR : Lb'.map PFR ≫ adjb'.counit.app ((TUn.obj (Lb'.obj G)).obj (La'.obj O)) =
      αb'.app (G, Rb'.obj (La'.obj O)) ≫ (TUn.obj (Lb'.obj G)).map (adjb'.counit.app (La'.obj O)))
    (hnat : (TU.obj (Ra'.obj (Lb'.obj G))).map (adjb.counit.app O) ≫ PFa' O =
      PFa' (Lb.obj (Rb.obj O)) ≫ Ra'.map ((TUn.obj (Lb'.obj G)).map (La'.map (adjb.counit.app O))))
    (hbcO : Lb'.map bcO ≫ adjb'.counit.app (La'.obj O) = cE ≫ La'.map (adjb.counit.app O))
    (flipX : (TX.obj M).obj (Rb.obj O) ⟶ (TX.obj (Rb.obj O)).obj M)
    (flipU : (TU.obj (Lb.obj M)).obj (Lb.obj (Rb.obj O)) ⟶
      (TU.obj (Lb.obj (Rb.obj O))).obj (Lb.obj M))
    (flipU' : (TU.obj (Lb.obj M)).obj O ⟶ (TU.obj O).obj (Lb.obj M))
    (luU : (TU.obj O).obj (Lb.obj M) ⟶ Lb.obj M) (ruU : ∀ Y : DU, (TU.obj Y).obj O ⟶ Y)
    (hbraid : Lb.map flipX ≫ αb.app (Rb.obj O, M) = αb.app (M, Rb.obj O) ≫ flipU)
    (hflip : flipU ≫ (TU.map (adjb.counit.app O)).app (Lb.obj M) =
      (TU.obj (Lb.obj M)).map (adjb.counit.app O) ≫ flipU')
    (hlu : flipU' ≫ luU = ruU (Lb.obj M))
    (hru : ∀ {Y Y' : DU} (y : Y ⟶ Y'), (TU.map y).app O ≫ ruU Y' = ruU Y ≫ y)
    (hunit : PFa' O ≫ Ra'.map ((TUn.obj (Lb'.obj G)).map uO ≫ ruN) =
      ruU (Ra'.obj (Lb'.obj G)))
    (ψ : Lb.obj M ⟶ Ra'.obj Z) (hPA : Lb.map s ≫ bc G ≫ Ra'.map bridge' = ψ) :
    (TX.map s).app (Rb.obj O) ≫ PFa ≫
        Ra.map (((TXn.obj G).map bcO ≫ PFR) ≫
          Rb'.map ((TUn.obj (Lb'.obj G)).map uO ≫ ruN ≫ bridge')) ≫ cmp.app Z =
      flipX ≫ PFb ≫ Rb.map (luU ≫ ψ) := by
  have hR : Lb.map (flipX ≫ PFb ≫ Rb.map (luU ≫ ψ)) ≫ adjb.counit.app (Ra'.obj Z) =
      αb.app (M, Rb.obj O) ≫ (TU.obj (Lb.obj M)).map (adjb.counit.app O) ≫ ruU (Lb.obj M) ≫
        ψ := by
    rw [Functor.map_comp, Category.assoc, counit_comp adjb, hPFb]
    simp only [Category.assoc]
    rw [reassoc_of% hbraid, reassoc_of% hflip, reassoc_of% hlu]
  have hν : Lb'.map ((TXn.obj G).map bcO ≫ PFR) ≫
        adjb'.counit.app ((TUn.obj (Lb'.obj G)).obj (La'.obj O)) =
      αb'.app (G, La.obj (Rb.obj O)) ≫
        (TUn.obj (Lb'.obj G)).map (cE ≫ La'.map (adjb.counit.app O)) := by
    have hn : Lb'.map ((TXn.obj G).map bcO) ≫ αb'.app (G, Rb'.obj (La'.obj O)) =
        αb'.app (G, La.obj (Rb.obj O)) ≫ (TUn.obj (Lb'.obj G)).map (Lb'.map bcO) := by
      have := αb'.naturality (𝟙 G ×ₘ bcO)
      simp only [Functor.comp_map, Functor.prod_map, CategoryTheory.Functor.map_id,
        Stacks.Cohomology.DerivedProjectionFormula.uncurry_map_id_left] at this
      exact this
    rw [Functor.map_comp, Category.assoc, hPFR, reassoc_of% hn, ← Functor.map_comp, hbcO]
  have hνκ : Lb'.map (((TXn.obj G).map bcO ≫ PFR) ≫
        Rb'.map ((TUn.obj (Lb'.obj G)).map uO ≫ ruN ≫ bridge')) ≫ adjb'.counit.app Z =
      (αb'.app (G, La.obj (Rb.obj O)) ≫ (TUn.obj (Lb'.obj G)).map cE) ≫
        ((TUn.obj (Lb'.obj G)).map (La'.map (adjb.counit.app O)) ≫
          ((TUn.obj (Lb'.obj G)).map uO ≫ ruN ≫ bridge')) := by
    rw [counit_comp adjb', hν, Functor.map_comp]
    simp only [Category.assoc]
  have h0 : Lb.map PFa ≫ bc ((TXn.obj G).obj (La.obj (Rb.obj O))) ≫
        Ra'.map (αb'.app (G, La.obj (Rb.obj O)) ≫ (TUn.obj (Lb'.obj G)).map cE) =
      αb.app (Ra.obj G, Rb.obj O) ≫ (TU.map (bc G)).app (Lb.obj (Rb.obj O)) ≫
        PFa' (Lb.obj (Rb.obj O)) := by
    have h := h0B6B
    unfold Stacks.Cohomology.DerivedProjectionFormula.ProjectionFormulaBaseChangeSquare at h
    rw [Stacks.Cohomology.DerivedProjectionFormula.uncurry_map_id_right,
      Stacks.Cohomology.DerivedProjectionFormula.uncurry_map_id_left] at h
    exact h.symm
  have hW : PFa' (Lb.obj (Rb.obj O)) ≫
        Ra'.map ((TUn.obj (Lb'.obj G)).map (La'.map (adjb.counit.app O)) ≫
          ((TUn.obj (Lb'.obj G)).map uO ≫ ruN ≫ bridge')) =
      (TU.obj (Ra'.obj (Lb'.obj G))).map (adjb.counit.app O) ≫ ruU (Ra'.obj (Lb'.obj G)) ≫
        Ra'.map bridge' := by
    rw [Functor.map_comp, ← Category.assoc, ← hnat, Category.assoc]
    congr 1
    rw [show ((TUn.obj (Lb'.obj G)).map uO ≫ ruN ≫ bridge') =
        ((TUn.obj (Lb'.obj G)).map uO ≫ ruN) ≫ bridge' from (Category.assoc _ _ _).symm,
      Functor.map_comp, ← Category.assoc, hunit]
  have hs : Lb.map ((TX.map s).app (Rb.obj O)) ≫ αb.app (Ra.obj G, Rb.obj O) =
      αb.app (M, Rb.obj O) ≫ (TU.map (Lb.map s)).app (Lb.obj (Rb.obj O)) := by
    have := αb.naturality (s ×ₘ 𝟙 (Rb.obj O))
    simp only [Functor.comp_map, Functor.prod_map, CategoryTheory.Functor.map_id,
      Stacks.Cohomology.DerivedProjectionFormula.uncurry_map_id_right] at this
    exact this
  refine eq_of_counit adjb ?_
  rw [hR]
  have hL : Lb.map ((TX.map s).app (Rb.obj O) ≫ PFa ≫
        Ra.map (((TXn.obj G).map bcO ≫ PFR) ≫
          Rb'.map ((TUn.obj (Lb'.obj G)).map uO ≫ ruN ≫ bridge')) ≫ cmp.app Z) ≫
        adjb.counit.app (Ra'.obj Z) =
      Lb.map ((TX.map s).app (Rb.obj O)) ≫ Lb.map PFa ≫
        (Lb.map (Ra.map (((TXn.obj G).map bcO ≫ PFR) ≫
          Rb'.map ((TUn.obj (Lb'.obj G)).map uO ≫ ruN ≫ bridge')) ≫ cmp.app Z) ≫
          adjb.counit.app (Ra'.obj Z)) := by
    simp only [Functor.map_comp, Category.assoc]
  refine hL.trans ?_
  rw [transpose_cmp adjb adjb' cmp bc hfac, hνκ, Functor.map_comp, reassoc_of% h0, hW,
    reassoc_of% hs]
  congr 1
  have hx : (TU.map (Lb.map s)).app (Lb.obj (Rb.obj O)) ≫
      (TU.map (bc G)).app (Lb.obj (Rb.obj O)) ≫
        (TU.obj (Ra'.obj (Lb'.obj G))).map (adjb.counit.app O) =
      (TU.obj (Lb.obj M)).map (adjb.counit.app O) ≫ (TU.map (Lb.map s ≫ bc G)).app O := by
    rw [← NatTrans.comp_app_assoc, ← Functor.map_comp]
    exact ((TU.map (Lb.map s ≫ bc G)).naturality (adjb.counit.app O)).symm
  rw [reassoc_of% hx, reassoc_of% (hru (Lb.map s ≫ bc G)), ← hPA]

/-- **The projection formula at the unit**, at variables: if the comparison `α` is compatible
with the right unit constraints through `u : L O ⟶ OD`, then the projection-formula map at
`(W, O)` followed by `R` of the unit constraint is the unit constraint. -/
theorem adjunctionTensorMap_unit_comp {C D : Type*} [Category C] [Category D] {L : C ⥤ D}
    {R : D ⥤ C} (adj : L ⊣ R) (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D)
    (α : Functor.uncurry.obj TC ⋙ L ⟶ L.prod L ⋙ Functor.uncurry.obj TD) {O : C} {OD : D}
    (u : L.obj O ⟶ OD) (ρC : ∀ Y : C, (TC.obj Y).obj O ⟶ Y) (ρD : ∀ Y : D, (TD.obj Y).obj OD ⟶ Y)
    (hρD : ∀ {Y Y' : D} (y : Y ⟶ Y'), (TD.map y).app OD ≫ ρD Y' = ρD Y ≫ y)
    (hcoh : ∀ Y : C, L.map (ρC Y) = α.app (Y, O) ≫ (TD.obj (L.obj Y)).map u ≫ ρD (L.obj Y))
    (W : D) :
    adjunctionTensorMap adj (Functor.uncurry.obj TC) (Functor.uncurry.obj TD) α W O ≫
        R.map ((TD.obj W).map u ≫ ρD W) = ρC (R.obj W) := by
  refine eq_of_counit adj ?_
  rw [counit_comp adj, map_adjunctionTensorMap_comp_counit' adj TC TD α W O, hcoh,
    Category.assoc, Category.assoc, Category.assoc]
  congr 1
  have h1 : (TD.map (adj.counit.app W)).app OD ≫ ρD W =
      ρD (L.obj (R.obj W)) ≫ adj.counit.app W := hρD (adj.counit.app W)
  have h2 : (TD.map (adj.counit.app W)).app (L.obj O) ≫ (TD.obj W).map u =
      (TD.obj (L.obj (R.obj W))).map u ≫ (TD.map (adj.counit.app W)).app OD :=
    ((TD.map (adj.counit.app W)).naturality u).symm
  rw [reassoc_of% h2, h1]

/-- **The right-handed projection-formula map is the left-handed one read across the
commutativity constraints**, at variables. -/
theorem adjunctionTensorMap_swap_eq {C D : Type*} [Category C] [Category D] {L : C ⥤ D}
    {R : D ⥤ C} (adj : L ⊣ R) (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D)
    (α : Functor.uncurry.obj TC ⋙ L ⟶ L.prod L ⋙ Functor.uncurry.obj TD)
    (βC : ∀ A B : C, (TC.obj A).obj B ⟶ (TC.obj B).obj A)
    (βD : ∀ A B : D, (TD.obj A).obj B ⟶ (TD.obj B).obj A)
    (hbr : ∀ A B : C, L.map (βC A B) ≫ α.app (B, A) = α.app (A, B) ≫ βD (L.obj A) (L.obj B))
    (hnat : ∀ (A : D) {B B' : D} (g : B ⟶ B'),
      βD A B ≫ (TD.map g).app A = (TD.obj A).map g ≫ βD A B')
    (hinv : ∀ A B : D, βD A B ≫ βD B A = 𝟙 _) (W : D) (K : C) :
    adjunctionTensorMap adj (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj TC)
        (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj TD)
        (Stacks.Cohomology.DerivedProjectionFormula.comparisonSwap _ _ α) W K =
      βC K (R.obj W) ≫
        adjunctionTensorMap adj (Functor.uncurry.obj TC) (Functor.uncurry.obj TD) α W K ≫
          R.map (βD W (L.obj K)) := by
  refine eq_of_counit adj ?_
  rw [map_adjunctionTensorMap_swap_comp_counit adj TC TD α W K, Functor.map_comp,
    Category.assoc]
  refine Eq.trans ?_ (congrArg (L.map (βC K (R.obj W)) ≫ ·) (counit_comp adj
    (adjunctionTensorMap adj (Functor.uncurry.obj TC) (Functor.uncurry.obj TD) α W K)
    (βD W (L.obj K)))).symm
  rw [map_adjunctionTensorMap_comp_counit' adj TC TD α W K, Category.assoc,
    reassoc_of% (hbr K (R.obj W)), reassoc_of% (hnat (L.obj K) (adj.counit.app W)), hinv,
    Category.comp_id]

end Generic

section MateForm

universe u

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The sheaf-level chase of the level sections square, with the base change map, the
comparison of iterated pushforwards and the projection-formula maps of the `Mate` and adjunction
constructions**, at variable functors between the derived categories of four ringed spaces.
Stacks 0B6B, the transposition identities and the naturality are used here, at variables, where
they are free. At `HasDerivedCategory.standard`, scoped to this declaration. -/
theorem sheaf_square_mate {U' U X' X : RingedSpace.{u, u}}
    {La : (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) ⥤ (DerivedCategory
        (SheafOfModules.{u} (structureSheafRing X')))} {Ra : (DerivedCategory (SheafOfModules.{u}
        (structureSheafRing X'))) ⥤ (DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))}
        (adja : La ⊣ Ra)
    {Lb : (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) ⥤ (DerivedCategory
        (SheafOfModules.{u} (structureSheafRing U)))} {Rb : (DerivedCategory (SheafOfModules.{u}
        (structureSheafRing U))) ⥤ (DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))}
        (adjb : Lb ⊣ Rb)
    {La' : (DerivedCategory (SheafOfModules.{u} (structureSheafRing U))) ⥤ (DerivedCategory
        (SheafOfModules.{u} (structureSheafRing U')))} {Ra' : (DerivedCategory (SheafOfModules.{u}
        (structureSheafRing U'))) ⥤ (DerivedCategory (SheafOfModules.{u} (structureSheafRing U)))}
        (adja' : La' ⊣ Ra')
    {Lb' : (DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))) ⥤ (DerivedCategory
        (SheafOfModules.{u} (structureSheafRing U')))} {Rb' : (DerivedCategory (SheafOfModules.{u}
        (structureSheafRing U'))) ⥤ (DerivedCategory (SheafOfModules.{u} (structureSheafRing X')))}
        (adjb' : Lb' ⊣ Rb')
    {Lc : (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) ⥤ (DerivedCategory
        (SheafOfModules.{u} (structureSheafRing U')))} (eg : Lb ⋙ La' ≅ Lc) (ef : La ⋙ Lb' ≅ Lc)
    {L₂ : (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) ⥤ (DerivedCategory
        (SheafOfModules.{u} (structureSheafRing U')))} (C₂ : Lb ⋙ La' ≅ L₂)
    (TX : (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) ⥤ (DerivedCategory
        (SheafOfModules.{u} (structureSheafRing X))) ⥤ (DerivedCategory (SheafOfModules.{u}
        (structureSheafRing X)))) (TXn : (DerivedCategory (SheafOfModules.{u} (structureSheafRing
        X'))) ⥤ (DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))) ⥤ (DerivedCategory
        (SheafOfModules.{u} (structureSheafRing X'))))
    (TU : (DerivedCategory (SheafOfModules.{u} (structureSheafRing U))) ⥤ (DerivedCategory
        (SheafOfModules.{u} (structureSheafRing U))) ⥤ (DerivedCategory (SheafOfModules.{u}
        (structureSheafRing U)))) (TUn : (DerivedCategory (SheafOfModules.{u} (structureSheafRing
        U'))) ⥤ (DerivedCategory (SheafOfModules.{u} (structureSheafRing U'))) ⥤ (DerivedCategory
        (SheafOfModules.{u} (structureSheafRing U'))))
    (αa : Functor.uncurry.obj TX ⋙ La ⟶ La.prod La ⋙ Functor.uncurry.obj TXn)
    (αb : Functor.uncurry.obj TX ⋙ Lb ⟶ Lb.prod Lb ⋙ Functor.uncurry.obj TU)
    (αa' : Functor.uncurry.obj TU ⋙ La' ⟶ La'.prod La' ⋙ Functor.uncurry.obj TUn)
    (αb' : Functor.uncurry.obj TXn ⋙ Lb' ⟶ Lb'.prod Lb' ⋙ Functor.uncurry.obj TUn)
    {M : (DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))} {G : (DerivedCategory
        (SheafOfModules.{u} (structureSheafRing X')))} {O : (DerivedCategory (SheafOfModules.{u}
        (structureSheafRing U)))} {On : (DerivedCategory (SheafOfModules.{u} (structureSheafRing
        U')))} {Z : (DerivedCategory (SheafOfModules.{u} (structureSheafRing U')))} (s : M ⟶ Ra.obj
        G)
    (uO : La'.obj O ⟶ On)
    (ruN : ∀ Y : (DerivedCategory (SheafOfModules.{u} (structureSheafRing U'))), (TUn.obj Y).obj On
        ⟶ Y) (bridge' : Lb'.obj G ⟶ Z)
    (hsq : Stacks.AffineProjectionFormula.TensorComparisonCompatible eg ef
      (Functor.uncurry.obj TX) (Functor.uncurry.obj TU) (Functor.uncurry.obj TXn)
      (Functor.uncurry.obj TUn) αa αa' αb αb' (Ra.obj G) (Rb.obj O))
    (bcO : La.obj (Rb.obj O) ⟶ Rb'.obj (La'.obj O))
    (e : Lc.obj (Rb.obj O) = L₂.obj (Rb.obj O)) (e₂ : L₂.obj (Rb.obj O) = Lc.obj (Rb.obj O))
    (hadj : (adjb'.homEquiv (La.obj (Rb.obj O)) (La'.obj O)).symm bcO =
      (ef.hom.app (Rb.obj O) ≫ eqToHom e) ≫ C₂.inv.app (Rb.obj O) ≫ La'.map (adjb.counit.app O))
    (hl : eg.hom.app (Rb.obj O) = C₂.hom.app (Rb.obj O) ≫ eqToHom e₂)
    (flipX : (TX.obj M).obj (Rb.obj O) ⟶ (TX.obj (Rb.obj O)).obj M)
    (flipU : (TU.obj (Lb.obj M)).obj (Lb.obj (Rb.obj O)) ⟶
      (TU.obj (Lb.obj (Rb.obj O))).obj (Lb.obj M))
    (flipU' : (TU.obj (Lb.obj M)).obj O ⟶ (TU.obj O).obj (Lb.obj M))
    (luU : (TU.obj O).obj (Lb.obj M) ⟶ Lb.obj M) (ruU : ∀ Y : (DerivedCategory (SheafOfModules.{u}
        (structureSheafRing U))), (TU.obj Y).obj O ⟶ Y)
    (hbraid : Lb.map flipX ≫ αb.app (Rb.obj O, M) = αb.app (M, Rb.obj O) ≫ flipU)
    (hflip : flipU ≫ (TU.map (adjb.counit.app O)).app (Lb.obj M) =
      (TU.obj (Lb.obj M)).map (adjb.counit.app O) ≫ flipU')
    (hlu : flipU' ≫ luU = ruU (Lb.obj M))
    (hru : ∀ {Y Y' : (DerivedCategory (SheafOfModules.{u} (structureSheafRing U)))} (y : Y ⟶ Y'),
        (TU.map y).app O ≫ ruU Y' = ruU Y ≫ y)
    (hruN : ∀ {Y Y' : (DerivedCategory (SheafOfModules.{u} (structureSheafRing U')))} (y : Y ⟶ Y'),
        (TUn.map y).app On ≫ ruN Y' = ruN Y ≫ y)
    (hcoh : ∀ Y : (DerivedCategory (SheafOfModules.{u} (structureSheafRing U))), La'.map (ruU Y) =
        αa'.app (Y, O) ≫ (TUn.obj (La'.obj Y)).map uO ≫
      ruN (La'.obj Y))
    (ψ : Lb.obj M ⟶ Ra'.obj Z)
    (hPA : Lb.map s ≫ Stacks.Cohomology.DerivedBaseChange.Mate.derivedBaseChangeMap adja adja'
      eg ef G ≫ Ra'.map bridge' = ψ) :
    (TX.map s).app (Rb.obj O) ≫
        adjunctionTensorMap adja (Functor.uncurry.obj TX) (Functor.uncurry.obj TXn) αa G
          (Rb.obj O) ≫
        Ra.map (((TXn.obj G).map bcO ≫
            adjunctionTensorMap adjb' (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj TXn)
              (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj TUn)
              (Stacks.Cohomology.DerivedProjectionFormula.comparisonSwap _ _ αb')
              (La'.obj O) G) ≫
          Rb'.map ((TUn.obj (Lb'.obj G)).map uO ≫ ruN (Lb'.obj G) ≫ bridge')) ≫
        (Stacks.Cohomology.DerivedBaseChange.Mate.derivedPushforwardComparisonSquare adja adja'
          adjb adjb' eg ef).natTrans.app Z =
      flipX ≫
        adjunctionTensorMap adjb (Functor.uncurry.obj TX) (Functor.uncurry.obj TU) αb O M ≫
        Rb.map (luU ≫ ψ) :=
  sheaf_square adjb adjb' TX TXn TU TUn αb αb' s bcO uO (ruN (Lb'.obj G)) bridge'
    (Stacks.Cohomology.DerivedBaseChange.Mate.derivedPushforwardComparisonSquare adja adja'
      adjb adjb' eg ef).natTrans
    (fun K => Stacks.Cohomology.DerivedBaseChange.Mate.derivedBaseChangeMap adja adja' eg ef K)
    (fun K => Stacks.Cohomology.DerivedBaseChange.Mate.derivedBaseChangeMap_unit_fac adja adja'
      adjb adjb' eg ef K)
    (adjunctionTensorMap adja (Functor.uncurry.obj TX) (Functor.uncurry.obj TXn) αa G (Rb.obj O))
    (fun H => adjunctionTensorMap adja' (Functor.uncurry.obj TU) (Functor.uncurry.obj TUn) αa'
      (Lb'.obj G) H)
    (adjunctionTensorMap adjb (Functor.uncurry.obj TX) (Functor.uncurry.obj TU) αb O M)
    (adjunctionTensorMap adjb' (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj TXn)
      (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj TUn)
      (Stacks.Cohomology.DerivedProjectionFormula.comparisonSwap _ _ αb') (La'.obj O) G)
    ((Stacks.AffineProjectionFormula.squareCompositeIso eg ef).inv.app (Rb.obj O))
    (Stacks.Cohomology.DerivedProjectionFormula.adjunctionTensorMap_derivedBaseChangeMap adja adja'
      (Functor.uncurry.obj TX) (Functor.uncurry.obj TXn) (Functor.uncurry.obj TU)
      (Functor.uncurry.obj TUn) αa αa' αb αb' eg ef G (Rb.obj O) hsq)
    (map_adjunctionTensorMap_comp_counit' adjb TX TU αb O M)
    (map_adjunctionTensorMap_swap_comp_counit adjb' TXn TUn αb' (La'.obj O) G)
    (adjunctionTensorMap_natural_right' adja' TU TUn αa' (Lb'.obj G) (adjb.counit.app O))
    (by
      have hinv : eg.inv.app (Rb.obj O) = eqToHom e ≫ C₂.inv.app (Rb.obj O) := by
        rw [← cancel_epi (eg.hom.app (Rb.obj O)), Iso.hom_inv_id_app, hl, Category.assoc,
          eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Iso.hom_inv_id_app]
      refine (Adjunction.homEquiv_counit _ _ _ _).symm.trans (hadj.trans ?_)
      rw [Stacks.AffineProjectionFormula.squareCompositeIso_inv_app, hinv]
      simp only [Category.assoc])
    flipX flipU flipU' luU ruU hbraid hflip hlu hru
    (adjunctionTensorMap_unit_comp adja' TU TUn αa' uO ruU ruN hruN hcoh (Lb'.obj G)) ψ hPA

end MateForm

section GenericLeray

variable {DX DXn DU DUn MA MAn : Type*} [Category DX] [Category DXn] [Category DU]
  [Category DUn] [Category MA] [Category MAn]
  {Ra : DXn ⥤ DX} {Rb : DU ⥤ DX} {Ra' : DUn ⥤ DU} {Rb' : DUn ⥤ DXn}
  {Γp : DX ⥤ MA} {Γpn : DXn ⥤ MAn} {Γq : DU ⥤ MA} {Γqn : DUn ⥤ MAn}
  {rs : MAn ⥤ MA} {rsA : MA ⥤ MA} {rsAn : MAn ⥤ MAn}
  (ℓa : Ra ⋙ Γp ≅ Γpn ⋙ rs) (ℓb : Rb ⋙ Γp ≅ Γq ⋙ rsA) (ℓa' : Ra' ⋙ Γq ≅ Γqn ⋙ rs)
  (ℓb' : Rb' ⋙ Γpn ≅ Γqn ⋙ rsAn) (eA : rsA ≅ 𝟭 MA) (eAn : rsAn ≅ 𝟭 MAn)

/-- The compatibility of the Leray identifications `ℓa`, `ℓb'` along one side of a square of
pushforwards with `ℓb`, `ℓa'` along the other, through the comparison `cmp`, at `Y`. It is a
definition so that a statement of it at concrete functors is elaborated from its arguments
alone. -/
def LeraySquare (cmp : Rb' ⋙ Ra ⟶ Ra' ⋙ Rb) (Y : DUn) : Prop :=
  ℓa.hom.app (Rb'.obj Y) ≫ rs.map (ℓb'.hom.app Y) ≫ rs.map (eAn.hom.app (Γqn.obj Y)) =
    Γp.map (cmp.app Y) ≫ ℓb.hom.app (Ra'.obj Y) ≫ eA.hom.app (Γq.obj (Ra'.obj Y)) ≫
      ℓa'.hom.app Y

/-- **The Leray identifications around a square of pushforwards are compatible**, at variables:
the two factorizations `Rb' ⋙ Ra ≅ Rk` and `Ra' ⋙ Rb ≅ Rk'` of a composite, whose Leray
identifications are the composites of the factors and agree up to `Rk = Rk'`. -/
theorem leray_square {Rk Rk' : DUn ⥤ DX} (cA : Rb' ⋙ Ra ≅ Rk) (cB : Ra' ⋙ Rb ≅ Rk')
    (pF : Rk = Rk') (LA : Rk ⋙ Γp ≅ Γqn ⋙ rs) (LB : Rk' ⋙ Γp ≅ Γqn ⋙ rs)
    (rA : rsAn ⋙ rs ≅ rs) (rB : rs ⋙ rsA ≅ rs) (cmp : Rb' ⋙ Ra ⟶ Ra' ⋙ Rb) (Y : DUn)
    (hA : LA.hom.app Y = Γp.map (cA.inv.app Y) ≫ ℓa.hom.app (Rb'.obj Y) ≫
      rs.map (ℓb'.hom.app Y) ≫ rA.hom.app (Γqn.obj Y))
    (hB : LB.hom.app Y = Γp.map (cB.inv.app Y) ≫ ℓb.hom.app (Ra'.obj Y) ≫
      rsA.map (ℓa'.hom.app Y) ≫ rB.hom.app (Γqn.obj Y))
    (hT : LA.hom.app Y ≍ LB.hom.app Y) (hcmp : cmp = cA.hom ≫ eqToHom pF ≫ cB.inv)
    (h₂ : rA.hom.app (Γqn.obj Y) = rs.map (eAn.hom.app (Γqn.obj Y)))
    (h₃ : rB.hom.app (Γqn.obj Y) = eA.hom.app (rs.obj (Γqn.obj Y))) :
    LeraySquare ℓa ℓb ℓa' ℓb' eA eAn cmp Y := by
  unfold LeraySquare
  subst pF
  have hT' : LA.hom.app Y = LB.hom.app Y := eq_of_heq hT
  have hcmp' : cmp.app Y = cA.hom.app Y ≫ cB.inv.app Y := by
    rw [hcmp, eqToHom_refl, Category.id_comp, NatTrans.comp_app]
  have hA' : Γp.map (cA.hom.app Y) ≫ LA.hom.app Y = ℓa.hom.app (Rb'.obj Y) ≫
      rs.map (ℓb'.hom.app Y) ≫ rs.map (eAn.hom.app (Γqn.obj Y)) := by
    rw [hA, ← h₂, ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp]
  have hn : rsA.map (ℓa'.hom.app Y) ≫ eA.hom.app (rs.obj (Γqn.obj Y)) =
      eA.hom.app (Γq.obj (Ra'.obj Y)) ≫ ℓa'.hom.app Y := eA.hom.naturality (ℓa'.hom.app Y)
  rw [← hA', hT', hB, hcmp', h₃, hn, Functor.map_comp]
  simp only [Category.assoc]

variable {La : DX ⥤ DXn} {Lb : DX ⥤ DU} {La' : DU ⥤ DUn} {Lb' : DXn ⥤ DUn}

/-- **Assembly of the level sections square**, at variables: the sheaf-level square `hsheaf`, the
compatibility `hsq` of the Leray identifications around the square, and the identification
`hpost` of the tail of the right-hand side give the square in the category of linear objects. -/
theorem assembly {Q : DX} {K : DXn} {Y : DUn} {Z : DUn} {W : DU}
    (pf : Q ⟶ Ra.obj K) (ν : K ⟶ Rb'.obj Y) (κ : Y ⟶ Z) (cmp : Rb' ⋙ Ra ⟶ Ra' ⋙ Rb)
    (pb : Q ⟶ Rb.obj W) (ψ : W ⟶ Ra'.obj Z)
    (hsheaf : pf ≫ Ra.map (ν ≫ Rb'.map κ) ≫ cmp.app Z = pb ≫ Rb.map ψ)
    (hsq : LeraySquare ℓa ℓb ℓa' ℓb' eA eAn cmp Z)
    (post : Γq.obj W ⟶ rs.obj (Γqn.obj Z)) (hpost : post = Γq.map ψ ≫ ℓa'.hom.app Z) :
    (Γp.map pf ≫ ℓa.hom.app K) ≫
        rs.map (Γpn.map ν ≫ ℓb'.hom.app Y ≫ eAn.hom.app (Γqn.obj Y) ≫ Γqn.map κ) =
      (Γp.map pb ≫ ℓb.hom.app W ≫ eA.hom.app (Γq.obj W)) ≫ post := by
  have n1 : ℓa.hom.app K ≫ rs.map (Γpn.map ν) = Γp.map (Ra.map ν) ≫ ℓa.hom.app (Rb'.obj Y) :=
    (ℓa.hom.naturality ν).symm
  have n2 : ℓb'.hom.app Y ≫ rsAn.map (Γqn.map κ) = Γpn.map (Rb'.map κ) ≫ ℓb'.hom.app Z :=
    (ℓb'.hom.naturality κ).symm
  have n3 : eAn.hom.app (Γqn.obj Y) ≫ Γqn.map κ = rsAn.map (Γqn.map κ) ≫ eAn.hom.app (Γqn.obj Z) :=
    (eAn.hom.naturality (Γqn.map κ)).symm
  have n4 : ℓa.hom.app (Rb'.obj Y) ≫ rs.map (Γpn.map (Rb'.map κ)) =
      Γp.map (Ra.map (Rb'.map κ)) ≫ ℓa.hom.app (Rb'.obj Z) := (ℓa.hom.naturality (Rb'.map κ)).symm
  have n5 : ℓb.hom.app W ≫ rsA.map (Γq.map ψ) = Γp.map (Rb.map ψ) ≫ ℓb.hom.app (Ra'.obj Z) :=
    (ℓb.hom.naturality ψ).symm
  have n6 : eA.hom.app (Γq.obj W) ≫ Γq.map ψ = rsA.map (Γq.map ψ) ≫ eA.hom.app (Γq.obj (Ra'.obj Z))
      :=
    (eA.hom.naturality (Γq.map ψ)).symm
  have lhs : (Γp.map pf ≫ ℓa.hom.app K) ≫
        rs.map (Γpn.map ν ≫ ℓb'.hom.app Y ≫ eAn.hom.app (Γqn.obj Y) ≫ Γqn.map κ) =
      Γp.map (pf ≫ Ra.map (ν ≫ Rb'.map κ)) ≫ ℓa.hom.app (Rb'.obj Z) ≫ rs.map (ℓb'.hom.app Z) ≫
        rs.map (eAn.hom.app (Γqn.obj Z)) := by
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% n1, ← rs.map_comp (eAn.hom.app (Γqn.obj Y)) (Γqn.map κ), n3, rs.map_comp,
      ← rs.map_comp_assoc (ℓb'.hom.app Y), n2, rs.map_comp, Category.assoc, reassoc_of% n4]
  unfold LeraySquare at hsq
  rw [lhs, hsq, ← Functor.map_comp_assoc, Category.assoc, hsheaf, hpost]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% n6, reassoc_of% n5]

/-- `assembly` in the shape in which the level sections square presents itself. -/
theorem assembly' {Q Q' P₁ : DX} {K : DXn} {Y : DUn} {Z : DUn} {W₀ W : DU} {T' : MA}
    (s₁ : Q ⟶ Q') (p₁ : Q' ⟶ Ra.obj K) (ν : K ⟶ Rb'.obj Y) (κ : Y ⟶ Z)
    (cmp : Rb' ⋙ Ra ⟶ Ra' ⋙ Rb) (f₁ : Q ⟶ P₁) (p₂ : P₁ ⟶ Rb.obj W₀) (lu : W₀ ⟶ W)
    (ψ : W ⟶ Ra'.obj Z) (br : Γq.obj W ⟶ T') (L : T' ⟶ rs.obj (Γqn.obj Z))
    (hsheaf : s₁ ≫ p₁ ≫ Ra.map (ν ≫ Rb'.map κ) ≫ cmp.app Z = f₁ ≫ p₂ ≫ Rb.map (lu ≫ ψ))
    (hsq : LeraySquare ℓa ℓb ℓa' ℓb' eA eAn cmp Z)
    (hpost : br ≫ L = Γq.map ψ ≫ ℓa'.hom.app Z) (f₁' : Q ⟶ P₁) (hf : f₁' = f₁)
    (lu' : W₀ ⟶ W) (hl : lu' = lu) :
    (Γp.map s₁ ≫ Γp.map p₁ ≫ ℓa.hom.app K) ≫
        rs.map (Γpn.map ν ≫ ℓb'.hom.app Y ≫ eAn.hom.app (Γqn.obj Y) ≫ Γqn.map κ) =
      ((Γp.map f₁' ≫ Γp.map p₂ ≫ Γp.map (Rb.map lu') ≫ ℓb.hom.app W ≫ eA.hom.app (Γq.obj W) ≫
        𝟙 _) ≫ br) ≫ L := by
  rw [hf, hl]
  have h := assembly ℓa ℓb ℓa' ℓb' eA eAn (s₁ ≫ p₁) ν κ cmp (f₁ ≫ p₂ ≫ Rb.map lu) ψ
    (by simpa only [Category.assoc, Functor.map_comp] using hsheaf) hsq (br ≫ L) hpost
  simpa only [Category.assoc, Functor.map_comp, Category.id_comp] using h

end GenericLeray

section Monoidal

open Stacks.SheafOfModules.DerivedMonoidal MonoidalCategory
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)
open Stacks.Cohomology.DerivedProjectionFormula (singleUnit)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

variable (Z : RingedSpace.{u, u})
  [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The commutativity constraint of the derived tensor product on a ringed space, at the
spelling of the derived categories of the derived pullback and pushforward. -/
def tensorBraidingHom (M N : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z))) :
    ((derivedTensorProductFunctor Z.sheaf).obj M).obj N ⟶
      ((derivedTensorProductFunctor Z.sheaf).obj N).obj M :=
  canonicalBraidingHom Z.sheaf M N

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The left unit constraint of the derived tensor product on a ringed space. -/
def tensorLeftUnitorHom (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z))) :
    ((derivedTensorProductFunctor Z.sheaf).obj (singleUnit Z)).obj M ⟶ M :=
  canonicalLeftUnitorHom Z.sheaf M

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The right unit constraint of the derived tensor product on a ringed space. -/
def tensorRightUnitorHom (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z))) :
    ((derivedTensorProductFunctor Z.sheaf).obj M).obj (singleUnit Z) ⟶ M :=
  canonicalRightUnitorHom Z.sheaf M

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The commutativity constraint of the derived tensor product is natural in the second
variable, at the spelling of the reseated monoidal structure. -/
theorem canonicalBraidingHom_naturality_right
    (M : Stacks.DerivedTensor.RingedSite.DerivedModules Z.sheaf)
    {A B : Stacks.DerivedTensor.RingedSite.DerivedModules Z.sheaf} (g : A ⟶ B) :
    canonicalBraidingHom Z.sheaf M A ≫ ((derivedTensorProductFunctor Z.sheaf).map g).app M =
      ((derivedTensorProductFunctor Z.sheaf).obj M).map g ≫ canonicalBraidingHom Z.sheaf M B := by
  let := canonicalDerivedMonoidal Z.sheaf
  let := canonicalDerivedSymmetric Z.sheaf
  exact (BraidedCategory.braiding_naturality_right M g).symm

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The commutativity constraint followed by the left unit constraint is the right unit
constraint, at the spelling of the reseated monoidal structure. -/
theorem canonicalBraidingHom_comp_canonicalLeftUnitorHom
    (M : Stacks.DerivedTensor.RingedSite.DerivedModules Z.sheaf) :
    canonicalBraidingHom Z.sheaf M (singleUnit Z) ≫ canonicalLeftUnitorHom Z.sheaf M =
      canonicalRightUnitorHom Z.sheaf M := by
  let := canonicalDerivedMonoidal Z.sheaf
  let := canonicalDerivedSymmetric Z.sheaf
  exact braiding_leftUnitor M

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The right unit constraint is natural, at the spelling of the reseated monoidal
structure. -/
theorem canonicalRightUnitorHom_naturality
    {Y Y' : Stacks.DerivedTensor.RingedSite.DerivedModules Z.sheaf} (y : Y ⟶ Y') :
    ((derivedTensorProductFunctor Z.sheaf).map y).app (singleUnit Z) ≫
        canonicalRightUnitorHom Z.sheaf Y' = canonicalRightUnitorHom Z.sheaf Y ≫ y := by
  let := canonicalDerivedMonoidal Z.sheaf
  exact rightUnitor_naturality y

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The commutativity constraint of the derived tensor product is natural in the second
variable. -/
theorem tensorBraidingHom_naturality_right
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z)))
    {A B : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z))} (g : A ⟶ B) :
    tensorBraidingHom Z M A ≫ ((derivedTensorProductFunctor Z.sheaf).map g).app M =
      ((derivedTensorProductFunctor Z.sheaf).obj M).map g ≫ tensorBraidingHom Z M B :=
  canonicalBraidingHom_naturality_right Z M g

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The commutativity constraint followed by the left unit constraint is the right unit
constraint. -/
theorem tensorBraidingHom_comp_tensorLeftUnitorHom
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z))) :
    tensorBraidingHom Z M (singleUnit Z) ≫ tensorLeftUnitorHom Z M = tensorRightUnitorHom Z M :=
  canonicalBraidingHom_comp_canonicalLeftUnitorHom Z M

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The right unit constraint is natural. -/
theorem tensorRightUnitorHom_naturality
    {Y Y' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z))} (y : Y ⟶ Y') :
    ((derivedTensorProductFunctor Z.sheaf).map y).app (singleUnit Z) ≫ tensorRightUnitorHom Z Y' =
      tensorRightUnitorHom Z Y ≫ y :=
  canonicalRightUnitorHom_naturality Z y

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The comparison of Tag 079U carries the commutativity constraint to the commutativity
constraint. -/
theorem derivedPullback_map_tensorBraidingHom
    (M N : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    (derivedPullback f).map (tensorBraidingHom Y M N) ≫
        (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso f).hom.app (N, M) =
      (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso f).hom.app (M, N) ≫
        tensorBraidingHom X ((derivedPullback f).obj M) ((derivedPullback f).obj N) :=
  Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_braiding f M N

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The right unit coherence of the comparison of Tag 079U, in the form
`Lf^* ρ = α ≫ (1 ⊗ u) ≫ ρ`. -/
theorem derivedPullback_map_tensorRightUnitorHom
    (W : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    (derivedPullback f).map (tensorRightUnitorHom Y W) =
      (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso f).hom.app
          (W, singleUnit Y) ≫
        ((derivedTensorProductFunctor X.sheaf).obj ((derivedPullback f).obj W)).map
            (Stacks.Cohomology.DerivedProjectionFormula.derivedPullbackUnitIso f).hom ≫
        tensorRightUnitorHom X ((derivedPullback f).obj W) := by
  have h := Stacks.Cohomology.DerivedPullbackTensor.rightUnitorCoherence_canonical f W
  simp only [canonicalWhiskerLeft, derivedTensorBifunctorOfSite] at h
  refine Eq.trans ?_ (congrArg (fun m =>
      (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso f).hom.app
          (W, singleUnit Y) ≫
        ((derivedTensorProductFunctor X.sheaf).obj ((derivedPullback f).obj W)).map
            (Stacks.Cohomology.DerivedProjectionFormula.derivedPullbackUnitIso f).hom ≫ m) h).symm
  exact ((congrArg (_ ≫ ·) ((((derivedTensorProductFunctor X.sheaf).obj
    ((derivedPullback f).obj W)).mapIso
      (Stacks.Cohomology.DerivedProjectionFormula.derivedPullbackUnitIso f)).hom_inv_id_assoc
        _)).trans (((Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso f).app
          (W, singleUnit Y)).hom_inv_id_assoc _)).symm

end Monoidal

section RingedSpaces

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.Cohomology.DerivedBaseChange
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)
open Stacks.Cohomology.DerivedProjectionFormula (singleUnit projectionFormulaMap
  projectionFormulaMapRight pullbackTensorComparison derivedPullbackUnitIso)

universe u

variable {U' U X' X : RingedSpace.{u, u}} (a' : U' ⟶ U) (b' : U' ⟶ X') (b : U ⟶ X) (a : X' ⟶ X)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The sheaf-level level sections square, for a commutative square of ringed spaces**
`a' ≫ b = b' ≫ a`, with the projection-formula maps written as adjunction-tensor maps. At
`HasDerivedCategory.standard`, scoped to this declaration. -/
theorem sheaf_square_ringedSpace (sq1 : a' ≫ b = b' ≫ a) (sq2 : b' ≫ a = a' ≫ b)
    {M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    {G : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
    {Z : DerivedCategory (SheafOfModules.{u} (structureSheafRing U'))}
    (s : M ⟶ (derivedPushforward a).obj G) (bridge' : (derivedPullback b').obj G ⟶ Z)
    (ψ : (derivedPullback b).obj M ⟶ (derivedPushforward a').obj Z)
    (hPA : (derivedPullback b).map s ≫ Mate.derivedBaseChangeMap (derivedAdjunction a)
      (derivedAdjunction a') (derivedPullbackCompIsoLeft b' a' a b sq2)
      (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical b' a) G ≫
      (derivedPushforward a').map bridge' = ψ) :
    ((derivedTensorProductFunctor X.sheaf).map s).app ((derivedPushforward b).obj (singleUnit U)) ≫
      projectionFormulaMap a G ((derivedPushforward b).obj (singleUnit U)) ≫
      (derivedPushforward a).map
        ((((derivedTensorProductFunctor X'.sheaf).obj G).map
            (derivedBaseChangeMap a' b' b a sq1 (singleUnit U)) ≫
          projectionFormulaMapRight b' G ((derivedPullback a').obj (singleUnit U))) ≫
          (derivedPushforward b').map
            (((derivedTensorProductFunctor U'.sheaf).obj ((derivedPullback b').obj G)).map
                (derivedPullbackUnitIso a').hom ≫
              tensorRightUnitorHom U' ((derivedPullback b').obj G) ≫ bridge')) ≫
      (Mate.derivedPushforwardComparisonSquare (derivedAdjunction a) (derivedAdjunction a')
        (derivedAdjunction b) (derivedAdjunction b') (derivedPullbackCompIsoLeft b' a' a b sq2)
        (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical b' a)).natTrans.app Z =
    tensorBraidingHom X M ((derivedPushforward b).obj (singleUnit U)) ≫
      projectionFormulaMap b (singleUnit U) M ≫
      (derivedPushforward b).map (tensorLeftUnitorHom U ((derivedPullback b).obj M) ≫ ψ) :=
  sheaf_square_mate (derivedAdjunction a) (derivedAdjunction b) (derivedAdjunction a')
    (derivedAdjunction b') (derivedPullbackCompIsoLeft b' a' a b sq2)
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical b' a)
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical a' b)
    (derivedTensorProductFunctor X.sheaf) (derivedTensorProductFunctor X'.sheaf)
    (derivedTensorProductFunctor U.sheaf) (derivedTensorProductFunctor U'.sheaf)
    (pullbackTensorComparison a) (pullbackTensorComparison b) (pullbackTensorComparison a')
    (pullbackTensorComparison b')
    s (derivedPullbackUnitIso a').hom
    (fun Y => tensorRightUnitorHom U' Y) bridge'
    (Stacks.Cohomology.DerivedProjectionFormula.tensorComparisonCompatible_of_comparisonSquare
      _ _ _ _ _ _ _ _
      (Stacks.Cohomology.DerivedRelativeCupProduct.derivedPullbackTensorIso_comparison_square
        b' a' a b sq2) _ _)
    (derivedBaseChangeMap a' b' b a sq1 (singleUnit U)) _ _
    (derivedBaseChangeMap_adjoint_split a' b' b a sq1 (singleUnit U) (by rw [sq1]))
    (derivedPullbackCompIsoLeft_hom_app_eqToHom b' a' a b sq2 _ (by rw [sq1]))
    (tensorBraidingHom X M _) (tensorBraidingHom U _ _) (tensorBraidingHom U _ _)
    (tensorLeftUnitorHom U _) (fun Y => tensorRightUnitorHom U Y)
    (derivedPullback_map_tensorBraidingHom b M _)
    (tensorBraidingHom_naturality_right U _ _)
    (tensorBraidingHom_comp_tensorLeftUnitorHom U _)
    (fun y => tensorRightUnitorHom_naturality U y)
    (fun y => tensorRightUnitorHom_naturality U' y)
    (fun Y => derivedPullback_map_tensorRightUnitorHom a' Y) ψ hPA

end RingedSpaces


end AlgebraicGeometry.GrothendieckExistence.LevelSectionsSquare

namespace AlgebraicGeometry.GrothendieckExistence.ExistenceSituation

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open AlgebraicGeometry.GrothendieckExistence.LevelSectionsSquare

universe u

variable (S : ExistenceSituation.{u})

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The Leray identifications around the square `Uₙ ⟶ U`, `Xₙ ⟶ X` are compatible**: the
identification for `iₙ` followed by the one for `Uₙ ⟶ Xₙ`, read over `A`, is the comparison
`Riₙ,* R(Uₙ ⟶ Xₙ)_* ⟶ R(U ⟶ X)_* R(Uₙ ⟶ U)_*` of the two iterated derived pushforwards followed
by the identification for `U ⟶ X` and the one for `Uₙ ⟶ U`. At `HasDerivedCategory.standard`,
scoped to this declaration. -/
theorem leraySquare_levelOpen (U : S.X.left.Opens) (n : ℕ)
    (Y : DerivedCategory (S.levelOpen U n).toScheme.Modules) :
    LeraySquare
      (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso (S.closedImmersion n) S.X.hom
        (S.levelStructure n) (S.limitProjection n) (S.closedImmersion_comp_hom n))
      (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso U.ι S.X.hom (U.ι ≫ S.X.hom)
        (RingHom.id _) (Stacks.Cohomology.CountableSections.comp_eq_comp_specMap_id S.X.hom U.ι))
      (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso (S.levelOpenImmersion U n)
        (U.ι ≫ S.X.hom) ((S.levelOpen U n).ι ≫ S.levelStructure n) (S.limitProjection n)
        (S.levelOpenImmersion_comp U n))
      (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso (S.levelOpen U n).ι
        (S.levelStructure n) ((S.levelOpen U n).ι ≫ S.levelStructure n) (RingHom.id _)
        (Stacks.Cohomology.CountableSections.comp_eq_comp_specMap_id (S.levelStructure n)
          (S.levelOpen U n).ι))
      (restrictScalarsIdDerivedIso (RingHom.id _) rfl).symm
      (restrictScalarsIdDerivedIso (RingHom.id _) rfl).symm
      (Stacks.Cohomology.DerivedBaseChange.Mate.derivedPushforwardComparisonSquare
          (derivedAdjunction (S.closedImmersion n).toLRSHom.toShHom)
          (derivedAdjunction (S.levelOpenImmersion U n).toLRSHom.toShHom)
          (derivedAdjunction U.ι.toLRSHom.toShHom)
          (derivedAdjunction (S.levelOpen U n).ι.toLRSHom.toShHom)
          (Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft
            (S.levelOpen U n).ι.toLRSHom.toShHom (S.levelOpenImmersion U n).toLRSHom.toShHom
            (S.closedImmersion n).toLRSHom.toShHom U.ι.toLRSHom.toShHom (S.levelOpen_square U n))
          (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
            (S.levelOpen U n).ι.toLRSHom.toShHom
            (S.closedImmersion n).toLRSHom.toShHom)).natTrans Y := by
  have sqS : (S.levelOpen U n).ι ≫ S.closedImmersion n = S.levelOpenImmersion U n ≫ U.ι :=
    (morphismRestrict_ι _ _).symm
  have hk' : ((S.levelOpen U n).ι ≫ S.closedImmersion n) ≫ S.X.hom =
      ((S.levelOpen U n).ι ≫ S.levelStructure n) ≫
        Spec.map (CommRingCat.ofHom (S.limitProjection n)) := by
    rw [Category.assoc, S.closedImmersion_comp_hom n, Category.assoc]
  have hk'' : (S.levelOpenImmersion U n ≫ U.ι) ≫ S.X.hom =
      ((S.levelOpen U n).ι ≫ S.levelStructure n) ≫
        Spec.map (CommRingCat.ofHom (S.limitProjection n)) := by
    rw [← sqS]; exact hk'
  have hA := derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso_comp
    (S.levelOpen U n).ι (S.closedImmersion n) S.X.hom (S.levelStructure n)
    ((S.levelOpen U n).ι ≫ S.levelStructure n) (S.limitProjection n) (RingHom.id _)
    (S.limitProjection n) (RingHom.id_comp _).symm (S.closedImmersion_comp_hom n)
    (Stacks.Cohomology.CountableSections.comp_eq_comp_specMap_id (S.levelStructure n)
      (S.levelOpen U n).ι) hk' Y
  have hB := derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso_comp
    (S.levelOpenImmersion U n) U.ι S.X.hom (U.ι ≫ S.X.hom)
    ((S.levelOpen U n).ι ≫ S.levelStructure n) (RingHom.id _) (S.limitProjection n)
    (S.limitProjection n) (RingHom.comp_id _).symm
    (Stacks.Cohomology.CountableSections.comp_eq_comp_specMap_id S.X.hom U.ι)
    (S.levelOpenImmersion_comp U n) hk'' Y
  have hT := derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso_congr_hom_app sqS
    S.X.hom ((S.levelOpen U n).ι ≫ S.levelStructure n) (S.limitProjection n) hk' hk'' Y
  have hcmp :=
    Stacks.Cohomology.DerivedBaseChange.derivedPushforwardComparisonSquare_natTrans_eq_compIso
      (S.levelOpen U n).ι.toLRSHom.toShHom (S.levelOpenImmersion U n).toLRSHom.toShHom
      (S.closedImmersion n).toLRSHom.toShHom U.ι.toLRSHom.toShHom (S.levelOpen_square U n)
  have h₂ := derivedRestrictScalarsComp_id_right_hom_app (S.limitProjection n)
    (RingHom.id_comp _).symm ((derivedGlobalSectionsOver ((S.levelOpen U n).ι ≫
      S.levelStructure n)).obj Y)
  have h₃ := derivedRestrictScalarsComp_id_left_hom_app (S.limitProjection n)
    (RingHom.comp_id _).symm ((derivedGlobalSectionsOver ((S.levelOpen U n).ι ≫
      S.levelStructure n)).obj Y)
  exact leray_square _ _ _ _ (restrictScalarsIdDerivedIso (RingHom.id _) rfl).symm
    (restrictScalarsIdDerivedIso (RingHom.id _) rfl).symm
    (derivedPushforwardCompIso (S.levelOpen U n).ι.toLRSHom.toShHom
      (S.closedImmersion n).toLRSHom.toShHom)
    (derivedPushforwardCompIso (S.levelOpenImmersion U n).toLRSHom.toShHom U.ι.toLRSHom.toShHom)
    _ _ _ _ _ _ Y hA hB hT hcmp h₂ h₃

end AlgebraicGeometry.GrothendieckExistence.ExistenceSituation

namespace AlgebraicGeometry.GrothendieckExistence.ExistenceSituation

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)
open Stacks.Cohomology.DerivedProjectionFormula (singleUnit projectionFormulaMap
  projectionFormulaMapRight derivedPullbackUnitIso)
open AlgebraicGeometry.GrothendieckExistence.LevelSectionsSquare

universe u

variable (S : ExistenceSituation.{u})

attribute [local instance 10000] HasDerivedCategory.standard in
/-- Flat base change along `Xₙ ⟶ X` for the open immersion `U ⟶ X` at `𝒪_U`
([Stacks, Tag 08IB]): `Liₙ^* Rι_* 𝒪_U ⟶ R(Uₙ ⟶ Xₙ)_* L(Uₙ ⟶ U)^* 𝒪_U` is invertible for `U`
quasi-compact. At `HasDerivedCategory.standard`, scoped to this declaration. -/
theorem isIso_derivedBaseChangeMap_levelOpen_unit (U : S.X.left.Opens)
    (hU : IsCompact (U : Set S.X.left)) (n : ℕ) :
    IsIso (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap
      (S.levelOpenImmersion U n).toLRSHom.toShHom (S.levelOpen U n).ι.toLRSHom.toShHom
      U.ι.toLRSHom.toShHom (S.closedImmersion n).toLRSHom.toShHom (S.levelOpen_square U n).symm
      (singleUnit U.toScheme.toRingedSpace)) := by
  have : CompactSpace U := isCompact_iff_compactSpace.mp hU
  have := S.separated
  exact derivedBaseChangeIsIsoOnQuasicoherent (S.levelOpenImmersion U n) (S.levelOpen U n).ι
    U.ι (S.closedImmersion n) (isPullback_morphismRestrict (S.closedImmersion n) U)
    inferInstance inferInstance (torIndependent_of_flat_left U.ι (S.closedImmersion n)) _
    (derivedUnitObject U) (fun j =>
        Stacks.Cohomology.CountableSections.isQuasicoherent_homology_derivedUnitObject U j)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The right-handed projection formula along `Uₙ ⟶ Xₙ` at `(ℱₙ, L(Uₙ ⟶ U)^* 𝒪_U)` is
invertible ([Stacks, Tag 08EU]). At `HasDerivedCategory.standard`, scoped to this declaration.
-/
theorem isIso_projectionFormulaMapRight_levelOpen (U : S.X.left.Opens)
    (hU : IsCompact (U : Set S.X.left)) (n : ℕ) :
    IsIso (projectionFormulaMapRight (S.levelOpen U n).ι.toLRSHom.toShHom
      ((DerivedCategory.singleFunctor _ 0).obj (S.F n))
      ((derivedPullback (S.levelOpenImmersion U n).toLRSHom.toShHom).obj
        (singleUnit U.toScheme.toRingedSpace))) := by
  have := S.closedSchemeProjection n
  have := S.finitelyPresented n
  have := S.separated
  have : QuasiSeparatedSpace (schemeAt S.system S.X n) :=
    quasiSeparatedSpace_of_quasiSeparated (S.closedImmersion n)
  have : CompactSpace (S.levelOpen U n) := isCompact_iff_compactSpace.mp
    ((S.closedImmersion n).isClosedEmbedding.isCompact_preimage hU)
  have hG : ∀ j : ℤ, ((DerivedCategory.homologyFunctor _ j).obj
      ((DerivedCategory.singleFunctor _ 0).obj (S.F n))).IsQuasicoherent := fun j => by
    by_cases hj : j = 0
    · subst hj
      exact (SheafOfModules.isQuasicoherent.{u} _).prop_of_iso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _).symm
        (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isFinitePresentation
          _ (S.finitelyPresented n)).1
    · exact
        (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isFinitePresentation
        _ (isFinitePresentation_of_isZero _
          (DerivedCategory.Plus.isZero_homologyFunctor_singleFunctor_obj _ hj))).1
  have hE := Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel
    (S.levelOpenImmersion U n) (derivedUnitObject U)
    (fun j => Stacks.Cohomology.CountableSections.isQuasicoherent_homology_derivedUnitObject U j)
  have hPF :=
      Stacks.Cohomology.ProjectionFormulaQCoh.projectionFormulaMap_isIso_of_isQuasicoherent_homology
    (S.levelOpen U n).ι inferInstance inferInstance _ _ hE hG
  have e := adjunctionTensorMap_swap_eq (derivedAdjunction (S.levelOpen U n).ι.toLRSHom.toShHom)
    (derivedTensorProductFunctor (schemeAt S.system S.X n).toRingedSpace.sheaf)
    (derivedTensorProductFunctor (S.levelOpen U n).toScheme.toRingedSpace.sheaf)
    (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison
      (S.levelOpen U n).ι.toLRSHom.toShHom)
    (fun A B => tensorBraidingHom _ A B) (fun A B => tensorBraidingHom _ A B)
    (fun A B => derivedPullback_map_tensorBraidingHom _ A B)
    (fun A _ _ g => tensorBraidingHom_naturality_right _ A g)
    (fun A B => Stacks.Cohomology.SupportedComplexes.canonicalBraidingHom_symmetry _ A B)
    ((derivedPullback (S.levelOpenImmersion U n).toLRSHom.toShHom).obj
      (singleUnit U.toScheme.toRingedSpace))
    ((DerivedCategory.singleFunctor _ 0).obj (S.F n))
  have hb : ∀ (Z : RingedSpace.{u, u}) (A B : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing Z))),
      IsIso (tensorBraidingHom Z A B) := fun Z A B =>
    ⟨tensorBraidingHom Z B A, Stacks.Cohomology.SupportedComplexes.canonicalBraidingHom_symmetry Z
        A B,
      Stacks.Cohomology.SupportedComplexes.canonicalBraidingHom_symmetry Z B A⟩
  have := hb
  exact (congrArg IsIso e).mpr (@IsIso.comp_isIso _ _ _ _ _ _ _ (hb _ _ _)
    (@IsIso.comp_isIso _ _ _ _ _ _ _ hPF (@Functor.map_isIso _ _ _ _ _ _ _ _ (hb _ _ _))))

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The right unit constraint of the derived tensor product is invertible. -/
theorem isIso_canonicalRightUnitorHom (Z : RingedSpace.{u, u})
    (M : Stacks.DerivedTensor.RingedSite.DerivedModules Z.sheaf) :
    IsIso (Stacks.SheafOfModules.DerivedMonoidal.canonicalRightUnitorHom Z.sheaf M) := by
  let := Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Z.sheaf
  exact inferInstanceAs (IsIso (MonoidalCategory.rightUnitor M).hom)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The right unit constraint of the derived tensor product is invertible. -/
theorem isIso_tensorRightUnitorHom (Z : RingedSpace.{u, u})
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z))) :
    IsIso (tensorRightUnitorHom Z M) :=
  isIso_canonicalRightUnitorHom Z M

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The level isomorphism of the projection-formula square of [Stacks, Tag 0CTG]**,
`RΓ_{Aₙ}(Xₙ, ℱₙ ⊗^𝐋 Liₙ^* Rι_* 𝒪_U) ≅ RΓ_{Aₙ}(Uₙ, ℱₙ)`: flat base change
`Liₙ^* Rι_* 𝒪_U ≅ R(Uₙ ⟶ Xₙ)_* 𝒪_{Uₙ}` ([Stacks, Tag 08IB]), the projection formula along
`Uₙ ⟶ Xₙ` ([Stacks, Tag 08EU]), the `Aₙ`-linear Leray identification for `Uₙ ⟶ Xₙ`, the unit
constraint and restriction to `Uₙ`. At `HasDerivedCategory.standard`, scoped to this declaration.
-/
def levelSectionsIso (U : S.X.left.Opens) (hU : IsCompact (U : Set S.X.left)) (n : ℕ) :
    S.levelTensor n ((derivedPushforward U.ι.toLRSHom.toShHom).obj (derivedUnitObject U)) ≅
      S.levelSectionsOver U n :=
  (derivedGlobalSectionsOver (S.levelStructure n)).mapIso
      (((derivedTensorProductFunctor (schemeAt S.system S.X n).toRingedSpace.sheaf).obj
          ((DerivedCategory.singleFunctor _ 0).obj (S.F n))).mapIso
          (@asIso _ _ _ _ (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap
            (S.levelOpenImmersion U n).toLRSHom.toShHom (S.levelOpen U n).ι.toLRSHom.toShHom
            U.ι.toLRSHom.toShHom (S.closedImmersion n).toLRSHom.toShHom
            (S.levelOpen_square U n).symm (singleUnit U.toScheme.toRingedSpace))
            (S.isIso_derivedBaseChangeMap_levelOpen_unit U hU n)) ≪≫
        @asIso _ _ _ _ (projectionFormulaMapRight (S.levelOpen U n).ι.toLRSHom.toShHom
          ((DerivedCategory.singleFunctor _ 0).obj (S.F n))
          ((derivedPullback (S.levelOpenImmersion U n).toLRSHom.toShHom).obj
            (singleUnit U.toScheme.toRingedSpace)))
          (S.isIso_projectionFormulaMapRight_levelOpen U hU n)) ≪≫
    (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso (S.levelOpen U n).ι
      (S.levelStructure n) ((S.levelOpen U n).ι ≫ S.levelStructure n) (RingHom.id _)
      (Stacks.Cohomology.CountableSections.comp_eq_comp_specMap_id (S.levelStructure n)
        (S.levelOpen U n).ι)).app _ ≪≫
    (restrictScalarsIdDerivedIso (RingHom.id _) rfl).symm.app _ ≪≫
    (derivedGlobalSectionsOver ((S.levelOpen U n).ι ≫ S.levelStructure n)).mapIso
      (((derivedTensorProductFunctor (S.levelOpen U n).toScheme.toRingedSpace.sheaf).obj
          ((derivedPullback (S.levelOpen U n).ι.toLRSHom.toShHom).obj
            ((DerivedCategory.singleFunctor _ 0).obj (S.F n)))).mapIso
          (derivedPullbackUnitIso (S.levelOpenImmersion U n).toLRSHom.toShHom) ≪≫
        @asIso _ _ _ _ (tensorRightUnitorHom (S.levelOpen U n).toScheme.toRingedSpace _)
          (isIso_tensorRightUnitorHom _ _) ≪≫
        derivedPullbackSingleIsoOfFlat (S.levelOpen U n).ι (S.F n))

attribute [local instance 10000] HasDerivedCategory.standard in
/-- `levelSectionsIso` unfolded. -/
theorem levelSectionsIso_hom (U : S.X.left.Opens) (hU : IsCompact (U : Set S.X.left)) (n : ℕ) :
    (S.levelSectionsIso U hU n).hom =
      (derivedGlobalSectionsOver (S.levelStructure n)).map
          (((derivedTensorProductFunctor (schemeAt S.system S.X n).toRingedSpace.sheaf).obj
              ((DerivedCategory.singleFunctor _ 0).obj (S.F n))).map
              (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap
                (S.levelOpenImmersion U n).toLRSHom.toShHom (S.levelOpen U n).ι.toLRSHom.toShHom
                U.ι.toLRSHom.toShHom (S.closedImmersion n).toLRSHom.toShHom
                (S.levelOpen_square U n).symm (singleUnit U.toScheme.toRingedSpace)) ≫
            projectionFormulaMapRight (S.levelOpen U n).ι.toLRSHom.toShHom
              ((DerivedCategory.singleFunctor _ 0).obj (S.F n))
              ((derivedPullback (S.levelOpenImmersion U n).toLRSHom.toShHom).obj
                (singleUnit U.toScheme.toRingedSpace))) ≫
        (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso (S.levelOpen U n).ι
          (S.levelStructure n) ((S.levelOpen U n).ι ≫ S.levelStructure n) (RingHom.id _)
          (Stacks.Cohomology.CountableSections.comp_eq_comp_specMap_id (S.levelStructure n)
            (S.levelOpen U n).ι)).hom.app _ ≫
        (restrictScalarsIdDerivedIso (RingHom.id _) rfl).symm.hom.app _ ≫
        (derivedGlobalSectionsOver ((S.levelOpen U n).ι ≫ S.levelStructure n)).map
          (((derivedTensorProductFunctor (S.levelOpen U n).toScheme.toRingedSpace.sheaf).obj
              ((derivedPullback (S.levelOpen U n).ι.toLRSHom.toShHom).obj
                ((DerivedCategory.singleFunctor _ 0).obj (S.F n)))).map
              (derivedPullbackUnitIso (S.levelOpenImmersion U n).toLRSHom.toShHom).hom ≫
            tensorRightUnitorHom (S.levelOpen U n).toScheme.toRingedSpace _ ≫
            (derivedPullbackSingleIsoOfFlat (S.levelOpen U n).ι (S.F n)).hom) :=
  rfl

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The flat pushforward sections comparison at an object, unfolded. -/
theorem flatPushforwardSectionsComparison_app_eq (U : S.X.left.Opens)
    (M : DerivedCategory S.X.left.Modules) :
    (Stacks.Cohomology.CountableSections.flatPushforwardSectionsComparison S.X.hom U.ι).app M =
      (derivedGlobalSectionsOver S.X.hom).map
          ((Stacks.Cohomology.CountableSections.derivedTensorFlipObjIso S.X.left _).hom.app M) ≫
        (derivedGlobalSectionsOver S.X.hom).map
          (projectionFormulaMap U.ι.toLRSHom.toShHom (derivedUnitObject U) M) ≫
        (derivedGlobalSectionsOver S.X.hom).map ((derivedPushforward U.ι.toLRSHom.toShHom).map
          ((Stacks.Cohomology.CountableSections.derivedTensorUnitLeftIso U).hom.app
            ((derivedPullback U.ι.toLRSHom.toShHom).obj M))) ≫
        (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso U.ι S.X.hom (U.ι ≫ S.X.hom)
          (RingHom.id _) (Stacks.Cohomology.CountableSections.comp_eq_comp_specMap_id S.X.hom
            U.ι)).hom.app _ ≫
        (restrictScalarsIdDerivedIso (RingHom.id _) rfl).symm.hom.app _ ≫ 𝟙 _ :=
  rfl

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The commutativity constraint `derivedTensorFlipObjIso` is `tensorBraidingHom`. -/
theorem derivedTensorFlipObjIso_hom_app_eq (W : Scheme.{u})
    (M N : Stacks.DerivedTensor.RingedSite.DerivedModules W.toRingedSpace.sheaf) :
    (Stacks.Cohomology.CountableSections.derivedTensorFlipObjIso W N).hom.app M =
      tensorBraidingHom W.toRingedSpace M N := by
  let := Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal W.toRingedSpace.sheaf
  let := Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric W.toRingedSpace.sheaf
  simp only [Stacks.Cohomology.CountableSections.derivedTensorFlipObjIso,
    tensorBraidingHom, Stacks.SheafOfModules.DerivedMonoidal.canonicalBraidingHom,
    Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app, Iso.symm_hom,
    BraidedCategory.tensorLeftIsoTensorRight_inv_app]
  simp only [Functor.flip_obj_obj, MonoidalCategory.curriedTensor_obj_obj, eqToHom_refl,
    Category.comp_id, Category.id_comp]
  exact (SymmetricCategory.braiding_swap_eq_inv_braiding N M).symm

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The left unit constraint `derivedTensorUnitLeftIso` is `tensorLeftUnitorHom`. -/
theorem derivedTensorUnitLeftIso_hom_app_eq (W : Scheme.{u})
    (M : Stacks.DerivedTensor.RingedSite.DerivedModules W.toRingedSpace.sheaf) :
    (Stacks.Cohomology.CountableSections.derivedTensorUnitLeftIso W).hom.app M =
      tensorLeftUnitorHom W.toRingedSpace M := by
  simp only [Functor.id_obj, Stacks.Cohomology.CountableSections.derivedTensorUnitLeftIso,
    Iso.trans_hom, eqToIso.hom, NatTrans.comp_app, MonoidalCategory.curriedTensor_obj_obj,
    eqToHom_app, MonoidalCategory.leftUnitorNatIso_hom_app, tensorLeftUnitorHom,
    Stacks.SheafOfModules.DerivedMonoidal.canonicalLeftUnitorHom]
  exact (congrArg (· ≫ _) (eqToHom_refl _ _)).trans (Category.id_comp _)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The equation of the projection-formula square of [Stacks, Tag 0CTG].** -/
theorem levelSectionsSquare_eq (U : S.X.left.Opens) (hU : IsCompact (U : Set S.X.left))
    (n : ℕ) :
    S.levelRestrictionMap n ((derivedPushforward U.ι.toLRSHom.toShHom).obj (derivedUnitObject U)) ≫
        (ModuleCat.restrictScalars (S.limitProjection n)).mapDerivedCategory.map
          (S.levelSectionsIso U hU n).hom =
      (Stacks.Cohomology.CountableSections.flatPushforwardSectionsComparison S.X.hom U.ι ≫
          Functor.whiskerRight (derivedPullbackOpenRestrictIso U).hom
            (derivedGlobalSectionsOver (U.ι ≫ S.X.hom))).app
          (S.derivedPushforwardSystemOfModel.obj ⟨n⟩) ≫
        (S.sectionsOverPushforwardIso U n).hom := by
  have hsq := S.leraySquare_levelOpen U n
    ((DerivedCategory.singleFunctor _ 0).obj
      ((Scheme.Modules.pullback (S.levelOpen U n).ι).obj (S.F n)))
  have hpost := S.map_derivedPullbackOpenRestrictIso_hom_comp_sectionsOverPushforwardIso_hom U n
  have hsheaf := sheaf_square_ringedSpace (S.levelOpenImmersion U n).toLRSHom.toShHom
    (S.levelOpen U n).ι.toLRSHom.toShHom U.ι.toLRSHom.toShHom
    (S.closedImmersion n).toLRSHom.toShHom (S.levelOpen_square U n).symm (S.levelOpen_square U n)
    (G := (DerivedCategory.singleFunctor
      (SheafOfModules (structureSheafRing (schemeAt S.system S.X n).toSheafedSpace)) 0).obj (S.F n))
    ((@closedImmersionDerivedPushforwardSingleIso _ _ (S.closedImmersion n)
      (S.closedSchemeProjection n)).hom.app (S.F n))
    (derivedPullbackSingleIsoOfFlat (S.levelOpen U n).ι (S.F n)).hom _ rfl
  have hA := assembly'
    (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso (S.closedImmersion n) S.X.hom
      (S.levelStructure n) (S.limitProjection n) (S.closedImmersion_comp_hom n))
    (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso U.ι S.X.hom (U.ι ≫ S.X.hom)
      (RingHom.id _) (Stacks.Cohomology.CountableSections.comp_eq_comp_specMap_id S.X.hom U.ι))
    (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso (S.levelOpenImmersion U n)
      (U.ι ≫ S.X.hom) ((S.levelOpen U n).ι ≫ S.levelStructure n) (S.limitProjection n)
      (S.levelOpenImmersion_comp U n))
    (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso (S.levelOpen U n).ι
      (S.levelStructure n) ((S.levelOpen U n).ι ≫ S.levelStructure n) (RingHom.id _)
      (Stacks.Cohomology.CountableSections.comp_eq_comp_specMap_id (S.levelStructure n)
        (S.levelOpen U n).ι))
    (restrictScalarsIdDerivedIso (RingHom.id _) rfl).symm
    (restrictScalarsIdDerivedIso (RingHom.id _) rfl).symm
    _ _ _ _ _ _ _ _ _ _ _ hsheaf hsq hpost _ (derivedTensorFlipObjIso_hom_app_eq S.X.left _ _)
    _ (derivedTensorUnitLeftIso_hom_app_eq U _)
  refine Eq.trans ?_ (hA.trans ?_)
  · rfl
  · rfl

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The projection-formula square of [Stacks, Tag 0CTG]**, for every quasi-compact open
`U ⊆ X` and every level `n`: the flat pushforward sections comparison
`RΓ(X, - ⊗^𝐋 Rι_* 𝒪_U) ⟶ RΓ(U, Lι^* -)`, read through `Lι^* = (-)|_U`, is invertible on
`D_QCoh(𝒪_X)` ([Stacks, Tag 08EU]), and at `iₙ,* ℱₙ` it is carried by the level identification of
[Stacks, Tag 0CTE] (1) and the isomorphism `levelSectionsIso` to the Leray identification
`RΓ(U, iₙ,* ℱₙ) = RΓ(Uₙ, ℱₙ)`. The square is `levelSectionsSquare_eq`. At
`HasDerivedCategory.standard`, scoped to this declaration. -/
theorem projectionFormulaSquare (U : S.X.left.Opens) (hU : IsCompact (U : Set S.X.left))
    (n : ℕ) : S.ProjectionFormulaSquare U n := by
  have : CompactSpace U := isCompact_iff_compactSpace.mp hU
  have := S.separated
  refine ⟨Stacks.Cohomology.CountableSections.flatPushforwardSectionsComparison S.X.hom U.ι ≫
      Functor.whiskerRight (derivedPullbackOpenRestrictIso U).hom
        (derivedGlobalSectionsOver (U.ι ≫ S.X.hom)), fun M hM => ?_, S.levelSectionsIso U hU n,
    S.levelSectionsSquare_eq U hU n⟩
  have h := Stacks.Cohomology.CountableSections.isIso_flatPushforwardSectionsComparison_app
    S.X.hom U.ι M hM
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h
    (@Functor.map_isIso _ _ _ _ _ _ _ _ ((derivedPullbackOpenRestrictIso U).app M).isIso_hom)

end AlgebraicGeometry.GrothendieckExistence.ExistenceSituation

end
