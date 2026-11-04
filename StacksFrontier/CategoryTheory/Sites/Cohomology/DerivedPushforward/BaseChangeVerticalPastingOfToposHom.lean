module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangePastingOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.CompositionOfToposHomUnconditional
public import StacksCore.Tactic.StacksAttribute

/-!
# Vertical pasting of derived base change maps along morphisms of ringed topoi

Consider a diagram of ringed topoi

```
                   k
  (Sh(B'), 𝒪_B') ———→ (Sh(B), 𝒪_B)
         │ f'                │ f
         v                   v
  (Sh(C'), 𝒪_C') ———→ (Sh(C), 𝒪_C)
         │ g'        l       │ g
         v                   v
  (Sh(D'), 𝒪_D') ———→ (Sh(D), 𝒪_D)
                   m
```

whose two squares commute up to given 2-isomorphisms `st : l ∘ f' ≅ f ∘ k` and
`sb : m ∘ g' ≅ g ∘ l` (Stacks 04IC), the outer rectangle commuting up to their pasting
`AlgebraicGeometry.RingedToposHom.TwoIso.pasteVertical st sb`.  Stacks 0E46 says that the base
change maps of Remark 07A7 for the two squares compose to the base change map of the rectangle:
the composite

`Lm^* R(g ∘ f)_* = Lm^* Rg_* Rf_* ⟶ Rg'_* Ll^* Rf_* ⟶ Rg'_* Rf'_* Lk^* = R(g' ∘ f')_* Lk^*`

is the base change map of the rectangle.  This file proves it for arbitrary morphisms of ringed
topoi in the sense of Stacks 01D3, part (2), at free universes.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.TwoIso.pasteVertical`: the 2-isomorphism of the outer
  rectangle of two vertically composable 2-commutative squares.

## Main results

* `baseChangeMap_vertical`: the formal vertical pasting law for base change maps, on abstract
  functors and adjunctions.
* `derivedBaseChangeMapOfTwoIso_vertical`: **Stacks 0E46**.

## Implementation notes

The base change map of a square is the transpose, under the derived adjunction of the left
vertical arrow, of the comparison of the two iterated derived pullbacks around the square followed
by the derived counit of the right vertical arrow.  Transposing the composite through the derived
adjunctions of `g'` and `f'` and using the description of the derived adjunction of a composite
(`Stacks.Cohomology.DerivedPushforwardCompositionOfToposHom.derivedAdjunction_comp_homEquiv`)
reduces the claim to the identity expressing the comparison of the rectangle as the vertical
composite of the comparisons of the two squares.  That identity is the inverse of the one for the
horizontal pasting of the transposed diagram, `squareComparison_paste`, whose five inputs are the
coherences of Stacks 0D6D proved in
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/TwoIsoCoherenceOfToposHom.lean`.

As in the horizontal case, the assembly `derivedBaseChangeMap_pasteVertical_of_iso` is stated
over the derived categories of the six ringed topoi with every functor and adjunction a variable,
so that its instance at the derived functors is checked by the kernel syntactically.

## References

* [Stacks Project, Tag 0E46](https://stacks.math.columbia.edu/tag/0E46)
* [Stacks Project, Tag 07A7](https://stacks.math.columbia.edu/tag/07A7)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 0D6E](https://stacks.math.columbia.edu/tag/0D6E)
* [Stacks Project, Tag 04IC](https://stacks.math.columbia.edu/tag/04IC)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPushforward
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom
open Stacks.Cohomology.DerivedPushforwardCompositionOfToposHom

namespace AlgebraicGeometry.RingedToposHom.TwoIso

universe vB uB wB vB' uB' wB' vC uC wC vC' uC' wC' vD uD wD vD' uD' wD'

variable {B : RingedTopos.{vB, uB, wB}} {B' : RingedTopos.{vB', uB', wB'}}
  {C : RingedTopos.{vC, uC, wC}} {C' : RingedTopos.{vC', uC', wC'}}
  {D : RingedTopos.{vD, uD, wD}} {D' : RingedTopos.{vD', uD', wD'}}
  [B.J.HasSheafCompose (forget RingCat.{wB})] [B'.J.HasSheafCompose (forget RingCat.{wB'})]
  [C.J.HasSheafCompose (forget RingCat.{wC})] [C'.J.HasSheafCompose (forget RingCat.{wC'})]
  [D.J.HasSheafCompose (forget RingCat.{wD})] [D'.J.HasSheafCompose (forget RingCat.{wD'})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{wB} RingCat.{wB})]
  [B'.J.HasSheafCompose (forget₂ CommRingCat.{wB'} RingCat.{wB'})]
  [C.J.HasSheafCompose (forget₂ CommRingCat.{wC} RingCat.{wC})]
  [C'.J.HasSheafCompose (forget₂ CommRingCat.{wC'} RingCat.{wC'})]
  [D.J.HasSheafCompose (forget₂ CommRingCat.{wD} RingCat.{wD})]
  [D'.J.HasSheafCompose (forget₂ CommRingCat.{wD'} RingCat.{wD'})]

/-- **Vertical pasting of two 2-commutative squares of ringed topoi.**  For squares

```
        k
  B' ———→ B
  │ f'    │ f
  v   l   v
  C' ———→ C
  │ g'    │ g
  v       v
  D' ———→ D
        m
```

commuting up to `st : l ∘ f' ≅ f ∘ k` and `sb : m ∘ g' ≅ g ∘ l` (Stacks 04IC), the
2-isomorphism `m ∘ (g' ∘ f') ≅ (g ∘ f) ∘ k` exhibiting the outer rectangle as commutative.  It
is the inverse of the horizontal pasting of the transposed diagram, which unfolds to: reassociate,
apply `sb` in front of `f'`, reassociate, apply `st` behind `g`, reassociate. -/
noncomputable def pasteVertical {f : RingedToposHom B C} {g : RingedToposHom C D}
    {f' : RingedToposHom B' C'} {g' : RingedToposHom C' D'} {k : RingedToposHom B' B}
    {l : RingedToposHom C' C} {m : RingedToposHom D' D}
    (st : TwoIso (l.comp f') (f.comp k)) (sb : TwoIso (m.comp g') (g.comp l)) :
    TwoIso (m.comp (g'.comp f')) ((g.comp f).comp k) :=
  (pasteHorizontal sb.symm st.symm).symm

end AlgebraicGeometry.RingedToposHom.TwoIso

namespace Stacks.Cohomology.DerivedBaseChangeOfToposHom

universe vB uB wB vB' uB' wB' vC uC wC vC' uC' wC' vD uD wD vD' uD' wD'

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

noncomputable section

/-- **The vertical pasting law for base change maps, on abstract functors.**  Given adjunctions
`Lf ⊣ Rf`, `Lg ⊣ Rg`, `Lgf ⊣ Rgf` and their primed counterparts, with `Lgf` identified with
`Lg ⋙ Lf` by `cH` and `Rgf` with `Rf ⋙ Rg` by `pG` compatibly with transposition (`hpG`), and
likewise for the primed ones, and comparisons `σt`, `σb`, `σr` of the iterated pullbacks around
the top square, the bottom square and the rectangle such that `σr` is the vertical composite of
`σb` and `σt` (`hσ`), the base change maps given by their adjoint descriptions compose. -/
theorem baseChangeMap_vertical {DB DB' DC DC' DD DD' : Type*}
    [Category* DB] [Category* DB'] [Category* DC] [Category* DC'] [Category* DD] [Category* DD']
    {Lf : DC ⥤ DB} {Lg : DD ⥤ DC} {Lgf : DD ⥤ DB} {Lf' : DC' ⥤ DB'} {Lg' : DD' ⥤ DC'}
    {Lgf' : DD' ⥤ DB'} {Lk : DB ⥤ DB'} {Ll : DC ⥤ DC'} {Lm : DD ⥤ DD'}
    {Rf : DB ⥤ DC} {Rg : DC ⥤ DD} {Rgf : DB ⥤ DD} {Rf' : DB' ⥤ DC'} {Rg' : DC' ⥤ DD'}
    {Rgf' : DB' ⥤ DD'}
    (adjf : Lf ⊣ Rf) (adjg : Lg ⊣ Rg) (adjgf : Lgf ⊣ Rgf)
    (adjf' : Lf' ⊣ Rf') (adjg' : Lg' ⊣ Rg') (adjgf' : Lgf' ⊣ Rgf')
    (cH : Lg ⋙ Lf ≅ Lgf) (cG : Lg' ⋙ Lf' ≅ Lgf') (pG : Rf ⋙ Rg ≅ Rgf) (pG' : Rf' ⋙ Rg' ≅ Rgf')
    (hpG : ∀ M K (φ : Lgf.obj M ⟶ K),
      adjg.homEquiv _ _ (adjf.homEquiv _ _ (cH.hom.app M ≫ φ)) ≫ pG.hom.app K =
        adjgf.homEquiv M K φ)
    (hpG' : ∀ M K (φ : Lgf'.obj M ⟶ K),
      adjg'.homEquiv _ _ (adjf'.homEquiv _ _ (cG.hom.app M ≫ φ)) ≫ pG'.hom.app K =
        adjgf'.homEquiv M K φ)
    (σt : Ll ⋙ Lf' ⟶ Lf ⋙ Lk) (σb : Lm ⋙ Lg' ⟶ Lg ⋙ Ll)
    (σr : ∀ M, Lgf'.obj (Lm.obj M) ⟶ Lk.obj (Lgf.obj M))
    (hσ : ∀ M, σr M = cG.inv.app (Lm.obj M) ≫ Lf'.map (σb.app M) ≫ σt.app (Lg.obj M) ≫
      Lk.map (cH.hom.app M))
    (K : DB) (bct : Ll.obj (Rf.obj K) ⟶ Rf'.obj (Lk.obj K))
    (bcb : Lm.obj (Rg.obj (Rf.obj K)) ⟶ Rg'.obj (Ll.obj (Rf.obj K)))
    (bcr : Lm.obj (Rgf.obj K) ⟶ Rgf'.obj (Lk.obj K))
    (hbct : (adjf'.homEquiv _ _).symm bct = σt.app (Rf.obj K) ≫ Lk.map (adjf.counit.app K))
    (hbcb : (adjg'.homEquiv _ _).symm bcb =
      σb.app (Rg.obj (Rf.obj K)) ≫ Ll.map (adjg.counit.app (Rf.obj K)))
    (hbcr : (adjgf'.homEquiv _ _).symm bcr = σr (Rgf.obj K) ≫ Lk.map (adjgf.counit.app K)) :
    Lm.map (pG.inv.app K) ≫ bcb ≫ Rg'.map bct ≫ pG'.hom.app (Lk.obj K) = bcr := by
  -- the counit of `Lgf ⊣ Rgf`, through the counits of `Lg ⊣ Rg` and `Lf ⊣ Rf`
  have h₃ : adjg.homEquiv (Rgf.obj K) (Rf.obj K) (adjf.homEquiv (Lg.obj (Rgf.obj K)) K
      (cH.hom.app (Rgf.obj K) ≫ adjgf.counit.app K)) = pG.inv.app K := by
    rw [← cancel_mono (pG.hom.app K), Iso.inv_hom_id_app, hpG, Adjunction.homEquiv_unit]
    exact adjgf.right_triangle_components K
  have hε : Lk.map (cH.hom.app (Rgf.obj K)) ≫ Lk.map (adjgf.counit.app K) =
      Lk.map (Lf.map (Lg.map (pG.inv.app K))) ≫
        Lk.map (Lf.map (adjg.counit.app (Rf.obj K))) ≫ Lk.map (adjf.counit.app K) := by
    have h := congrArg (fun x => (adjf.homEquiv (Lg.obj (Rgf.obj K)) K).symm
      ((adjg.homEquiv (Rgf.obj K) (Rf.obj K)).symm x)) h₃
    simp only [Equiv.symm_apply_apply] at h
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit] at h
    rw [← Functor.map_comp, h]
    simp only [Functor.map_comp, Category.assoc]
  have nt : ∀ {X Y : DC} (u : X ⟶ Y),
      σt.app X ≫ Lk.map (Lf.map u) = Lf'.map (Ll.map u) ≫ σt.app Y := fun u => by
    simpa only [Functor.comp_map] using (σt.naturality u).symm
  have nb : Lf'.map (Lg'.map (Lm.map (pG.inv.app K))) ≫ Lf'.map (σb.app (Rg.obj (Rf.obj K))) =
      Lf'.map (σb.app (Rgf.obj K)) ≫ Lf'.map (Ll.map (Lg.map (pG.inv.app K))) := by
    simp only [← Functor.map_comp]
    exact congrArg Lf'.map (σb.naturality (pG.inv.app K))
  have h₁ : Lf'.map (Lg'.map (Rg'.map bct)) ≫ Lf'.map (adjg'.counit.app (Rf'.obj (Lk.obj K))) =
      Lf'.map (adjg'.counit.app (Ll.obj (Rf.obj K))) ≫ Lf'.map bct := by
    simp only [← Functor.map_comp, adjg'.counit_naturality bct]
  have hbct' : Lf'.map bct ≫ adjf'.counit.app (Lk.obj K) =
      σt.app (Rf.obj K) ≫ Lk.map (adjf.counit.app K) := hbct
  have hbcb' : Lf'.map (Lg'.map bcb) ≫ Lf'.map (adjg'.counit.app (Ll.obj (Rf.obj K))) =
      Lf'.map (σb.app (Rg.obj (Rf.obj K))) ≫ Lf'.map (Ll.map (adjg.counit.app (Rf.obj K))) := by
    simp only [← Functor.map_comp]
    exact congrArg Lf'.map hbcb
  have key : (adjf'.homEquiv (Lg'.obj (Lm.obj (Rgf.obj K))) (Lk.obj K)).symm
      ((adjg'.homEquiv (Lm.obj (Rgf.obj K)) (Rf'.obj (Lk.obj K))).symm
        (Lm.map (pG.inv.app K) ≫ bcb ≫ Rg'.map bct)) =
      cG.hom.app (Lm.obj (Rgf.obj K)) ≫ σr (Rgf.obj K) ≫ Lk.map (adjgf.counit.app K) := by
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, hσ]
    simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [reassoc_of% h₁, hbct',
      reassoc_of% hbcb', reassoc_of% nb, hε,
      reassoc_of% (nt (Lg.map (pG.inv.app K))),
      reassoc_of% (nt (X := Lg.obj (Rg.obj (Rf.obj K))) (Y := Rf.obj K)
        (adjg.counit.app (Rf.obj K)))]
  calc Lm.map (pG.inv.app K) ≫ bcb ≫ Rg'.map bct ≫ pG'.hom.app (Lk.obj K)
      = (Lm.map (pG.inv.app K) ≫ bcb ≫ Rg'.map bct) ≫ pG'.hom.app (Lk.obj K) := by
        simp only [Category.assoc]
    _ = adjg'.homEquiv (Lm.obj (Rgf.obj K)) (Rf'.obj (Lk.obj K))
          (adjf'.homEquiv (Lg'.obj (Lm.obj (Rgf.obj K))) (Lk.obj K)
            (cG.hom.app (Lm.obj (Rgf.obj K)) ≫ (σr (Rgf.obj K) ≫ Lk.map (adjgf.counit.app K)))) ≫
          pG'.hom.app (Lk.obj K) := by
        rw [← key, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    _ = adjgf'.homEquiv (Lm.obj (Rgf.obj K)) (Lk.obj K)
          (σr (Rgf.obj K) ≫ Lk.map (adjgf.counit.app K)) := hpG' _ _ _
    _ = bcr := by rw [← hbcr, Equiv.apply_symm_apply]

section Paste

variable {B : RingedTopos.{vB, uB, wB}} {B' : RingedTopos.{vB', uB', wB'}}
  {C : RingedTopos.{vC, uC, wC}} {C' : RingedTopos.{vC', uC', wC'}}
  {D : RingedTopos.{vD, uD, wD}} {D' : RingedTopos.{vD', uD', wD'}}
  [B.J.HasSheafCompose (forget RingCat.{wB})]
  [B'.J.HasSheafCompose (forget RingCat.{wB'})]
  [C.J.HasSheafCompose (forget RingCat.{wC})]
  [C'.J.HasSheafCompose (forget RingCat.{wC'})]
  [D.J.HasSheafCompose (forget RingCat.{wD})]
  [D'.J.HasSheafCompose (forget RingCat.{wD'})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{wB} RingCat.{wB})]
  [B'.J.HasSheafCompose (forget₂ CommRingCat.{wB'} RingCat.{wB'})]
  [C.J.HasSheafCompose (forget₂ CommRingCat.{wC} RingCat.{wC})]
  [C'.J.HasSheafCompose (forget₂ CommRingCat.{wC'} RingCat.{wC'})]
  [D.J.HasSheafCompose (forget₂ CommRingCat.{wD} RingCat.{wD})]
  [D'.J.HasSheafCompose (forget₂ CommRingCat.{wD'} RingCat.{wD'})]
  [B.J.HasSheafCompose (forget AddCommGrpCat.{wB})]
  [B'.J.HasSheafCompose (forget AddCommGrpCat.{wB'})]
  [C.J.HasSheafCompose (forget AddCommGrpCat.{wC})]
  [C'.J.HasSheafCompose (forget AddCommGrpCat.{wC'})]
  [D.J.HasSheafCompose (forget AddCommGrpCat.{wD})]
  [D'.J.HasSheafCompose (forget AddCommGrpCat.{wD'})]
  [HasSheafify B.J AddCommGrpCat.{wB}] [B.J.WEqualsLocallyBijective AddCommGrpCat.{wB}]
  [HasSheafify B'.J AddCommGrpCat.{wB'}] [B'.J.WEqualsLocallyBijective AddCommGrpCat.{wB'}]
  [HasSheafify C.J AddCommGrpCat.{wC}] [C.J.WEqualsLocallyBijective AddCommGrpCat.{wC}]
  [HasSheafify C'.J AddCommGrpCat.{wC'}] [C'.J.WEqualsLocallyBijective AddCommGrpCat.{wC'}]
  [HasSheafify D.J AddCommGrpCat.{wD}] [D.J.WEqualsLocallyBijective AddCommGrpCat.{wD}]
  [HasSheafify D'.J AddCommGrpCat.{wD'}] [D'.J.WEqualsLocallyBijective AddCommGrpCat.{wD'}]
  [HasSheafify B.J (Type wB)] [HasSheafify B'.J (Type wB')] [HasSheafify C.J (Type wC)]
  [HasSheafify C'.J (Type wC')] [HasSheafify D.J (Type wD)] [HasSheafify D'.J (Type wD')]

omit [B.J.HasSheafCompose (forget RingCat.{wB})] [B'.J.HasSheafCompose (forget RingCat.{wB'})]
  [C.J.HasSheafCompose (forget RingCat.{wC})] [C'.J.HasSheafCompose (forget RingCat.{wC'})]
  [D.J.HasSheafCompose (forget RingCat.{wD})] [D'.J.HasSheafCompose (forget RingCat.{wD'})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{wB} RingCat.{wB})]
  [B'.J.HasSheafCompose (forget₂ CommRingCat.{wB'} RingCat.{wB'})]
  [C.J.HasSheafCompose (forget₂ CommRingCat.{wC} RingCat.{wC})]
  [C'.J.HasSheafCompose (forget₂ CommRingCat.{wC'} RingCat.{wC'})]
  [D.J.HasSheafCompose (forget₂ CommRingCat.{wD} RingCat.{wD})]
  [D'.J.HasSheafCompose (forget₂ CommRingCat.{wD'} RingCat.{wD'})]
  [B.J.HasSheafCompose (forget AddCommGrpCat.{wB})]
  [B'.J.HasSheafCompose (forget AddCommGrpCat.{wB'})]
  [C.J.HasSheafCompose (forget AddCommGrpCat.{wC})]
  [C'.J.HasSheafCompose (forget AddCommGrpCat.{wC'})]
  [D.J.HasSheafCompose (forget AddCommGrpCat.{wD})]
  [D'.J.HasSheafCompose (forget AddCommGrpCat.{wD'})]
  [HasSheafify B.J (Type wB)] [HasSheafify B'.J (Type wB')] [HasSheafify C.J (Type wC)]
  [HasSheafify C'.J (Type wC')] [HasSheafify D.J (Type wD)] [HasSheafify D'.J (Type wD')] in
/-- **The vertical pasting law for base change maps, over the derived categories of six ringed
topoi.**  With every functor and adjunction a variable: if the comparisons of iterated pullbacks
satisfy the five identities of `squareComparison_paste` for the transposed diagram, and the
composition isomorphisms `pG`, `pG'` of the right adjoints are compatible with transposition,
then the base change maps `bct`, `bcb`, `bcr` of the two squares and of the rectangle, each given
by its adjoint description, compose. -/
theorem derivedBaseChangeMap_pasteVertical_of_iso
    {Lf : DerivedCategory (SheafOfModules.{wC} (SheafOfModules.Tensor.ringSheaf C.O)) ⥤
      DerivedCategory (SheafOfModules.{wB} (SheafOfModules.Tensor.ringSheaf B.O))}
    {Lg : DerivedCategory (SheafOfModules.{wD} (SheafOfModules.Tensor.ringSheaf D.O)) ⥤
      DerivedCategory (SheafOfModules.{wC} (SheafOfModules.Tensor.ringSheaf C.O))}
    {Lgf : DerivedCategory (SheafOfModules.{wD} (SheafOfModules.Tensor.ringSheaf D.O)) ⥤
      DerivedCategory (SheafOfModules.{wB} (SheafOfModules.Tensor.ringSheaf B.O))}
    {Lf' : DerivedCategory (SheafOfModules.{wC'} (SheafOfModules.Tensor.ringSheaf C'.O)) ⥤
      DerivedCategory (SheafOfModules.{wB'} (SheafOfModules.Tensor.ringSheaf B'.O))}
    {Lg' : DerivedCategory (SheafOfModules.{wD'} (SheafOfModules.Tensor.ringSheaf D'.O)) ⥤
      DerivedCategory (SheafOfModules.{wC'} (SheafOfModules.Tensor.ringSheaf C'.O))}
    {Lgf' : DerivedCategory (SheafOfModules.{wD'} (SheafOfModules.Tensor.ringSheaf D'.O)) ⥤
      DerivedCategory (SheafOfModules.{wB'} (SheafOfModules.Tensor.ringSheaf B'.O))}
    {Lk : DerivedCategory (SheafOfModules.{wB} (SheafOfModules.Tensor.ringSheaf B.O)) ⥤
      DerivedCategory (SheafOfModules.{wB'} (SheafOfModules.Tensor.ringSheaf B'.O))}
    {Ll : DerivedCategory (SheafOfModules.{wC} (SheafOfModules.Tensor.ringSheaf C.O)) ⥤
      DerivedCategory (SheafOfModules.{wC'} (SheafOfModules.Tensor.ringSheaf C'.O))}
    {Lm : DerivedCategory (SheafOfModules.{wD} (SheafOfModules.Tensor.ringSheaf D.O)) ⥤
      DerivedCategory (SheafOfModules.{wD'} (SheafOfModules.Tensor.ringSheaf D'.O))}
    {Rf : DerivedCategory (SheafOfModules.{wB} (SheafOfModules.Tensor.ringSheaf B.O)) ⥤
      DerivedCategory (SheafOfModules.{wC} (SheafOfModules.Tensor.ringSheaf C.O))}
    {Rg : DerivedCategory (SheafOfModules.{wC} (SheafOfModules.Tensor.ringSheaf C.O)) ⥤
      DerivedCategory (SheafOfModules.{wD} (SheafOfModules.Tensor.ringSheaf D.O))}
    {Rgf : DerivedCategory (SheafOfModules.{wB} (SheafOfModules.Tensor.ringSheaf B.O)) ⥤
      DerivedCategory (SheafOfModules.{wD} (SheafOfModules.Tensor.ringSheaf D.O))}
    {Rf' : DerivedCategory (SheafOfModules.{wB'} (SheafOfModules.Tensor.ringSheaf B'.O)) ⥤
      DerivedCategory (SheafOfModules.{wC'} (SheafOfModules.Tensor.ringSheaf C'.O))}
    {Rg' : DerivedCategory (SheafOfModules.{wC'} (SheafOfModules.Tensor.ringSheaf C'.O)) ⥤
      DerivedCategory (SheafOfModules.{wD'} (SheafOfModules.Tensor.ringSheaf D'.O))}
    {Rgf' : DerivedCategory (SheafOfModules.{wB'} (SheafOfModules.Tensor.ringSheaf B'.O)) ⥤
      DerivedCategory (SheafOfModules.{wD'} (SheafOfModules.Tensor.ringSheaf D'.O))}
    (adjf : Lf ⊣ Rf) (adjg : Lg ⊣ Rg) (adjgf : Lgf ⊣ Rgf)
    (adjf' : Lf' ⊣ Rf') (adjg' : Lg' ⊣ Rg') (adjgf' : Lgf' ⊣ Rgf')
    (pG : Rf ⋙ Rg ≅ Rgf) (pG' : Rf' ⋙ Rg' ≅ Rgf')
    {A₁ B₁ : DerivedCategory (SheafOfModules.{wC} (SheafOfModules.Tensor.ringSheaf C.O)) ⥤
      DerivedCategory (SheafOfModules.{wB'} (SheafOfModules.Tensor.ringSheaf B'.O))}
    {A₂ B₂ : DerivedCategory (SheafOfModules.{wD} (SheafOfModules.Tensor.ringSheaf D.O)) ⥤
      DerivedCategory (SheafOfModules.{wC'} (SheafOfModules.Tensor.ringSheaf C'.O))}
    {R₀ R₁ R₂ R₃ R₄ R₅ :
      DerivedCategory (SheafOfModules.{wD} (SheafOfModules.Tensor.ringSheaf D.O)) ⥤
      DerivedCategory (SheafOfModules.{wB'} (SheafOfModules.Tensor.ringSheaf B'.O))}
    (cH : Lg ⋙ Lf ≅ Lgf) (cG : Lg' ⋙ Lf' ≅ Lgf')
    (c₁ : Lf ⋙ Lk ≅ A₁) (U₁ : A₁ ≅ B₁) (d₁ : Ll ⋙ Lf' ≅ B₁)
    (c₂ : Lg ⋙ Ll ≅ A₂) (U₂ : A₂ ≅ B₂) (d₂ : Lm ⋙ Lg' ≅ B₂)
    (c₀ : Lgf ⋙ Lk ≅ R₀) (U₀ : R₀ ≅ R₅) (d₀ : Lm ⋙ Lgf' ≅ R₅)
    (e₁ : Lg ⋙ A₁ ≅ R₁) (e₂ : Lg ⋙ B₁ ≅ R₂) (e₃ : A₂ ⋙ Lf' ≅ R₃) (e₄ : B₂ ⋙ Lf' ≅ R₄)
    (a₁ : R₁ ≅ R₀) (w₁ : R₁ ≅ R₂) (a₂ : R₂ ≅ R₃) (w₂ : R₃ ≅ R₄) (a₃ : R₅ ≅ R₄)
    (hA₁ : ∀ N, c₁.hom.app (Lg.obj N) ≫ e₁.hom.app N ≫ a₁.hom.app N =
      Lk.map (cH.hom.app N) ≫ c₀.hom.app N)
    (hW : ∀ N, e₁.hom.app N ≫ w₁.hom.app N = U₁.hom.app (Lg.obj N) ≫ e₂.hom.app N)
    (hA₂ : ∀ N, d₁.hom.app (Lg.obj N) ≫ e₂.hom.app N ≫ a₂.hom.app N =
      Lf'.map (c₂.hom.app N) ≫ e₃.hom.app N)
    (hL : ∀ N, e₃.hom.app N ≫ w₂.hom.app N = Lf'.map (U₂.hom.app N) ≫ e₄.hom.app N)
    (hA₃ : ∀ N, cG.hom.app (Lm.obj N) ≫ d₀.hom.app N ≫ a₃.hom.app N =
      Lf'.map (d₂.hom.app N) ≫ e₄.hom.app N)
    (hT : ∀ N, U₀.hom.app N =
      a₁.inv.app N ≫ w₁.hom.app N ≫ a₂.hom.app N ≫ w₂.hom.app N ≫ a₃.inv.app N)
    (hpG : ∀ M K (φ : Lgf.obj M ⟶ K),
      adjg.homEquiv _ _ (adjf.homEquiv _ _ (cH.hom.app M ≫ φ)) ≫ pG.hom.app K =
        adjgf.homEquiv M K φ)
    (hpG' : ∀ M K (φ : Lgf'.obj M ⟶ K),
      adjg'.homEquiv _ _ (adjf'.homEquiv _ _ (cG.hom.app M ≫ φ)) ≫ pG'.hom.app K =
        adjgf'.homEquiv M K φ)
    (K : DerivedCategory (SheafOfModules.{wB} (SheafOfModules.Tensor.ringSheaf B.O)))
    (bct : Ll.obj (Rf.obj K) ⟶ Rf'.obj (Lk.obj K))
    (bcb : Lm.obj (Rg.obj (Rf.obj K)) ⟶ Rg'.obj (Ll.obj (Rf.obj K)))
    (bcr : Lm.obj (Rgf.obj K) ⟶ Rgf'.obj (Lk.obj K))
    (hbct : (adjf'.homEquiv _ _).symm bct =
      d₁.hom.app (Rf.obj K) ≫ (c₁ ≪≫ U₁).inv.app (Rf.obj K) ≫ Lk.map (adjf.counit.app K))
    (hbcb : (adjg'.homEquiv _ _).symm bcb =
      d₂.hom.app (Rg.obj (Rf.obj K)) ≫ (c₂ ≪≫ U₂).inv.app (Rg.obj (Rf.obj K)) ≫
        Ll.map (adjg.counit.app (Rf.obj K)))
    (hbcr : (adjgf'.homEquiv _ _).symm bcr =
      d₀.hom.app (Rgf.obj K) ≫ (c₀ ≪≫ U₀).inv.app (Rgf.obj K) ≫
        Lk.map (adjgf.counit.app K)) :
    Lm.map (pG.inv.app K) ≫ bcb ≫ Rg'.map bct ≫ pG'.hom.app (Lk.obj K) = bcr := by
  have hσ : ∀ M, d₀.hom.app M ≫ (c₀ ≪≫ U₀).inv.app M =
      cG.inv.app (Lm.obj M) ≫ Lf'.map ((d₂.hom ≫ (c₂ ≪≫ U₂).inv).app M) ≫
        (d₁.hom ≫ (c₁ ≪≫ U₁).inv).app (Lg.obj M) ≫ Lk.map (cH.hom.app M) := fun M => by
    have H := squareComparison_paste cH cG c₁ U₁.symm d₁ c₂ U₂.symm d₂ c₀ U₀.symm d₀
      e₁ e₂ e₃ e₄ a₁ w₁ a₂ w₂ a₃ hA₁ hW hA₂ hL hA₃ hT M
    simp only [Iso.trans_inv, NatTrans.comp_app, Category.assoc]
    refine (Stacks.Cohomology.DerivedBaseChangePasting.comp₄_inv
      (Lk.map (cH.inv.app M)) (Lk.map (cH.hom.app M))
      (Lf'.map (c₂.hom.app M ≫ U₂.hom.app M ≫ d₂.inv.app M))
      (Lf'.map (d₂.hom.app M ≫ U₂.inv.app M ≫ c₂.inv.app M))
      (a' := d₁.hom.app (Lg.obj M) ≫ U₁.inv.app (Lg.obj M) ≫ c₁.inv.app (Lg.obj M))
      (b' := cG.inv.app (Lm.obj M))
      (c' := d₀.hom.app M ≫ U₀.inv.app M ≫ c₀.inv.app M)
      ?_ ?_ ?_ ?_ ?_ H).symm.trans ?_
    · rw [← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
    · simp
    · rw [← Functor.map_comp]
      simp
    · exact Iso.inv_hom_id_app cG (Lm.obj M)
    · simp
    · simp only [Category.assoc]
  exact baseChangeMap_vertical adjf adjg adjgf adjf' adjg' adjgf' cH cG pG pG' hpG hpG'
    (d₁.hom ≫ (c₁ ≪≫ U₁).inv) (d₂.hom ≫ (c₂ ≪≫ U₂).inv)
    (fun M => d₀.hom.app M ≫ (c₀ ≪≫ U₀).inv.app M) hσ K bct bcb bcr
    (by rw [hbct, NatTrans.comp_app, Category.assoc])
    (by rw [hbcb, NatTrans.comp_app, Category.assoc])
    (by rw [hbcr, Category.assoc])

variable (f : RingedToposHom B C) (g : RingedToposHom C D) (f' : RingedToposHom B' C')
  (g' : RingedToposHom C' D') (k : RingedToposHom B' B) (l : RingedToposHom C' C)
  (m : RingedToposHom D' D)

omit [B.J.HasSheafCompose (forget AddCommGrpCat.{wB})]
  [C.J.HasSheafCompose (forget AddCommGrpCat.{wC})]
  [C'.J.HasSheafCompose (forget AddCommGrpCat.{wC'})]
  [D'.J.HasSheafCompose (forget AddCommGrpCat.{wD'})]
  [HasSheafify B.J AddCommGrpCat.{wB}] [B.J.WEqualsLocallyBijective AddCommGrpCat.{wB}]
  [HasSheafify C.J AddCommGrpCat.{wC}] [C.J.WEqualsLocallyBijective AddCommGrpCat.{wC}]
  [HasSheafify C'.J AddCommGrpCat.{wC'}] [C'.J.WEqualsLocallyBijective AddCommGrpCat.{wC'}]
  [HasSheafify D'.J AddCommGrpCat.{wD'}] [D'.J.WEqualsLocallyBijective AddCommGrpCat.{wD'}]
  [HasSheafify B.J (Type wB)] [HasSheafify C.J (Type wC)] [HasSheafify C'.J (Type wC')]
  [HasSheafify D'.J (Type wD')] in
/-- The derived pullback isomorphism of the inverse of the pasted 2-isomorphism of a vertical
rectangle is the composite of the derived pullback isomorphisms of the five pieces it is pasted
from. -/
theorem derivedPullbackIsoOfTwoIso_pasteVertical_symm_hom_app
    (st : RingedToposHom.TwoIso (l.comp f') (f.comp k))
    (sb : RingedToposHom.TwoIso (m.comp g') (g.comp l)) (N :
      DerivedCategory (SheafOfModules.{wD} (SheafOfModules.Tensor.ringSheaf D.O))) :
    (derivedPullbackIsoOfTwoIso (RingedToposHom.TwoIso.pasteVertical st sb).symm).hom.app N =
      (derivedPullbackIsoOfTwoIso (RingedToposHom.TwoIso.associator k f g)).inv.app N ≫
        (derivedPullbackIsoOfTwoIso (st.symm.whiskerRight g)).hom.app N ≫
        (derivedPullbackIsoOfTwoIso (RingedToposHom.TwoIso.associator f' l g)).hom.app N ≫
        (derivedPullbackIsoOfTwoIso (sb.symm.whiskerLeft f')).hom.app N ≫
        (derivedPullbackIsoOfTwoIso (RingedToposHom.TwoIso.associator f' g' m)).inv.app N := by
  show (derivedPullbackIsoOfTwoIso
    (RingedToposHom.TwoIso.pasteHorizontal sb.symm st.symm)).hom.app N = _
  rw [RingedToposHom.TwoIso.pasteHorizontal,
    derivedPullbackIsoOfTwoIso_trans, derivedPullbackIsoOfTwoIso_trans,
    derivedPullbackIsoOfTwoIso_trans, derivedPullbackIsoOfTwoIso_trans,
    derivedPullbackIsoOfTwoIso_symm, derivedPullbackIsoOfTwoIso_symm]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]

variable
  [IsGrothendieckAbelian.{wB} (SheafOfModules.{wB} (SheafOfModules.Tensor.ringSheaf B.O))]
  [IsGrothendieckAbelian.{wB'} (SheafOfModules.{wB'} (SheafOfModules.Tensor.ringSheaf B'.O))]
  [IsGrothendieckAbelian.{wC} (SheafOfModules.{wC} (SheafOfModules.Tensor.ringSheaf C.O))]
  [IsGrothendieckAbelian.{wC'} (SheafOfModules.{wC'} (SheafOfModules.Tensor.ringSheaf C'.O))]

/-- **Stacks 0E46.**  Consider a commutative diagram of ringed topoi

```
                 k
  (Sh(B'), 𝒪) ———→ (Sh(B), 𝒪)
       │ f'              │ f
       v        l        v
  (Sh(C'), 𝒪) ———→ (Sh(C), 𝒪)
       │ g'              │ g
       v                 v
  (Sh(D'), 𝒪) ———→ (Sh(D), 𝒪)
                 m
```

in which each square commutes up to the given 2-isomorphism (Stacks 04IC):
`st : l ∘ f' ≅ f ∘ k` and `sb : m ∘ g' ≅ g ∘ l`, the outer rectangle commuting up to their
pasting `AlgebraicGeometry.RingedToposHom.TwoIso.pasteVertical st sb`.  Then the base change
maps of Remark 07A7 for the two squares compose to the base change map of the rectangle: for
`K` in `D(𝒪_B)`, the composite

`Lm^* R(g ∘ f)_* K = Lm^* Rg_* Rf_* K ⟶ Rg'_* Ll^* Rf_* K ⟶ Rg'_* Rf'_* Lk^* K
  = R(g' ∘ f')_* Lk^* K`

is the base change map of the rectangle.  The two identifications `=` are the composition
isomorphisms of Stacks 0D6E, `derivedPushforwardCompIsoOfAdjoints`.

The seven morphisms are arbitrary morphisms of ringed topoi in the sense of Stacks 01D3,
part (2), the two 2-isomorphisms are arbitrary, and the eighteen universes of the six ringed topoi
are free.  As for the base change map of Remark 07A7 itself (`derivedBaseChangeMapOfTwoIso`), the
module categories of the ringed topoi at the sources of the vertical arrows carry the instance
`CategoryTheory.IsGrothendieckAbelian` at their section universes, which is what makes the
unbounded derived pushforwards exist at free universes (see the implementation notes of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/Existence.lean`). -/
@[stacks 0E46]
theorem derivedBaseChangeMapOfTwoIso_vertical
    (st : RingedToposHom.TwoIso (l.comp f') (f.comp k))
    (sb : RingedToposHom.TwoIso (m.comp g') (g.comp l)) (K :
      DerivedCategory (SheafOfModules.{wB} (SheafOfModules.Tensor.ringSheaf B.O))) :
    (derivedPullback m).map ((derivedPushforwardCompIsoOfAdjoints f g).inv.app K) ≫
        derivedBaseChangeMapOfTwoIso g l g' m sb ((derivedPushforward f).obj K) ≫
        (derivedPushforward g').map (derivedBaseChangeMapOfTwoIso f k f' l st K) ≫
        (derivedPushforwardCompIsoOfAdjoints f' g').hom.app ((derivedPullback k).obj K) =
      derivedBaseChangeMapOfTwoIso (g.comp f) k (g'.comp f') m
        (RingedToposHom.TwoIso.pasteVertical st sb) K :=
  derivedBaseChangeMap_pasteVertical_of_iso (derivedAdjunction f) (derivedAdjunction g)
    (derivedAdjunction (g.comp f)) (derivedAdjunction f') (derivedAdjunction g')
    (derivedAdjunction (g'.comp f'))
    (derivedPushforwardCompIsoOfAdjoints f g) (derivedPushforwardCompIsoOfAdjoints f' g')
    (derivedPullbackCompIso f g) (derivedPullbackCompIso f' g')
    (derivedPullbackCompIso k f) (derivedPullbackIsoOfTwoIso st.symm)
    (derivedPullbackCompIsoLeft f' l)
    (derivedPullbackCompIso l g) (derivedPullbackIsoOfTwoIso sb.symm)
    (derivedPullbackCompIsoLeft g' m)
    (derivedPullbackCompIso k (g.comp f))
    (derivedPullbackIsoOfTwoIso (RingedToposHom.TwoIso.pasteVertical st sb).symm)
    (derivedPullbackCompIsoLeft (g'.comp f') m)
    (derivedPullbackCompIso (f.comp k) g) (derivedPullbackCompIso (l.comp f') g)
    (derivedPullbackCompIso f' (g.comp l)) (derivedPullbackCompIso f' (m.comp g'))
    (derivedPullbackIsoOfTwoIso (RingedToposHom.TwoIso.associator k f g))
    (derivedPullbackIsoOfTwoIso (st.symm.whiskerRight g))
    (derivedPullbackIsoOfTwoIso (RingedToposHom.TwoIso.associator f' l g))
    (derivedPullbackIsoOfTwoIso (sb.symm.whiskerLeft f'))
    (derivedPullbackIsoOfTwoIso (RingedToposHom.TwoIso.associator f' g' m))
    (derivedPullbackCompComparison_assoc_associator k f g)
    (derivedPullbackCompComparison_whiskerRight st.symm g)
    (derivedPullbackCompComparison_assoc_associator f' l g)
    (derivedPullbackCompComparison_whiskerLeft f' sb.symm)
    (derivedPullbackCompComparison_assoc_associator f' g' m)
    (derivedPullbackIsoOfTwoIso_pasteVertical_symm_hom_app f g f' g' k l m st sb)
    (derivedAdjunction_comp_homEquiv f g) (derivedAdjunction_comp_homEquiv f' g')
    K _ _ _
    (derivedBaseChangeMapOfTwoIso_adjoint f k f' l st K)
    (derivedBaseChangeMapOfTwoIso_adjoint g l g' m sb ((derivedPushforward f).obj K))
    (derivedBaseChangeMapOfTwoIso_adjoint (g.comp f) k (g'.comp f') m
      (RingedToposHom.TwoIso.pasteVertical st sb) K)

end Paste

end

end Stacks.Cohomology.DerivedBaseChangeOfToposHom

end
