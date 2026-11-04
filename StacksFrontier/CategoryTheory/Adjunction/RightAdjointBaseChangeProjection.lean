module

public import StacksFrontier.CategoryTheory.Adjunction.RightAdjointBaseChange
public import StacksFrontier.CategoryTheory.Adjunction.ProjectionFormulaMap
public import StacksFrontier.CategoryTheory.Adjunction.CounitHomExt

/-!
# The pushed-forward base change map of right adjoints, through the projection formula

Consider the situation of `StacksFrontier/CategoryTheory/Adjunction/RightAdjointBaseChange.lean`:
adjunctions `Rf ⊣ a`, `Rf' ⊣ a'`, `Lg ⊣ Rg`, `Lg' ⊣ Rg'` and a base change transformation
`β : Lg ∘ Rf ⟶ Rf' ∘ Lg'` whose mate `ξ : Rg' ∘ a' ⟶ a ∘ Rg` is invertible, so that the base
change map `α : Lg' ∘ a ⟶ a' ∘ Lg` of Stacks 0E5D is defined. Suppose the four corners carry
bifunctors `T` (read `T(P, Q) = P ⊗ Q`), with comparisons `π` along `Lg`, `Lg'` and along a left
adjoint `Lf'` of `Rf'`, braidings `s` and right unitors `ρ`. Write `J = Rg 𝒪'` and `J' = Rg' 𝒪''`,
and `Φ_M : M ⊗ J ⟶ Rg(Lg M)` for the projection-formula map of `Lg ⊣ Rg` at the unit followed by
the unitor (and `Φ'` for `g'`).

Then `Rg'(α_K)`, followed by `ξ`, is identified with a two-variable comparison
`c : LJ ⊗ a K ⟶ a(J ⊗ K)` of `a`: the square

```
LJ ⊗ aK --τ⊗1--> J' ⊗ aK --s--> aK ⊗ J' --Φ'--> Rg' Lg' aK --Rg' α--> Rg' a' Lg K --ξ--> a Rg Lg K
   |                                                                                        ^
   c                                                                                        |
   v                                                                                        |
a(J ⊗ K) ----------------------------------s----------------> a(K ⊗ J) ---------a Φ---------+
```

commutes, where `τ : LJ ⟶ J'` is a transposed base change map at the unit. The inputs are the
hexagon of Stacks 0E48 for `β` (with the projection formula of `Lf' ⊣ Rf'` and an arbitrary map
`p` on the left), the characterization of `c` through `p`, the defining property of `τ`, the unit
compatibility of the comparison along `Lf'`, and the compatibility of the comparisons with the
braidings. Since all the other maps of the square are invertible in the situation of
Stacks 0E5I, so is `Rg'(α_K)`. This is the abstract content of the proof of Stacks 0E5I (1) over
an affine base, for a base change map built directly from `β` (no identification of the
composite pullbacks around the square is needed).

## Main definitions

* `CategoryTheory.RightAdjointBaseChange.pushforwardComparison` — `σ : Rf ∘ Rg' ⟶ Rg ∘ Rf'`, the
  adjoint transpose of `β` followed by the counit of `Lg' ⊣ Rg'`.
* `CategoryTheory.RightAdjointBaseChange.rightUnitProjection` — `Φ_M : M ⊗ R 𝒪 ⟶ R(L M)`.

## Main results

* `CategoryTheory.RightAdjointBaseChange.map_rightAdjointMate_app_comp_counit_eq` — `Rf ξ`
  followed by the trace is `σ` followed by `Rg` of the trace.
* `CategoryTheory.RightAdjointBaseChange.comp_rightUnitProjection_comp_pushforwardComparison` —
  the projection formula and `σ`.
* `CategoryTheory.RightAdjointBaseChange.rightUnitProjection_comp_map_comp_rightAdjointMate` —
  the square above.
* `CategoryTheory.RightAdjointBaseChange.isIso_map_map_app_of_isIso` — `Rg'(α_K)` is invertible.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.Prod

namespace CategoryTheory.RightAdjointBaseChange

section Bifunctor

variable {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D)
  (π : (CategoryTheory.Prod.swap C C ⋙ Functor.uncurry.obj TC) ⋙ L ⟶
    L.prod L ⋙ (CategoryTheory.Prod.swap D D ⋙ Functor.uncurry.obj TD))

/-- Naturality of a comparison along `L` in the variable read on the right of `T`. -/
theorem comparison_naturality_fst (N : C) {H H' : C} (q : H ⟶ H') :
    L.map ((TC.map q).app N) ≫ π.app (N, H') =
      π.app (N, H) ≫ (TD.map (L.map q)).app (L.obj N) := by
  have h := π.naturality ((𝟙 N, q) : ((N, H) : C × C) ⟶ (N, H'))
  simpa using h

/-- Naturality of a comparison along `L` in the variable read on the left of `T`. -/
theorem comparison_naturality_snd {N N' : C} (p : N ⟶ N') (H : C) :
    L.map ((TC.obj H).map p) ≫ π.app (N', H) =
      π.app (N, H) ≫ (TD.obj (L.obj H)).map (L.map p) := by
  have h := π.naturality ((p, 𝟙 H) : ((N, H) : C × C) ⟶ (N', H))
  simpa using h

/-- The projection-formula map `H ⊗ R E ⟶ R(L H ⊗ E)` followed by the counit, written with the
curried bifunctors. -/
theorem map_adjunctionTensorMap_comp_counit_curried (E : D) (H : C) :
    L.map (adjunctionTensorMap adj (CategoryTheory.Prod.swap C C ⋙ Functor.uncurry.obj TC)
        (CategoryTheory.Prod.swap D D ⋙ Functor.uncurry.obj TD) π E H) ≫
        adj.counit.app ((TD.obj (L.obj H)).obj E) =
      π.app (R.obj E, H) ≫ (TD.obj (L.obj H)).map (adj.counit.app E) := by
  have h := map_adjunctionTensorMap_comp_counit adj
    (CategoryTheory.Prod.swap C C ⋙ Functor.uncurry.obj TC)
    (CategoryTheory.Prod.swap D D ⋙ Functor.uncurry.obj TD) π E H
  simpa using h

/-- The projection-formula map is natural in the variable read on the left of `T`. -/
theorem adjunctionTensorMap_naturality_curried (E : D) {H H' : C} (h : H ⟶ H') :
    (TC.map h).app (R.obj E) ≫ adjunctionTensorMap adj
        (CategoryTheory.Prod.swap C C ⋙ Functor.uncurry.obj TC)
        (CategoryTheory.Prod.swap D D ⋙ Functor.uncurry.obj TD) π E H' =
      adjunctionTensorMap adj (CategoryTheory.Prod.swap C C ⋙ Functor.uncurry.obj TC)
          (CategoryTheory.Prod.swap D D ⋙ Functor.uncurry.obj TD) π E H ≫
        R.map ((TD.map (L.map h)).app E) := by
  have e := adjunctionTensorMap_natural adj
    (CategoryTheory.Prod.swap C C ⋙ Functor.uncurry.obj TC)
    (CategoryTheory.Prod.swap D D ⋙ Functor.uncurry.obj TD) π (𝟙 E) h
  simpa using e

variable (o : D) (ρ : TD.flip.obj o ⟶ 𝟭 D)

/-- **The projection-formula map at the unit**, `Φ_M : M ⊗ R 𝒪 ⟶ R(L M)`: the projection-formula
map `M ⊗ R 𝒪 ⟶ R(L M ⊗ 𝒪)` of `L ⊣ R` followed by `R` of the right unitor. -/
def rightUnitProjection (M : C) : (TC.obj M).obj (R.obj o) ⟶ R.obj (L.obj M) :=
  adjunctionTensorMap adj (CategoryTheory.Prod.swap C C ⋙ Functor.uncurry.obj TC)
      (CategoryTheory.Prod.swap D D ⋙ Functor.uncurry.obj TD) π o M ≫
    R.map (ρ.app (L.obj M))

/-- `Φ_M` is an isomorphism when the projection-formula map at `𝒪` and the right unitor at `L M`
are. -/
instance isIso_rightUnitProjection (M : C)
    [IsIso (adjunctionTensorMap adj (CategoryTheory.Prod.swap C C ⋙ Functor.uncurry.obj TC)
      (CategoryTheory.Prod.swap D D ⋙ Functor.uncurry.obj TD) π o M)]
    [IsIso (ρ.app (L.obj M))] :
    IsIso (rightUnitProjection adj TC TD π o ρ M) := by
  unfold rightUnitProjection; infer_instance

/-- The adjoint transpose of `Φ_M`: the comparison, the counit at `𝒪` and the unitor. -/
theorem map_rightUnitProjection_comp_counit (M : C) :
    L.map (rightUnitProjection adj TC TD π o ρ M) ≫ adj.counit.app (L.obj M) =
      π.app (R.obj o, M) ≫ (TD.obj (L.obj M)).map (adj.counit.app o) ≫ ρ.app (L.obj M) := by
  have h := map_adjunctionTensorMap_comp_counit_curried adj TC TD π o M
  have hn : L.map (R.map (ρ.app (L.obj M))) ≫ adj.counit.app (L.obj M) =
      adj.counit.app ((TD.obj (L.obj M)).obj o) ≫ ρ.app (L.obj M) :=
    adj.counit_naturality _
  rw [rightUnitProjection, Functor.map_comp, Category.assoc, hn, reassoc_of% h]

/-- `Φ` is natural in its argument. -/
theorem rightUnitProjection_naturality {M M' : C} (h : M ⟶ M') :
    (TC.map h).app (R.obj o) ≫ rightUnitProjection adj TC TD π o ρ M' =
      rightUnitProjection adj TC TD π o ρ M ≫ R.map (L.map h) := by
  have hρ : (TD.map (L.map h)).app o ≫ ρ.app (L.obj M') = ρ.app (L.obj M) ≫ L.map h :=
    ρ.naturality (L.map h)
  rw [rightUnitProjection, ← Category.assoc, adjunctionTensorMap_naturality_curried,
    rightUnitProjection, Category.assoc, Category.assoc, ← R.map_comp, ← R.map_comp, hρ]

end Bifunctor

section Braiding

variable {C : Type*} [Category C] {T : C ⥤ C ⥤ C} (s : T ⟶ T.flip)

/-- A transformation `T ⟶ T.flip` is natural in its first variable. -/
theorem flip_naturality_fst {P P' : C} (φ : P ⟶ P') (Q : C) :
    (T.map φ).app Q ≫ (s.app P').app Q = (s.app P).app Q ≫ (T.obj Q).map φ :=
  NatTrans.congr_app (s.naturality φ) Q

/-- A transformation `T ⟶ T.flip` is natural in its second variable. -/
theorem flip_naturality_snd (P : C) {Q Q' : C} (ψ : Q ⟶ Q') :
    (T.obj P).map ψ ≫ (s.app P).app Q' = (s.app P).app Q ≫ (T.map ψ).app P :=
  (s.app P).naturality ψ

end Braiding

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {CY : Type u₁} {CX : Type u₂} {CY' : Type u₃} {CX' : Type u₄}
  [Category.{v₁} CY] [Category.{v₂} CX] [Category.{v₃} CY'] [Category.{v₄} CX']
  {Rf : CX ⥤ CY} {a : CY ⥤ CX} {Rf' : CX' ⥤ CY'} {a' : CY' ⥤ CX'}
  {Lg : CY ⥤ CY'} {Rg : CY' ⥤ CY} {Lg' : CX ⥤ CX'} {Rg' : CX' ⥤ CX}
  (adjF : Rf ⊣ a) (adjF' : Rf' ⊣ a') (adjG : Lg ⊣ Rg) (adjG' : Lg' ⊣ Rg')
  (β : Rf ⋙ Lg ⟶ Lg' ⋙ Rf')

/-- **The comparison `σ : Rf ∘ Rg' ⟶ Rg ∘ Rf'` of the composite pushforwards**: the adjoint
transpose under `Lg ⊣ Rg` of `β` followed by `Rf'` of the counit of `Lg' ⊣ Rg'`. -/
def pushforwardComparison (P : CX') : Rf.obj (Rg'.obj P) ⟶ Rg.obj (Rf'.obj P) :=
  adjG.homEquiv _ _ (β.app (Rg'.obj P) ≫ Rf'.map (adjG'.counit.app P))

/-- The adjoint transpose of `σ` under `Lg ⊣ Rg` is `β` followed by `Rf'` of the counit of
`Lg' ⊣ Rg'`. -/
@[reassoc]
theorem map_pushforwardComparison_comp_counit (P : CX') :
    Lg.map (pushforwardComparison adjG adjG' β P) ≫ adjG.counit.app (Rf'.obj P) =
      β.app (Rg'.obj P) ≫ Rf'.map (adjG'.counit.app P) :=
  (adjG.homEquiv_counit _ _ _).symm.trans (Equiv.symm_apply_apply _ _)

/-- `σ` is natural. -/
theorem pushforwardComparison_naturality {P P' : CX'} (φ : P ⟶ P') :
    Rf.map (Rg'.map φ) ≫ pushforwardComparison adjG adjG' β P' =
      pushforwardComparison adjG adjG' β P ≫ Rg.map (Rf'.map φ) := by
  apply Stacks.Adjunction.hom_ext_of_map_comp_counit adjG
  have hβ : Lg.map (Rf.map (Rg'.map φ)) ≫ β.app (Rg'.obj P') =
      β.app (Rg'.obj P) ≫ Rf'.map (Lg'.map (Rg'.map φ)) := β.naturality (Rg'.map φ)
  have hε : Lg'.map (Rg'.map φ) ≫ adjG'.counit.app P' = adjG'.counit.app P ≫ φ :=
    adjG'.counit_naturality φ
  have hε' : Lg.map (Rg.map (Rf'.map φ)) ≫ adjG.counit.app (Rf'.obj P') =
      adjG.counit.app (Rf'.obj P) ≫ Rf'.map φ := adjG.counit_naturality _
  rw [Functor.map_comp, Category.assoc, map_pushforwardComparison_comp_counit, reassoc_of% hβ,
    ← Rf'.map_comp, hε, Functor.map_comp, Functor.map_comp, Category.assoc, hε',
    map_pushforwardComparison_comp_counit_assoc]

/-- `Rf` of the mate `ξ : Rg' ∘ a' ⟶ a ∘ Rg`, followed by the trace of `Rf ⊣ a`, is `σ` followed
by `Rg` of the trace of `Rf' ⊣ a'`. -/
theorem map_rightAdjointMate_app_comp_counit_eq (M : CY') :
    Rf.map ((rightAdjointMate adjF adjF' adjG adjG' β).app M) ≫ adjF.counit.app (Rg.obj M) =
      pushforwardComparison adjG adjG' β (a'.obj M) ≫ Rg.map (adjF'.counit.app M) := by
  apply Stacks.Adjunction.hom_ext_of_map_comp_counit adjG
  have hε' : Lg.map (Rg.map (adjF'.counit.app M)) ≫ adjG.counit.app M =
      adjG.counit.app (Rf'.obj (a'.obj M)) ≫ adjF'.counit.app M := adjG.counit_naturality _
  rw [Functor.map_comp, Category.assoc, map_rightAdjointMate_app_comp_counit, Functor.map_comp,
    Category.assoc, hε', map_pushforwardComparison_comp_counit_assoc]

section Tensor

variable (TY : CY ⥤ CY ⥤ CY) (TX : CX ⥤ CX ⥤ CX) (TY' : CY' ⥤ CY' ⥤ CY')
  (TX' : CX' ⥤ CX' ⥤ CX') {Lf' : CY' ⥤ CX'} (adjf' : Lf' ⊣ Rf')
  (πg : (CategoryTheory.Prod.swap CY CY ⋙ Functor.uncurry.obj TY) ⋙ Lg ⟶
    Lg.prod Lg ⋙ (CategoryTheory.Prod.swap CY' CY' ⋙ Functor.uncurry.obj TY'))
  (πg' : (CategoryTheory.Prod.swap CX CX ⋙ Functor.uncurry.obj TX) ⋙ Lg' ⟶
    Lg'.prod Lg' ⋙ (CategoryTheory.Prod.swap CX' CX' ⋙ Functor.uncurry.obj TX'))
  (πf' : (CategoryTheory.Prod.swap CY' CY' ⋙ Functor.uncurry.obj TY') ⋙ Lf' ⟶
    Lf'.prod Lf' ⋙ (CategoryTheory.Prod.swap CX' CX' ⋙ Functor.uncurry.obj TX'))
  (sY : TY ⟶ TY.flip) (sX : TX ⟶ TX.flip) (sY' : TY' ⟶ TY'.flip) (sX' : TX' ⟶ TX'.flip)
  (oY' : CY') (oX' : CX') (ρY' : TY'.flip.obj oY' ⟶ 𝟭 CY') (ρX' : TX'.flip.obj oX' ⟶ 𝟭 CX')
  (υ : Lf'.obj oY' ⟶ oX')

/-- **The projection formula of `Lf' ⊣ Rf'` at the unit, read through the braidings**: it is
the braiding followed by the right unitor, `𝒪 ⊗ Rf' P ⟶ Rf' P`. -/
theorem adjunctionTensorMap_comp_map_unit_braiding (P : CX')
    (hunit : ∀ Q : CY', πf'.app (oY', Q) ≫ (TX'.obj (Lf'.obj Q)).map υ ≫ ρX'.app (Lf'.obj Q) =
      Lf'.map (ρY'.app Q))
    (hbrf' : ∀ P Q : CY', Lf'.map ((sY'.app P).app Q) ≫ πf'.app (P, Q) =
      πf'.app (Q, P) ≫ (sX'.app (Lf'.obj P)).app (Lf'.obj Q)) :
    adjunctionTensorMap adjf' (CategoryTheory.Prod.swap CY' CY' ⋙ Functor.uncurry.obj TY')
        (CategoryTheory.Prod.swap CX' CX' ⋙ Functor.uncurry.obj TX') πf' P oY' ≫
        Rf'.map ((TX'.map υ).app P ≫ (sX'.app oX').app P ≫ ρX'.app P) =
      (sY'.app oY').app (Rf'.obj P) ≫ ρY'.app (Rf'.obj P) := by
  refine Stacks.Adjunction.hom_ext_of_map_comp_counit (Y := P) adjf' ?_
  have hε : Lf'.map (Rf'.map ((TX'.map υ).app P ≫ (sX'.app oX').app P ≫ ρX'.app P)) ≫
      adjf'.counit.app P = adjf'.counit.app ((TX'.obj (Lf'.obj oY')).obj P) ≫
        (TX'.map υ).app P ≫ (sX'.app oX').app P ≫ ρX'.app P := adjf'.counit_naturality _
  have h0 := map_adjunctionTensorMap_comp_counit_curried adjf' TY' TX' πf' P oY'
  have h1 : (TX'.obj (Lf'.obj oY')).map (adjf'.counit.app P) ≫ (TX'.map υ).app P =
      (TX'.map υ).app (Lf'.obj (Rf'.obj P)) ≫ (TX'.obj oX').map (adjf'.counit.app P) :=
    (TX'.map υ).naturality (adjf'.counit.app P)
  have h2 := flip_naturality_snd sX' oX' (adjf'.counit.app P)
  have h3 : (TX'.map (adjf'.counit.app P)).app oX' ≫ ρX'.app P =
      ρX'.app (Lf'.obj (Rf'.obj P)) ≫ adjf'.counit.app P :=
    ρX'.naturality (adjf'.counit.app P)
  have h4 := flip_naturality_fst sX' υ (Lf'.obj (Rf'.obj P))
  have h5 := hbrf' oY' (Rf'.obj P)
  have h6 := hunit (Rf'.obj P)
  have hR : Lf'.map ((sY'.app oY').app (Rf'.obj P) ≫ ρY'.app (Rf'.obj P)) ≫
      adjf'.counit.app P = (Lf'.map ((sY'.app oY').app (Rf'.obj P)) ≫
        Lf'.map (ρY'.app (Rf'.obj P))) ≫ adjf'.counit.app P := by
    rw [Functor.map_comp]
  rw [hR, Functor.map_comp, Category.assoc, hε, reassoc_of% h0, reassoc_of% h1,
    reassoc_of% h2, h3, ← h6, reassoc_of% h4, ← reassoc_of% h5]
  simp only [Category.assoc]

variable {LJ : CX} (cJ : Lg'.obj LJ ⟶ Lf'.obj (Lg.obj (Rg.obj oY'))) (τ : LJ ⟶ Rg'.obj oX')

section Core

variable (N : CX) (p : (TY.obj (Rg.obj oY')).obj (Rf.obj N) ⟶ Rf.obj ((TX.obj LJ).obj N))

/-- **The projection formula and the comparison `σ` of the composite pushforwards.** Given the
hexagon of Stacks 0E48 for `β` at `(N, J)`, the defining property of `τ`, the unit compatibility
along `Lf'` and the compatibility of the comparisons with the braidings, `p` followed by
`Rf(τ ⊗ 1, s, Φ')` and `σ` is the braiding followed by `Φ` and `Rg β`. -/
theorem comp_rightUnitProjection_comp_pushforwardComparison
    (hex : πg.app (Rf.obj N, Rg.obj oY') ≫ (TY'.obj (Lg.obj (Rg.obj oY'))).map (β.app N) ≫
        adjunctionTensorMap adjf' (CategoryTheory.Prod.swap CY' CY' ⋙ Functor.uncurry.obj TY')
          (CategoryTheory.Prod.swap CX' CX' ⋙ Functor.uncurry.obj TX') πf' (Lg'.obj N)
          (Lg.obj (Rg.obj oY')) =
      Lg.map p ≫ β.app ((TX.obj LJ).obj N) ≫
        Rf'.map (πg'.app (N, LJ) ≫ (TX'.map cJ).app (Lg'.obj N)))
    (hτ : Lg'.map τ ≫ adjG'.counit.app oX' = cJ ≫ Lf'.map (adjG.counit.app oY') ≫ υ)
    (hunit : ∀ Q : CY', πf'.app (oY', Q) ≫ (TX'.obj (Lf'.obj Q)).map υ ≫ ρX'.app (Lf'.obj Q) =
      Lf'.map (ρY'.app Q))
    (hbrg : ∀ P Q : CY, Lg.map ((sY.app P).app Q) ≫ πg.app (P, Q) =
      πg.app (Q, P) ≫ (sY'.app (Lg.obj P)).app (Lg.obj Q))
    (hbrg' : ∀ P Q : CX, Lg'.map ((sX.app P).app Q) ≫ πg'.app (P, Q) =
      πg'.app (Q, P) ≫ (sX'.app (Lg'.obj P)).app (Lg'.obj Q))
    (hbrf' : ∀ P Q : CY', Lf'.map ((sY'.app P).app Q) ≫ πf'.app (P, Q) =
      πf'.app (Q, P) ≫ (sX'.app (Lf'.obj P)).app (Lf'.obj Q)) :
    p ≫ Rf.map ((TX.map τ).app N ≫ (sX.app (Rg'.obj oX')).app N ≫
        rightUnitProjection adjG' TX TX' πg' oX' ρX' N) ≫
        pushforwardComparison adjG adjG' β (Lg'.obj N) =
      (sY.app (Rg.obj oY')).app (Rf.obj N) ≫
        rightUnitProjection adjG TY TY' πg oY' ρY' (Rf.obj N) ≫ Rg.map (β.app N) := by
  refine Stacks.Adjunction.hom_ext_of_map_comp_counit (Y := Rf'.obj (Lg'.obj N)) adjG ?_
  have hβ : Lg.map (Rf.map ((TX.map τ).app N ≫ (sX.app (Rg'.obj oX')).app N ≫
      rightUnitProjection adjG' TX TX' πg' oX' ρX' N)) ≫ β.app (Rg'.obj (Lg'.obj N)) =
      β.app ((TX.obj LJ).obj N) ≫ Rf'.map (Lg'.map ((TX.map τ).app N ≫
        (sX.app (Rg'.obj oX')).app N ≫ rightUnitProjection adjG' TX TX' πg' oX' ρX' N)) :=
    β.naturality _
  have hΦ' := map_rightUnitProjection_comp_counit adjG' TX TX' πg' oX' ρX' N
  have hn := comparison_naturality_fst TX TX' πg' N τ
  have hb' := hbrg' (Rg'.obj oX') N
  have hs' : (TX'.map (adjG'.counit.app oX')).app (Lg'.obj N) ≫ (sX'.app oX').app (Lg'.obj N) =
      (sX'.app (Lg'.obj (Rg'.obj oX'))).app (Lg'.obj N) ≫
        (TX'.obj (Lg'.obj N)).map (adjG'.counit.app oX') :=
    flip_naturality_fst sX' (adjG'.counit.app oX') (Lg'.obj N)
  have hx : Lg'.map ((TX.map τ).app N ≫ (sX.app (Rg'.obj oX')).app N ≫
      rightUnitProjection adjG' TX TX' πg' oX' ρX' N) ≫ adjG'.counit.app (Lg'.obj N) =
      (πg'.app (N, LJ) ≫ (TX'.map cJ).app (Lg'.obj N)) ≫
        (TX'.map (Lf'.map (adjG.counit.app oY'))).app (Lg'.obj N) ≫
        ((TX'.map υ).app (Lg'.obj N) ≫ (sX'.app oX').app (Lg'.obj N) ≫
          ρX'.app (Lg'.obj N)) := by
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hΦ',
      reassoc_of% hb', ← reassoc_of% hs', reassoc_of% hn, ← NatTrans.comp_app_assoc,
      ← Functor.map_comp, hτ]
    simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
  have hnat := adjunctionTensorMap_naturality_curried adjf' TY' TX' πf' (Lg'.obj N)
    (adjG.counit.app oY')
  have hLU := adjunctionTensorMap_comp_map_unit_braiding TY' TX' adjf' πf' sY' sX' oY' oX' ρY'
    ρX' υ (Lg'.obj N) hunit hbrf'
  have hL : Lg.map (p ≫ Rf.map ((TX.map τ).app N ≫ (sX.app (Rg'.obj oX')).app N ≫
        rightUnitProjection adjG' TX TX' πg' oX' ρX' N) ≫
        pushforwardComparison adjG adjG' β (Lg'.obj N)) ≫ adjG.counit.app (Rf'.obj (Lg'.obj N)) =
      πg.app (Rf.obj N, Rg.obj oY') ≫ (TY'.obj (Lg.obj (Rg.obj oY'))).map (β.app N) ≫
        (TY'.map (adjG.counit.app oY')).app (Rf'.obj (Lg'.obj N)) ≫
        (sY'.app oY').app (Rf'.obj (Lg'.obj N)) ≫ ρY'.app (Rf'.obj (Lg'.obj N)) := by
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
      map_pushforwardComparison_comp_counit, reassoc_of% hβ, ← Rf'.map_comp, hx,
      Rf'.map_comp, ← reassoc_of% hex, Rf'.map_comp, ← reassoc_of% hnat, hLU]
  have hΦ := map_rightUnitProjection_comp_counit adjG TY TY' πg oY' ρY' (Rf.obj N)
  have hb := hbrg (Rg.obj oY') (Rf.obj N)
  have hs : (TY'.map (adjG.counit.app oY')).app (Lg.obj (Rf.obj N)) ≫
      (sY'.app oY').app (Lg.obj (Rf.obj N)) =
      (sY'.app (Lg.obj (Rg.obj oY'))).app (Lg.obj (Rf.obj N)) ≫
        (TY'.obj (Lg.obj (Rf.obj N))).map (adjG.counit.app oY') :=
    flip_naturality_fst sY' (adjG.counit.app oY') (Lg.obj (Rf.obj N))
  have hs2 : (TY'.obj oY').map (β.app N) ≫ (sY'.app oY').app (Rf'.obj (Lg'.obj N)) =
      (sY'.app oY').app (Lg.obj (Rf.obj N)) ≫ (TY'.map (β.app N)).app oY' :=
    flip_naturality_snd sY' oY' (β.app N)
  have hρ : (TY'.map (β.app N)).app oY' ≫ ρY'.app (Rf'.obj (Lg'.obj N)) =
      ρY'.app (Lg.obj (Rf.obj N)) ≫ β.app N := ρY'.naturality (β.app N)
  have hT : (TY'.obj (Lg.obj (Rg.obj oY'))).map (β.app N) ≫
      (TY'.map (adjG.counit.app oY')).app (Rf'.obj (Lg'.obj N)) =
      (TY'.map (adjG.counit.app oY')).app (Lg.obj (Rf.obj N)) ≫ (TY'.obj oY').map (β.app N) :=
    (TY'.map (adjG.counit.app oY')).naturality (β.app N)
  have hcn : Lg.map (Rg.map (β.app N)) ≫ adjG.counit.app (Rf'.obj (Lg'.obj N)) =
      adjG.counit.app (Lg.obj (Rf.obj N)) ≫ β.app N := adjG.counit_naturality _
  have hR : Lg.map ((sY.app (Rg.obj oY')).app (Rf.obj N) ≫
        rightUnitProjection adjG TY TY' πg oY' ρY' (Rf.obj N) ≫ Rg.map (β.app N)) ≫
        adjG.counit.app (Rf'.obj (Lg'.obj N)) =
      πg.app (Rf.obj N, Rg.obj oY') ≫ (TY'.obj (Lg.obj (Rg.obj oY'))).map (β.app N) ≫
        (TY'.map (adjG.counit.app oY')).app (Rf'.obj (Lg'.obj N)) ≫
        (sY'.app oY').app (Rf'.obj (Lg'.obj N)) ≫ ρY'.app (Rf'.obj (Lg'.obj N)) := by
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hcn,
      reassoc_of% hΦ, reassoc_of% hb, ← reassoc_of% hs, ← hρ, ← reassoc_of% hs2,
      ← reassoc_of% hT]
  exact hL.trans hR.symm

end Core

variable (K : CY) [IsIso (rightAdjointMate adjF adjF' adjG adjG' β)]
  (p : (TY.obj (Rg.obj oY')).obj (Rf.obj (a.obj K)) ⟶ Rf.obj ((TX.obj LJ).obj (a.obj K)))
  (c : (TX.obj LJ).obj (a.obj K) ⟶ a.obj ((TY.obj (Rg.obj oY')).obj K))

/-- **The pushed-forward base change map of right adjoints, through the projection formula**:
`τ ⊗ 1`, the braiding, `Φ'`, `Rg'(α_K)` and `ξ` compose to the two-variable comparison `c`
followed by `a` of the braiding and of `Φ`. -/
theorem rightUnitProjection_comp_map_comp_rightAdjointMate [IsIso p]
    (hc : p ≫ Rf.map c ≫ adjF.counit.app _ = (TY.obj (Rg.obj oY')).map (adjF.counit.app K))
    (hex : πg.app (Rf.obj (a.obj K), Rg.obj oY') ≫
        (TY'.obj (Lg.obj (Rg.obj oY'))).map (β.app (a.obj K)) ≫
        adjunctionTensorMap adjf' (CategoryTheory.Prod.swap CY' CY' ⋙ Functor.uncurry.obj TY')
          (CategoryTheory.Prod.swap CX' CX' ⋙ Functor.uncurry.obj TX') πf' (Lg'.obj (a.obj K))
          (Lg.obj (Rg.obj oY')) =
      Lg.map p ≫ β.app ((TX.obj LJ).obj (a.obj K)) ≫
        Rf'.map (πg'.app (a.obj K, LJ) ≫ (TX'.map cJ).app (Lg'.obj (a.obj K))))
    (hτ : Lg'.map τ ≫ adjG'.counit.app oX' = cJ ≫ Lf'.map (adjG.counit.app oY') ≫ υ)
    (hunit : ∀ Q : CY', πf'.app (oY', Q) ≫ (TX'.obj (Lf'.obj Q)).map υ ≫ ρX'.app (Lf'.obj Q) =
      Lf'.map (ρY'.app Q))
    (hbrg : ∀ P Q : CY, Lg.map ((sY.app P).app Q) ≫ πg.app (P, Q) =
      πg.app (Q, P) ≫ (sY'.app (Lg.obj P)).app (Lg.obj Q))
    (hbrg' : ∀ P Q : CX, Lg'.map ((sX.app P).app Q) ≫ πg'.app (P, Q) =
      πg'.app (Q, P) ≫ (sX'.app (Lg'.obj P)).app (Lg'.obj Q))
    (hbrf' : ∀ P Q : CY', Lf'.map ((sY'.app P).app Q) ≫ πf'.app (P, Q) =
      πf'.app (Q, P) ≫ (sX'.app (Lf'.obj P)).app (Lf'.obj Q)) :
    (TX.map τ).app (a.obj K) ≫ (sX.app (Rg'.obj oX')).app (a.obj K) ≫
        rightUnitProjection adjG' TX TX' πg' oX' ρX' (a.obj K) ≫
        Rg'.map ((map adjF adjF' adjG adjG' β).app K) ≫
        (rightAdjointMate adjF adjF' adjG adjG' β).app (Lg.obj K) =
      c ≫ a.map ((sY.app (Rg.obj oY')).app K ≫ rightUnitProjection adjG TY TY' πg oY' ρY' K) := by
  refine Stacks.Adjunction.hom_ext_of_map_comp_counit (Y := Rg.obj (Lg.obj K)) adjF ?_
  rw [← cancel_epi p]
  have hcore := comp_rightUnitProjection_comp_pushforwardComparison adjG adjG' β TY TX TY' TX'
    adjf' πg πg' πf' sY sX sY' sX' oY' oX' ρY' ρX' υ cJ τ (a.obj K) p hex hτ hunit hbrg hbrg'
    hbrf'
  have hξ := map_rightAdjointMate_app_comp_counit_eq adjF adjF' adjG adjG' β (Lg.obj K)
  have hσ := pushforwardComparison_naturality adjG adjG' β ((map adjF adjF' adjG adjG' β).app K)
  have h0E5L := map_counit adjF adjF' adjG adjG' β K
  have hΦ : (TY.map (adjF.counit.app K)).app (Rg.obj oY') ≫
      rightUnitProjection adjG TY TY' πg oY' ρY' K =
      rightUnitProjection adjG TY TY' πg oY' ρY' (Rf.obj (a.obj K)) ≫
        Rg.map (Lg.map (adjF.counit.app K)) :=
    rightUnitProjection_naturality adjG TY TY' πg oY' ρY' (adjF.counit.app K)
  have hs : (TY.obj (Rg.obj oY')).map (adjF.counit.app K) ≫ (sY.app (Rg.obj oY')).app K =
      (sY.app (Rg.obj oY')).app (Rf.obj (a.obj K)) ≫
        (TY.map (adjF.counit.app K)).app (Rg.obj oY') :=
    flip_naturality_snd sY (Rg.obj oY') (adjF.counit.app K)
  have hcn : Rf.map (a.map ((sY.app (Rg.obj oY')).app K ≫
      rightUnitProjection adjG TY TY' πg oY' ρY' K)) ≫ adjF.counit.app (Rg.obj (Lg.obj K)) =
      adjF.counit.app ((TY.obj (Rg.obj oY')).obj K) ≫ (sY.app (Rg.obj oY')).app K ≫
        rightUnitProjection adjG TY TY' πg oY' ρY' K := adjF.counit_naturality _
  calc p ≫ Rf.map ((TX.map τ).app (a.obj K) ≫ (sX.app (Rg'.obj oX')).app (a.obj K) ≫
        rightUnitProjection adjG' TX TX' πg' oX' ρX' (a.obj K) ≫
        Rg'.map ((map adjF adjF' adjG adjG' β).app K) ≫
        (rightAdjointMate adjF adjF' adjG adjG' β).app (Lg.obj K)) ≫
        adjF.counit.app (Rg.obj (Lg.obj K)) =
      (p ≫ Rf.map ((TX.map τ).app (a.obj K) ≫ (sX.app (Rg'.obj oX')).app (a.obj K) ≫
        rightUnitProjection adjG' TX TX' πg' oX' ρX' (a.obj K)) ≫
        pushforwardComparison adjG adjG' β (Lg'.obj (a.obj K))) ≫
        Rg.map (Rf'.map ((map adjF adjF' adjG adjG' β).app K) ≫
          adjF'.counit.app (Lg.obj K)) := by
        simp only [Functor.map_comp, Category.assoc]
        rw [hξ, reassoc_of% hσ]
    _ = (sY.app (Rg.obj oY')).app (Rf.obj (a.obj K)) ≫
        rightUnitProjection adjG TY TY' πg oY' ρY' (Rf.obj (a.obj K)) ≫
        Rg.map (Lg.map (adjF.counit.app K)) := by
        rw [hcore, Category.assoc, Category.assoc, ← Rg.map_comp, h0E5L]
    _ = p ≫ Rf.map (c ≫ a.map ((sY.app (Rg.obj oY')).app K ≫
          rightUnitProjection adjG TY TY' πg oY' ρY' K)) ≫ adjF.counit.app (Rg.obj (Lg.obj K)) := by
        rw [Functor.map_comp, Category.assoc, hcn, reassoc_of% hc, reassoc_of% hs, hΦ]

/-- **The pushed-forward base change map of right adjoints is invertible**, as soon as `τ`, the
braidings, `Φ'` at `a K`, `c` and `Φ` at `K` are. -/
theorem isIso_map_map_app_of_isIso [IsIso p]
    (hc : p ≫ Rf.map c ≫ adjF.counit.app _ = (TY.obj (Rg.obj oY')).map (adjF.counit.app K))
    (hex : πg.app (Rf.obj (a.obj K), Rg.obj oY') ≫
        (TY'.obj (Lg.obj (Rg.obj oY'))).map (β.app (a.obj K)) ≫
        adjunctionTensorMap adjf' (CategoryTheory.Prod.swap CY' CY' ⋙ Functor.uncurry.obj TY')
          (CategoryTheory.Prod.swap CX' CX' ⋙ Functor.uncurry.obj TX') πf' (Lg'.obj (a.obj K))
          (Lg.obj (Rg.obj oY')) =
      Lg.map p ≫ β.app ((TX.obj LJ).obj (a.obj K)) ≫
        Rf'.map (πg'.app (a.obj K, LJ) ≫ (TX'.map cJ).app (Lg'.obj (a.obj K))))
    (hτ : Lg'.map τ ≫ adjG'.counit.app oX' = cJ ≫ Lf'.map (adjG.counit.app oY') ≫ υ)
    (hunit : ∀ Q : CY', πf'.app (oY', Q) ≫ (TX'.obj (Lf'.obj Q)).map υ ≫ ρX'.app (Lf'.obj Q) =
      Lf'.map (ρY'.app Q))
    (hbrg : ∀ P Q : CY, Lg.map ((sY.app P).app Q) ≫ πg.app (P, Q) =
      πg.app (Q, P) ≫ (sY'.app (Lg.obj P)).app (Lg.obj Q))
    (hbrg' : ∀ P Q : CX, Lg'.map ((sX.app P).app Q) ≫ πg'.app (P, Q) =
      πg'.app (Q, P) ≫ (sX'.app (Lg'.obj P)).app (Lg'.obj Q))
    (hbrf' : ∀ P Q : CY', Lf'.map ((sY'.app P).app Q) ≫ πf'.app (P, Q) =
      πf'.app (Q, P) ≫ (sX'.app (Lf'.obj P)).app (Lf'.obj Q))
    [IsIso τ] [IsIso ((sX.app (Rg'.obj oX')).app (a.obj K))]
    [IsIso (rightUnitProjection adjG' TX TX' πg' oX' ρX' (a.obj K))] [IsIso c]
    [IsIso ((sY.app (Rg.obj oY')).app K)] [IsIso (rightUnitProjection adjG TY TY' πg oY' ρY' K)] :
    IsIso (Rg'.map ((map adjF adjF' adjG adjG' β).app K)) := by
  have h := rightUnitProjection_comp_map_comp_rightAdjointMate adjF adjF' adjG adjG' β TY TX TY'
    TX' adjf' πg πg' πf' sY sX sY' sX' oY' oX' ρY' ρX' υ cJ τ K p c hc hex hτ hunit hbrg hbrg'
    hbrf'
  have h1 : IsIso ((TX.map τ).app (a.obj K) ≫ (sX.app (Rg'.obj oX')).app (a.obj K) ≫
      rightUnitProjection adjG' TX TX' πg' oX' ρX' (a.obj K) ≫
      Rg'.map ((map adjF adjF' adjG adjG' β).app K) ≫
      (rightAdjointMate adjF adjF' adjG adjG' β).app (Lg.obj K)) := by
    rw [h]; infer_instance
  rw [isIso_comp_left_iff, isIso_comp_left_iff, isIso_comp_left_iff] at h1
  exact IsIso.of_isIso_comp_right _ ((rightAdjointMate adjF adjF' adjG adjG' β).app (Lg.obj K))

end Tensor

end CategoryTheory.RightAdjointBaseChange
