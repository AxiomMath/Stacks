module

public import StacksFrontier.AlgebraicGeometry.SectionRingBaseChange.CohomologyBaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.SituationRestrict
public import StacksFrontier.AlgebraicGeometry.SymmetricPullback.Transpose
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Units
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison

/-!
# The pullback of a tail truncation along a commutative square

Let

```
Y' --q--> Y
|g'       |g
v         v
T' --h--> T
```

be a commutative square of schemes with `g`, `g'` quasi-compact and quasi-separated, `ℳ`, `ℳ'`
invertible modules on `Y`, `Y'` and `ε : q^*ℳ ≅ ℳ'`.  For a cut `e > 0`, pulling sections back
along `q` is a homomorphism of sheaves of graded algebras

`𝒪_T ⊕ ⨁_{n ≥ e} g_*ℳ^{⊗ n} ⟶ h_*(𝒪_{T'} ⊕ ⨁_{n ≥ e} g'_*(ℳ')^{⊗ n})`,

and its adjoint transpose is a homomorphism of graded algebras

`h^*(𝒪_T ⊕ ⨁_{n ≥ e} g_*ℳ^{⊗ n}) ⟶ 𝒪_{T'} ⊕ ⨁_{n ≥ e} g'_*(ℳ')^{⊗ n}`

which is, in each degree `n ≥ e`, the base-change morphism `h^* g_* ℳ^{⊗ n} ⟶ g'_* (ℳ')^{⊗ n}`.
This is the functoriality of the algebra `𝒜'` of [Stacks, Tag 0D4F] in the data.

## Main definitions

* `Stacks.AlgebraicGeometry.SectionRingBaseChange.tailPushHom`: the homomorphism into the direct
  image.
* `Stacks.AlgebraicGeometry.SectionRingBaseChange.tailPullbackHom`: its adjoint transpose.

## Main results

* `Stacks.AlgebraicGeometry.SectionRingBaseChange.isIso_tailPullbackHom_app`: the transpose is an
  isomorphism in every degree, as soon as the base-change morphisms in degrees `≥ e` are.

## References

* [Stacks Project, Tag 0D4F](https://stacks.math.columbia.edu/tag/0D4F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.RingedSpace Stacks.SheafOfModules.TensorPower Stacks.TensorPowerPullback
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.SectionAlgebra

universe u

namespace Stacks.AlgebraicGeometry.SectionRingBaseChange

attribute [local instance 10000] HasDerivedCategory.standard

variable {Y' Y T' T : Scheme.{u}} (q : Y' ⟶ Y) (g : Y ⟶ T) (g' : Y' ⟶ T') (h : T' ⟶ T)
  (w : q ≫ g = g' ≫ h) [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g']
  (M : Y.Modules) [Stacks.Ample.IsInvertibleModule Y M]
  (M' : Y'.Modules) [Stacks.Ample.IsInvertibleModule Y' M']
  (ε : (Scheme.Modules.pullback q).obj M ≅ M')

/-! ### The degreewise map into the direct image -/

/-- **Pulling sections of `ℳ^{⊗ n}` back along `q`, as a morphism of sheaves on `T`**:
`g_* ℳ^{⊗ n} ⟶ g_* q_* q^* ℳ^{⊗ n} = h_* g'_* q^* ℳ^{⊗ n} ≅ h_* g'_* (ℳ')^{⊗ n}`. -/
def pushPieceMap (n : ℤ) :
    (Scheme.Modules.pushforward g).obj ((Stacks.RelativeAmple.laurentPowers M).piece n) ⟶
      (Scheme.Modules.pushforward h).obj ((Scheme.Modules.pushforward g').obj
        ((Stacks.RelativeAmple.laurentPowers M').piece n)) :=
  haveI := isInvertible_tensorPower_of_isInvertibleModule Y M
  haveI := isInvertible_tensorPower_of_isInvertibleModule Y' M'
  haveI := isInvertible_tensorPower_of_isInvertibleModule Y' ((Scheme.Modules.pullback q).obj M)
  (Scheme.Modules.pushforward g).map ((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app
      ((Stacks.RelativeAmple.laurentPowers M).piece n)) ≫
    (Stacks.AlgebraicGeometry.AffinePushforward.pushforwardSquareIso w).hom.app _ ≫
    (Scheme.Modules.pushforward h).map ((Scheme.Modules.pushforward g').map
      ((pullbackIntPowIso q.toLRSHom.toShHom M n).hom ≫
        (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrIso ε n).hom))

omit [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g'] in
/-- `pushPieceMap` is the adjoint transpose of the base-change morphism
`h^* g_* ℳ^{⊗ n} ⟶ g'_* (ℳ')^{⊗ n}` (`baseChangePowHom`). -/
theorem pushPieceMap_eq (n : ℤ) :
    pushPieceMap q g g' h w M M' ε n =
      (Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv _ _
        (baseChangePowHom q g g' h M M' ε w n) := by
  rw [Adjunction.homEquiv_unit, baseChangePowHom, Functor.map_comp, ← Category.assoc]
  have key := Stacks.AlgebraicGeometry.AffineBaseChange.unit_comp_pushforward_baseChangeNatTrans
    w ((Stacks.RelativeAmple.laurentPowers M).piece n)
  refine Eq.trans ?_ (congrArg (· ≫ _) key).symm
  rw [pushPieceMap, Category.assoc]

omit [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g'] in
/-- On sections over `V`, `pushPieceMap` is `squarePieceMap` over `V` and `h⁻¹V`. -/
theorem pushPieceMap_app (n : ℤ) (V : T.Opens)
    (x : Γ((Scheme.Modules.pushforward g).obj ((Stacks.RelativeAmple.laurentPowers M).piece n),
      V)) :
    (pushPieceMap q g g' h w M M' ε n).app V x =
      squarePieceMap q g g' h w M M' ε V (h ⁻¹ᵁ V) le_rfl n x := by
  have := isInvertible_tensorPower_of_isInvertibleModule Y M
  have := isInvertible_tensorPower_of_isInvertibleModule Y' M'
  have := isInvertible_tensorPower_of_isInvertibleModule Y' ((Scheme.Modules.pullback q).obj M)
  have e1 : (pushPieceMap q g g' h w M M' ε n).app V x =
      ((pullbackIntPowIso q.toLRSHom.toShHom M n).hom ≫
        (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrIso ε n).hom).val.app
          (op (g' ⁻¹ᵁ (h ⁻¹ᵁ V)))
        (((Scheme.Modules.pullback q).obj
          ((Stacks.RelativeAmple.laurentPowers M).piece n)).presheaf.map
          (homOfLE (preimage_le_preimage q g g' h w V (h ⁻¹ᵁ V) le_rfl)).op
          (((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app
            ((Stacks.RelativeAmple.laurentPowers M).piece n)).app (g ⁻¹ᵁ V) x)) := rfl
  refine e1.trans ?_
  have hn := ConcreteCategory.congr_hom
    ((pullbackIntPowIso q.toLRSHom.toShHom M n).hom.val.naturality
      (homOfLE (preimage_le_preimage q g g' h w V (h ⁻¹ᵁ V) le_rfl)).op)
    (((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app
      ((Stacks.RelativeAmple.laurentPowers M).piece n)).app (g ⁻¹ᵁ V) x)
  exact congrArg (fun z => (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrIso ε
    n).hom.val.app (op (g' ⁻¹ᵁ (h ⁻¹ᵁ V))) z) hn

/-! ### The map of tail truncations into the direct image -/

section Tail

variable (e : ℕ) (he : 0 < e)

local notation "Pg" => Stacks.AlgebraicGeometry.PushforwardGradedAlgebra.pushforwardGradedAlgebra g
  (Stacks.RelativeAmple.laurentPowers M)
local notation "Pg'" =>
  Stacks.AlgebraicGeometry.PushforwardGradedAlgebra.pushforwardGradedAlgebra g'
  (Stacks.RelativeAmple.laurentPowers M')

/-- `h^♯` on sections over `V`, typed on the structure sheaves. -/
def pullRingHom (V : T.Opens) :
    T.ringCatSheaf.obj.obj (op V) →+* T'.ringCatSheaf.obj.obj (op (h ⁻¹ᵁ V)) :=
  (h.app V).hom

/-- **The degree-`n` component of the map of tail truncations into the direct image**: `h^♯` in
degree zero, `pushPieceMap` in each degree `n ≥ e`, and zero in between. -/
def tailPushApp (n : ℤ) :
    @Quiver.Hom T.Modules _ (tailPiece Pg e n)
      ((Scheme.Modules.pushforward h).obj (tailPiece Pg' e n)) :=
  if h0 : n = 0 then
    eqToHom (tailPiece_eq_unit Pg e h0) ≫ Scheme.Modules.unitToPushforwardUnit h ≫
      (Scheme.Modules.pushforward h).map (eqToHom (tailPiece_eq_unit Pg' e h0).symm)
  else if hn : (e : ℤ) ≤ n then
    eqToHom (tailPiece_eq_piece Pg e he hn) ≫ pushPieceMap q g g' h w M M' ε n ≫
      (Scheme.Modules.pushforward h).map (eqToHom (tailPiece_eq_piece Pg' e he hn).symm)
  else (0 : (@id T.Modules (tailPiece Pg e n)) ⟶
    (Scheme.Modules.pushforward h).obj (tailPiece Pg' e n))

omit [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g'] in
/-- On sections over `V`, `tailPushApp` is the degreewise map `tailMapApp` for `h^♯` and
`squarePieceMap`. -/
theorem tailPushApp_app (n : ℤ) (V : T.Opens) (x : (tailPiece Pg e n).val.obj (op V)) :
    (tailPushApp q g g' h w M M' ε e he n).val.app (op V) x =
      tailMapApp Pg Pg' e e he he le_rfl V (h ⁻¹ᵁ V) (pullRingHom h V)
        (squarePieceMap q g g' h w M M' ε V (h ⁻¹ᵁ V) le_rfl) n x := by
  unfold tailPushApp
  by_cases h0 : n = 0
  · rw [dite_eq_left h0, tailMapApp_zero h0]
    rfl
  · by_cases hn : (e : ℤ) ≤ n
    · rw [dite_eq_right h0, dite_eq_left hn, tailMapApp_tail h0 hn]
      exact congrArg _ (pushPieceMap_app q g g' h w M M' ε n V _)
    · rw [dite_eq_right h0, dite_eq_right hn, tailMapApp_null h0 hn]
      rfl

omit [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g'] in
/-- `squarePieceMap` over `V` and `h⁻¹V` is semilinear along the pullback of sections
`Γ(T, V) ⟶ Γ(T', h⁻¹V)`. -/
theorem squarePieceMap_smul' (V : T.Opens) (n : ℤ) (r : T.ringCatSheaf.obj.obj (op V))
    (x : ((Pg).piece n).val.obj (op V)) :
    squarePieceMap q g g' h w M M' ε V (h ⁻¹ᵁ V) le_rfl n (r • x) =
      pullRingHom h V r • squarePieceMap q g g' h w M M' ε V (h ⁻¹ᵁ V) le_rfl n x := by
  refine (squarePieceMap_smul q g g' h w M M' ε V (h ⁻¹ᵁ V) le_rfl n r x).trans ?_
  rw [pullRingHom, Scheme.Hom.app_eq_appLE]
  rfl

/-- **Pulling sections back along `q`, as a homomorphism of sheaves of graded algebras**
`𝒪_T ⊕ ⨁_{n ≥ e} g_*ℳ^{⊗ n} ⟶ h_*(𝒪_{T'} ⊕ ⨁_{n ≥ e} g'_*(ℳ')^{⊗ n})`. -/
def tailPushHom :
    SheafOfModules.GradedAlgebra.UnitalHom
      (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.situationAlgebra (tailAlgebra g M e he))
      (Stacks.RingedSpace.pushforwardAlgebra
        (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ringedSpaceHom h)
        (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.situationAlgebra
          (tailAlgebra g' M' e he))) where
  app n := tailPushApp q g g' h w M M' ε e he n
  map_mul i j V x y := by
    obtain ⟨V⟩ := V
    refine (tailPushApp_app q g g' h w M M' ε e he (i + j) V _).trans ?_
    refine (tailMapApp_mul (squarePieceMap_smul' q g g' h w M M' ε V)
      (fun n m _ _ x y => squarePieceMap_mul q g g' h w M M' ε V (h ⁻¹ᵁ V) le_rfl n m x y)
      i j x y).trans ?_
    rw [← tailPushApp_app q g g' h w M M' ε e he i V x,
      ← tailPushApp_app q g g' h w M M' ε e he j V y]
    rfl
  map_one V := by
    obtain ⟨V⟩ := V
    refine (tailPushApp_app q g g' h w M M' ε e he 0 V _).trans ?_
    exact tailMapApp_one

/-- The adjoint transpose of `a ≫ b ≫ G.map c` is invertible as soon as `a`, `c` and the transpose
of `b` are. -/
theorem isIso_homEquiv_symm_comp {C D : Type*} [Category C] [Category D] {F : C ⥤ D}
    {G : D ⥤ C} (adj : F ⊣ G) {X X' : C} {Y Y' : D} (a : X ⟶ X') (b : X' ⟶ G.obj Y')
    (c : Y' ⟶ Y) (ha : IsIso a) (hc : IsIso c) (hb : IsIso ((adj.homEquiv _ _).symm b)) :
    IsIso ((adj.homEquiv X Y).symm (a ≫ b ≫ G.map c)) := by
  rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_right_symm]
  infer_instance

/-- **The adjoint transpose: the homomorphism of graded algebras**
`h^*(𝒪_T ⊕ ⨁_{n ≥ e} g_*ℳ^{⊗ n}) ⟶ 𝒪_{T'} ⊕ ⨁_{n ≥ e} g'_*(ℳ')^{⊗ n}`. -/
def tailPullbackHom :
    SheafOfModules.GradedAlgebra.UnitalHom
      (Stacks.RingedSpace.pullbackGradedAlgebra
        (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ringedSpaceHom h)
        (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.situationAlgebra (tailAlgebra g M e he)))
      (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.situationAlgebra (tailAlgebra g' M' e he)) :=
  Stacks.RingedSpace.transposeUnitalHom _ (tailPushHom q g g' h w M M' ε e he)

/-- In degree `n`, `tailPullbackHom` is the adjoint transpose of `tailPushApp` in degree `n`. -/
theorem tailPullbackHom_app (n : ℤ) :
    (tailPullbackHom q g g' h w M M' ε e he).app n =
      ((Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv _ _).symm
        (tailPushApp q g g' h w M M' ε e he n) := rfl

/-- **The transpose is an isomorphism in every degree**, as soon as the base-change morphisms
`h^* g_* ℳ^{⊗ n} ⟶ g'_* (ℳ')^{⊗ n}` are for `n ≥ e`: in degree zero it is the identification
`h^* 𝒪_T ≅ 𝒪_{T'}`, in degrees `n ≥ e` the base-change morphism, and in between both sides
vanish. -/
theorem isIso_tailPullbackHom_app
    (hbc : ∀ n : ℤ, (e : ℤ) ≤ n → IsIso (baseChangePowHom q g g' h M M' ε w n)) (n : ℤ) :
    IsIso ((tailPullbackHom q g g' h w M M' ε e he).app n) := by
  rw [tailPullbackHom_app]
  by_cases h0 : n = 0
  · unfold tailPushApp
    rw [dite_eq_left h0]
    refine isIso_homEquiv_symm_comp _ _ _ _ (Iso.isIso_hom (eqToIso (tailPiece_eq_unit Pg e h0)))
      (Iso.isIso_hom (eqToIso (tailPiece_eq_unit Pg' e h0).symm)) ?_
    rw [← Scheme.Modules.pullbackUnitIso_homEquiv]
    exact (congrArg IsIso (((Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv
      T.unitModule T'.unitModule).symm_apply_apply (Scheme.Modules.pullbackUnitIso h).hom)).mpr
        (Iso.isIso_hom _)
  · by_cases hn : (e : ℤ) ≤ n
    · unfold tailPushApp
      rw [dite_eq_right h0, dite_eq_left hn]
      refine isIso_homEquiv_symm_comp _ _ _ _
        (Iso.isIso_hom (eqToIso (tailPiece_eq_piece Pg e he hn)))
        (Iso.isIso_hom (eqToIso (tailPiece_eq_piece Pg' e he hn).symm)) ?_
      rw [pushPieceMap_eq]
      exact (congrArg IsIso (((Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv _
        _).symm_apply_apply (baseChangePowHom q g g' h M M' ε w n))).mpr (hbc n hn)
    · have hs : IsZero ((Scheme.Modules.pullback h).obj (tailPiece Pg e n)) := by
        rw [tailPiece_eq_zero Pg e h0 hn]
        exact Functor.map_isZero _ (isZero_zero _)
      have ht : IsZero (tailPiece Pg' e n : T'.Modules) := by
        rw [tailPiece_eq_zero Pg' e h0 hn]
        exact isZero_zero _
      exact isIso_of_source_target_iso_zero _ hs.isoZero ht.isoZero

end Tail

end Stacks.AlgebraicGeometry.SectionRingBaseChange

end
