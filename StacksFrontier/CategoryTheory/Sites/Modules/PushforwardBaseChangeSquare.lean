module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Base change for restriction of sheaves of modules along a square of sites

Consider a square of continuous functors of sites

```
  CV --p--> CX
  |uV        |u
  v          v
  CW --pY-> CY
```

together with right adjoints `b` of `p` and `bY` of `pY`, and an isomorphism
`c : p ⋙ u ≅ uV ⋙ pY`.  Let `O` be a sheaf of rings on `CY`, `OW = pY_* O` its restriction to
`CW`, and `A = u_* O`, `AV = uV_* OW` the two restricted sheaves of rings.  Restriction of sheaves
of modules along these functors gives a square of categories of modules: the two direct images
`R : Mod(O) ⥤ Mod(A)` and `RV : Mod(OW) ⥤ Mod(AV)` along `u` and `uV`, the two restrictions
`rY : Mod(O) ⥤ Mod(OW)` and `rX : Mod(A) ⥤ Mod(AV)` along `pY` and `p` (the second through the ring
isomorphism induced by `c`), and right adjoints `gY` and `gX` of the restrictions, along `bY` and
`b`.

The *Beck–Chevalley transformation* `d : b ⋙ uV ⟶ u ⋙ bY` of the square is the mate of `c⁻¹`.
When it is invertible, the two composite right adjoints `gY ⋙ R` and `RV ⋙ gX` are isomorphic
(`AlgebraicGeometry.ChangeOfSitesSquare.rightAdjointSquareIso`), and the canonical base-change
morphism `R ⋙ rX ⟶ rY ⋙ RV` — the mate of that isomorphism — is, on sections, restriction along
`c⁻¹`, hence an isomorphism (`AlgebraicGeometry.ChangeOfSitesSquare.isIso_baseChangeMap`).

That is the input which lets a statement about the unit of an adjunction `L ⊣ R` be checked after
restriction along `p`: `AlgebraicGeometry.ChangeOfSitesSquare.unit_comp_map_conjugate` relates the
restriction of the unit of `L ⊣ R` to the unit of any adjunction `LV ⊣ RV`, through the conjugate
isomorphism `rX ⋙ LV ≅ L ⋙ rY` and the base-change morphism.

## Main definitions

* `AlgebraicGeometry.ChangeOfSitesSquare.baseChangeTransformation`: the Beck–Chevalley
  transformation `d` of the square of sites.
* `AlgebraicGeometry.ChangeOfSitesSquare.rightAdjointSquareIso`: the isomorphism
  `gY ⋙ R ≅ RV ⋙ gX` of composite right adjoints.
* `AlgebraicGeometry.ChangeOfSitesSquare.baseChangeMap`: the base-change morphism
  `R ⋙ rX ⟶ rY ⋙ RV`.

## Main results

* `AlgebraicGeometry.ChangeOfSitesSquare.baseChangeMap_app_val_app`: on sections the base-change
  morphism is restriction along `c⁻¹`.
* `AlgebraicGeometry.ChangeOfSitesSquare.isIso_baseChangeMap`: it is an isomorphism.
* `CategoryTheory.Adjunction.unit_comp_map_conjugate`: the unit relation of an adjunction square,
  for arbitrary categories.
-/

@[expose] public section

universe w v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ v₅ v₆ v₇ v₈ u₅ u₆ u₇ u₈

open CategoryTheory Functor Opposite

namespace CategoryTheory.Adjunction

variable {C : Type u₅} [Category.{v₅} C] {D : Type u₆} [Category.{v₆} D]
  {C' : Type u₇} [Category.{v₇} C'] {D' : Type u₈} [Category.{v₈} D']
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {L' : C' ⥤ D'} {R' : D' ⥤ C'} (adj' : L' ⊣ R')
  {rC : C ⥤ C'} {gC : C' ⥤ C} (aC : rC ⊣ gC) {rD : D ⥤ D'} {gD : D' ⥤ D} (aD : rD ⊣ gD)

/-- The base-change morphism `R ⋙ rC ⟶ rD ⋙ R'` attached to a natural transformation
`gD ⋙ R ⟶ R' ⋙ gC` of composite right adjoints: its mate across `rD ⊣ gD` and `rC ⊣ gC`. -/
def squareBaseChange (θ : gD ⋙ R ⟶ R' ⋙ gC) : R ⋙ rC ⟶ rD ⋙ R' :=
  ((mateEquiv aD aC).symm (TwoSquare.mk _ _ _ _ θ))

/-- The conjugate `rC ⋙ L' ⟶ L ⋙ rD` of a natural transformation `gD ⋙ R ⟶ R' ⋙ gC` of
composite right adjoints, across the composite adjunctions. -/
def squareConjugate (θ : gD ⋙ R ⟶ R' ⋙ gC) : rC ⋙ L' ⟶ L ⋙ rD :=
  (conjugateEquiv (adj.comp aD) (aC.comp adj')).symm θ

/-- **The unit relation of an adjunction square.**  The unit of `L' ⊣ R'` at `rC G`, followed by
`R'` of the conjugate of `θ`, is the restriction `rC` of the unit of `L ⊣ R` at `G`, followed by
the base-change morphism of `θ`.  So when the conjugate, the base-change morphism and the unit of
`L' ⊣ R'` are invertible, so is the restriction of the unit of `L ⊣ R`. -/
theorem unit_comp_map_conjugate (θ : gD ⋙ R ⟶ R' ⋙ gC) (G : C) :
    adj'.unit.app (rC.obj G) ≫ R'.map ((squareConjugate adj adj' aC aD θ).app G) =
      rC.map (adj.unit.app G) ≫ (squareBaseChange aC aD θ).app (L.obj G) := by
  have h := unit_conjugateEquiv_symm (adj.comp aD) (aC.comp adj') θ G
  simp only [Adjunction.comp_unit_app, Functor.comp_obj, Functor.comp_map, Category.assoc] at h
  have h' := congrArg (fun k => rC.map k ≫ aC.counit.app _) h
  simp only [Functor.map_comp, Category.assoc] at h'
  simp only [Functor.id_obj, Adjunction.counit_naturality, Adjunction.counit_naturality_assoc,
    Adjunction.left_triangle_components_assoc] at h'
  change _ ≫ R'.map (((conjugateEquiv (adj.comp aD) (aC.comp adj')).symm θ).app G) = _
  rw [← h']
  simp [squareBaseChange]

/-- **The counit relation of an adjunction square.**  `L'` of the base-change morphism of `θ` at
`M`, followed by the counit of `L' ⊣ R'`, is the conjugate of `θ` at `R M` followed by the
restriction `rD` of the counit of `L ⊣ R` at `M`. -/
theorem map_squareBaseChange_comp_counit (θ : gD ⋙ R ⟶ R' ⋙ gC) (M : D) :
    L'.map ((squareBaseChange aC aD θ).app M) ≫ adj'.counit.app (rD.obj M) =
      (squareConjugate adj adj' aC aD θ).app (R.obj M) ≫ rD.map (adj.counit.app M) := by
  apply (adj'.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Functor.comp_obj,
    Adjunction.unit_naturality_assoc, Adjunction.right_triangle_components, Category.comp_id]
  rw [reassoc_of% (unit_comp_map_conjugate adj adj' aC aD θ (R.obj M))]
  have hn : (squareBaseChange aC aD θ).app (L.obj (R.obj M)) ≫ R'.map (rD.map (adj.counit.app M)) =
      rC.map (R.map (adj.counit.app M)) ≫ (squareBaseChange aC aD θ).app M :=
    ((squareBaseChange aC aD θ).naturality (adj.counit.app M)).symm
  rw [hn, ← rC.map_comp_assoc, adj.right_triangle_components, rC.map_id, Category.id_comp]

/-- The conjugate of an isomorphism is an isomorphism. -/
instance isIso_squareConjugate (θ : gD ⋙ R ⟶ R' ⋙ gC) [IsIso θ] :
    IsIso (squareConjugate adj adj' aC aD θ) := by
  unfold squareConjugate
  infer_instance

/-- **Invertibility of the unit after restriction.**  If `θ` and its base-change morphism are
invertible, the restriction `rC` of the unit of `L ⊣ R` at `G` is invertible as soon as the unit of
`L' ⊣ R'` is invertible at `rC G`. -/
theorem isIso_map_unit_of_isIso (θ : gD ⋙ R ⟶ R' ⋙ gC) (hθ : IsIso θ)
    (hδ : IsIso (squareBaseChange aC aD θ)) (G : C) (h : IsIso (adj'.unit.app (rC.obj G))) :
    IsIso (rC.map (adj.unit.app G)) := by
  have := unit_comp_map_conjugate adj adj' aC aD θ G
  exact IsIso.of_isIso_fac_right this.symm

/-- **Invertibility of the counit after restriction.**  If `θ` and its base-change morphism are
invertible, the restriction `rD` of the counit of `L ⊣ R` at `M` is invertible as soon as the
counit of `L' ⊣ R'` is invertible at `rD M`. -/
theorem isIso_map_counit_of_isIso (θ : gD ⋙ R ⟶ R' ⋙ gC) (hθ : IsIso θ)
    (hδ : IsIso (squareBaseChange aC aD θ)) (M : D) (h : IsIso (adj'.counit.app (rD.obj M))) :
    IsIso (rD.map (adj.counit.app M)) := by
  have := map_squareBaseChange_comp_counit adj adj' aC aD θ M
  exact IsIso.of_isIso_fac_left this.symm

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ChangeOfSitesSquare

variable {CX : Type u₁} [Category.{v₁} CX] {CY : Type u₂} [Category.{v₂} CY]
  {CV : Type u₃} [Category.{v₃} CV] {CW : Type u₄} [Category.{v₄} CW]
  (JX : GrothendieckTopology CX) (JY : GrothendieckTopology CY)
  (JV : GrothendieckTopology CV) (JW : GrothendieckTopology CW)
  {u : CX ⥤ CY} {uV : CV ⥤ CW} {p : CV ⥤ CX} {b : CX ⥤ CV} {pY : CW ⥤ CY} {bY : CY ⥤ CW}
  [u.IsContinuous JX JY] [uV.IsContinuous JV JW] [p.IsContinuous JV JX] [b.IsContinuous JX JV]
  [pY.IsContinuous JW JY] [bY.IsContinuous JY JW]
  (adjX : p ⊣ b) (adjY : pY ⊣ bY) (c : p ⋙ u ≅ uV ⋙ pY)
  (O : Sheaf JY RingCat.{w})

/-- The Beck–Chevalley transformation `b ⋙ uV ⟶ u ⋙ bY` of the square of sites: the mate of
`c⁻¹` across `p ⊣ b` and `pY ⊣ bY`. -/
def baseChangeTransformation : b ⋙ uV ⟶ u ⋙ bY :=
  (mateEquiv adjX adjY (TwoSquare.mk _ _ _ _ c.inv))

/-- The defining property of the Beck–Chevalley transformation, on components. -/
theorem map_baseChangeTransformation_app_comp_counit (W : CX) :
    pY.map ((baseChangeTransformation adjX adjY c).app W) ≫ adjY.counit.app (u.obj W) =
      c.inv.app (b.obj W) ≫ u.map (adjX.counit.app W) :=
  mateEquiv_counit adjX adjY (TwoSquare.mk _ _ _ _ c.inv) W

/-- The other defining property of the Beck–Chevalley transformation, on components. -/
theorem map_unit_comp_baseChangeTransformation_app (V : CV) :
    uV.map (adjX.unit.app V) ≫ (baseChangeTransformation adjX adjY c).app (p.obj V) =
      adjY.unit.app (uV.obj V) ≫ bY.map (c.inv.app V) :=
  unit_mateEquiv adjX adjY (TwoSquare.mk _ _ _ _ c.inv) V

/-- Restriction along `pY ⊣ bY` of the unit of the Beck–Chevalley transformation is `c⁻¹`. -/
theorem baseChangeTransformation_triangle (V : CV) :
    pY.map (uV.map (adjX.unit.app V)) ≫ pY.map ((baseChangeTransformation adjX adjY c).app
        (p.obj V)) ≫ adjY.counit.app (u.obj (p.obj V)) = c.inv.app V := by
  rw [← Functor.map_comp_assoc, map_unit_comp_baseChangeTransformation_app, Functor.map_comp,
    Category.assoc]
  simp

/-! ### The sheaves of rings -/

/-- The restriction `OW = pY_* O` of the sheaf of rings to `CW`. -/
abbrev ringW : Sheaf JW RingCat.{w} := (pY.sheafPushforwardContinuous RingCat.{w} JW JY).obj O

/-- The direct image `A = u_* O`, a sheaf of rings on `CX`. -/
abbrev ringX : Sheaf JX RingCat.{w} := (u.sheafPushforwardContinuous RingCat.{w} JX JY).obj O

/-- The direct image `AV = uV_* OW`, a sheaf of rings on `CV`. -/
abbrev ringV : Sheaf JV RingCat.{w} :=
  (uV.sheafPushforwardContinuous RingCat.{w} JV JW).obj (ringW JY JW (pY := pY) O)

/-- The ring map `AV ⟶ p_* A` induced by `c`, along which `A`-modules are restricted to `CV`. -/
def ringMapV : ringV JY JV JW (uV := uV) (pY := pY) O ⟶
    (p.sheafPushforwardContinuous RingCat.{w} JV JX).obj (ringX JX JY (u := u) O) :=
  ⟨{ app V := O.obj.map (c.hom.app V.unop).op
     naturality V V' g := by
       change O.obj.map (pY.map (uV.map g.unop)).op ≫ O.obj.map (c.hom.app V'.unop).op =
         O.obj.map (c.hom.app V.unop).op ≫ O.obj.map (u.map (p.map g.unop)).op
       rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp]
       congr 2
       exact (c.hom.naturality g.unop).symm }⟩

/-- The inverse of `ringMapV`. -/
def ringMapVInv :
    (p.sheafPushforwardContinuous RingCat.{w} JV JX).obj (ringX JX JY (u := u) O) ⟶
      ringV JY JV JW (uV := uV) (pY := pY) O :=
  ⟨{ app V := O.obj.map (c.inv.app V.unop).op
     naturality V V' g := by
       change O.obj.map (u.map (p.map g.unop)).op ≫ O.obj.map (c.inv.app V'.unop).op =
         O.obj.map (c.inv.app V.unop).op ≫ O.obj.map (pY.map (uV.map g.unop)).op
       rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp]
       congr 2
       exact (c.inv.naturality g.unop).symm }⟩

/-- The ring isomorphism `ringMapV` induced by `c` is invertible, with inverse `ringMapVInv`. -/
instance isIso_ringMapV : IsIso (ringMapV JX JY JV JW c O) := by
  refine ⟨ringMapVInv JX JY JV JW c O, ?_, ?_⟩
  · ext V : 3
    change O.obj.map (c.hom.app V.unop).op ≫ O.obj.map (c.inv.app V.unop).op = 𝟙 _
    simp only [← Functor.map_comp, ← op_comp, Iso.inv_hom_id_app]
    exact O.obj.map_id _
  · ext V : 3
    change O.obj.map (c.inv.app V.unop).op ≫ O.obj.map (c.hom.app V.unop).op = 𝟙 _
    simp only [← Functor.map_comp, ← op_comp, Iso.hom_inv_id_app]
    exact O.obj.map_id _

/-- The ring map `A ⟶ b_* AV` along which `AV`-modules are pushed forward to `CX`. -/
def ringMapX : ringX JX JY (u := u) O ⟶
    (b.sheafPushforwardContinuous RingCat.{w} JX JV).obj (ringV JY JV JW (uV := uV) (pY := pY) O) :=
  ⟨{ app U := O.obj.map (c.inv.app (b.obj U.unop) ≫ u.map (adjX.counit.app U.unop)).op
     naturality U U' g := by
       change O.obj.map (u.map g.unop).op ≫
           O.obj.map (c.inv.app (b.obj U'.unop) ≫ u.map (adjX.counit.app U'.unop)).op =
         O.obj.map (c.inv.app (b.obj U.unop) ≫ u.map (adjX.counit.app U.unop)).op ≫
           O.obj.map (pY.map (uV.map (b.map g.unop))).op
       simp only [← Functor.map_comp, ← op_comp]
       congr 2
       have h := c.inv.naturality (b.map g.unop)
       dsimp at h
       rw [reassoc_of% h, Category.assoc, ← u.map_comp, ← u.map_comp]
       exact congrArg (fun k => c.inv.app (b.obj U'.unop) ≫ u.map k)
         (adjX.counit_naturality g.unop).symm }⟩

/-- The ring map `O ⟶ bY_* OW` along which `OW`-modules are pushed forward to `CY`. -/
def ringMapY : O ⟶
    (bY.sheafPushforwardContinuous RingCat.{w} JY JW).obj (ringW JY JW (pY := pY) O) :=
  ⟨{ app U := O.obj.map (adjY.counit.app U.unop).op
     naturality U U' g := by
       change O.obj.map g ≫ O.obj.map (adjY.counit.app U'.unop).op =
         O.obj.map (adjY.counit.app U.unop).op ≫ O.obj.map (pY.map (bY.map g.unop)).op
       simp only [← Functor.map_comp, ← op_comp]
       congr 1
       exact Quiver.Hom.unop_inj (adjY.counit_naturality g.unop).symm }⟩

/-! ### The functors on modules -/

/-- The direct image `R : Mod(O) ⥤ Mod(A)` along `u`. -/
noncomputable abbrev directImage :
    SheafOfModules.{w} O ⥤ SheafOfModules.{w} (ringX JX JY (u := u) O) :=
  SheafOfModules.pushforward (𝟙 _)

/-- The direct image `RV : Mod(OW) ⥤ Mod(AV)` along `uV`. -/
noncomputable abbrev directImageV :
    SheafOfModules.{w} (ringW JY JW (pY := pY) O) ⥤
      SheafOfModules.{w} (ringV JY JV JW (uV := uV) (pY := pY) O) :=
  SheafOfModules.pushforward (𝟙 _)

/-- The restriction `rY : Mod(O) ⥤ Mod(OW)` along `pY`. -/
noncomputable abbrev restrictionY :
    SheafOfModules.{w} O ⥤ SheafOfModules.{w} (ringW JY JW (pY := pY) O) :=
  SheafOfModules.pushforward (𝟙 _)

/-- The restriction `rX : Mod(A) ⥤ Mod(AV)` along `p`, through `ringMapV`. -/
noncomputable abbrev restrictionX :
    SheafOfModules.{w} (ringX JX JY (u := u) O) ⥤
      SheafOfModules.{w} (ringV JY JV JW (uV := uV) (pY := pY) O) :=
  SheafOfModules.pushforward (ringMapV JX JY JV JW c O)

/-- The right adjoint `gY : Mod(OW) ⥤ Mod(O)` of `rY`, along `bY`. -/
noncomputable abbrev pushY :
    SheafOfModules.{w} (ringW JY JW (pY := pY) O) ⥤ SheafOfModules.{w} O :=
  SheafOfModules.pushforward (ringMapY JY JW adjY O)

/-- The right adjoint `gX : Mod(AV) ⥤ Mod(A)` of `rX`, along `b`. -/
noncomputable abbrev pushX :
    SheafOfModules.{w} (ringV JY JV JW (uV := uV) (pY := pY) O) ⥤
      SheafOfModules.{w} (ringX JX JY (u := u) O) :=
  SheafOfModules.pushforward (ringMapX JX JY JV JW adjX c O)

/-- `rY ⊣ gY`. -/
noncomputable def adjunctionY : restrictionY JY JW (pY := pY) O ⊣ pushY JY JW adjY O :=
  SheafOfModules.pushforwardPushforwardAdj.{w} adjY (𝟙 _) (ringMapY JY JW adjY O)
    (by
      ext U : 2
      change O.obj.map (adjY.counit.app U.unop).op = O.obj.map (adjY.counit.app U.unop).op ≫ 𝟙 _
      rw [Category.comp_id])
    (by
      ext U : 2
      change 𝟙 _ ≫ O.obj.map (adjY.counit.app (pY.obj U.unop)).op ≫
        O.obj.map (pY.map (adjY.unit.app U.unop)).op = 𝟙 _
      simp only [Category.id_comp, ← Functor.map_comp, ← op_comp]
      simp)

/-- `rX ⊣ gX`. -/
noncomputable def adjunctionX :
    restrictionX JX JY JV JW c O ⊣ pushX JX JY JV JW adjX c O :=
  SheafOfModules.pushforwardPushforwardAdj.{w} adjX (ringMapV JX JY JV JW c O)
    (ringMapX JX JY JV JW adjX c O)
    (by
      ext U : 2
      change O.obj.map (u.map (adjX.counit.app U.unop)).op =
        O.obj.map (c.inv.app (b.obj U.unop) ≫ u.map (adjX.counit.app U.unop)).op ≫
          O.obj.map (c.hom.app (b.obj U.unop)).op
      simp only [← Functor.map_comp, ← op_comp, Iso.hom_inv_id_app_assoc])
    (by
      ext V : 2
      change O.obj.map (c.hom.app V.unop).op ≫
        O.obj.map (c.inv.app (b.obj (p.obj V.unop)) ≫ u.map (adjX.counit.app (p.obj V.unop))).op ≫
          O.obj.map (pY.map (uV.map (adjX.unit.app V.unop))).op = 𝟙 _
      have key : pY.map (uV.map (adjX.unit.app V.unop)) ≫ (c.inv.app (b.obj (p.obj V.unop)) ≫
          u.map (adjX.counit.app (p.obj V.unop))) ≫ c.hom.app V.unop = 𝟙 _ := by
        have h := c.inv.naturality (adjX.unit.app V.unop)
        dsimp at h
        simp only [Category.assoc]
        rw [reassoc_of% h, ← u.map_comp_assoc, adjX.left_triangle_components, u.map_id,
          Category.id_comp, Iso.inv_hom_id_app]
        rfl
      rw [show O.obj.map (c.hom.app V.unop).op ≫
          O.obj.map (c.inv.app (b.obj (p.obj V.unop)) ≫ u.map (adjX.counit.app (p.obj V.unop))).op ≫
            O.obj.map (pY.map (uV.map (adjX.unit.app V.unop))).op =
          O.obj.map (pY.map (uV.map (adjX.unit.app V.unop)) ≫ (c.inv.app (b.obj (p.obj V.unop)) ≫
            u.map (adjX.counit.app (p.obj V.unop))) ≫ c.hom.app V.unop).op by
          simp only [op_comp, Functor.map_comp, Category.assoc], key]
      exact O.obj.map_id _)

variable [IsIso (baseChangeTransformation adjX adjY c)]

/-- **The square of composite right adjoints**, `gY ⋙ R ≅ RV ⋙ gX`, given by restriction along the
Beck–Chevalley transformation once it is invertible. -/
noncomputable def rightAdjointSquareIso :
    pushY JY JW adjY O ⋙ directImage JX JY (u := u) O ≅
      directImageV JY JV JW (uV := uV) O ⋙ pushX JX JY JV JW adjX c O :=
  haveI := Functor.isContinuous_comp u bY JX JY JW
  haveI := Functor.isContinuous_comp b uV JX JV JW
  SheafOfModules.pushforwardComp _ _ ≪≫
    (SheafOfModules.pushforwardCongr₂ _ (asIso (baseChangeTransformation adjX adjY c))
      (by
        ext U : 3
        change (𝟙 _ ≫ O.obj.map (adjY.counit.app (u.obj U.unop)).op) ≫
            O.obj.map (pY.map ((baseChangeTransformation adjX adjY c).app U.unop)).op =
          O.obj.map (c.inv.app (b.obj U.unop) ≫ u.map (adjX.counit.app U.unop)).op ≫ 𝟙 _
        simp only [Category.id_comp, Category.comp_id, ← Functor.map_comp, ← op_comp,
          map_baseChangeTransformation_app_comp_counit])) ≪≫
    (SheafOfModules.pushforwardComp _ _).symm

/-- **The base-change morphism** `R ⋙ rX ⟶ rY ⋙ RV`: the mate of `rightAdjointSquareIso`. -/
noncomputable def baseChangeMap :
    directImage JX JY (u := u) O ⋙ restrictionX JX JY JV JW c O ⟶
      restrictionY JY JW (pY := pY) O ⋙ directImageV JY JV JW (uV := uV) O :=
  Adjunction.squareBaseChange (adjunctionX JX JY JV JW adjX c O) (adjunctionY JY JW adjY O)
    (rightAdjointSquareIso JX JY JV JW adjX adjY c O).hom

/-- **On sections, the base-change morphism is restriction along `c⁻¹`.** -/
theorem baseChangeMap_app_val_app (N : SheafOfModules.{w} O) (V : CVᵒᵖ) (x) :
    ((baseChangeMap JX JY JV JW adjX adjY c O).app N).val.app V x =
      N.val.map (c.inv.app V.unop).op x := by
  have h := baseChangeTransformation_triangle adjX adjY c V.unop
  simp only [baseChangeMap, Adjunction.squareBaseChange, mateEquiv_symm_apply,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.leftUnitor_inv_app,
    Functor.rightUnitor_hom_app, Category.id_comp, Functor.comp_map, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ConcreteCategory.comp_apply]
  change (N.val.presheaf.map (adjY.counit.app (u.obj (p.obj V.unop))).op ≫
      N.val.presheaf.map (pY.map ((baseChangeTransformation adjX adjY c).app (p.obj V.unop))).op ≫
      N.val.presheaf.map (pY.map (uV.map (adjX.unit.app V.unop))).op) x =
    N.val.presheaf.map (c.inv.app V.unop).op x
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, ← h, Category.assoc]

/-- The restriction isomorphism `R ⋙ rX ≅ rY ⋙ RV` along `c⁻¹`. -/
noncomputable def baseChangeIso :
    directImage JX JY (u := u) O ⋙ restrictionX JX JY JV JW c O ≅
      restrictionY JY JW (pY := pY) O ⋙ directImageV JY JV JW (uV := uV) O :=
  haveI := Functor.isContinuous_comp p u JV JX JY
  haveI := Functor.isContinuous_comp uV pY JV JW JY
  SheafOfModules.pushforwardComp _ _ ≪≫
    SheafOfModules.pushforwardCongr₂ _ c.symm (by
      ext V : 3
      change (O.obj.map (c.hom.app V.unop).op ≫ 𝟙 _) ≫ O.obj.map (c.inv.app V.unop).op =
        𝟙 _ ≫ 𝟙 _
      simp only [Category.comp_id, ← Functor.map_comp, ← op_comp, Iso.inv_hom_id_app]
      simp) ≪≫
    (SheafOfModules.pushforwardComp _ _).symm

/-- The base-change morphism is the restriction isomorphism `baseChangeIso` along `c⁻¹`. -/
theorem baseChangeMap_eq :
    baseChangeMap JX JY JV JW adjX adjY c O = (baseChangeIso JX JY JV JW c O).hom := by
  ext N V x
  rw [baseChangeMap_app_val_app]
  rfl

/-- **The base-change morphism `R ⋙ rX ⟶ rY ⋙ RV` is an isomorphism.** -/
instance isIso_baseChangeMap : IsIso (baseChangeMap JX JY JV JW adjX adjY c O) := by
  rw [baseChangeMap_eq]
  infer_instance

end AlgebraicGeometry.ChangeOfSitesSquare
