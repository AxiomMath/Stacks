module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalPointedSections
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.StratifiedCrystal

/-!
# A quasi-coherent crystal is the crystal of its stratification

Let `ℱ` be a crystal in quasi-coherent `𝒪_{X/S}`-modules on `Cris(X/S)`, with `X` and `S` affine,
let `M = lim_e Γ(T(0)_e, ℱ)` be its module over the completed envelope `D`
(`...SmallSite.wholeSpaceSections`) and let `E` be a stratification of `M` relative to the system
of [Stacks, Tag 07JN] (`...SmallSite.wholeSpaceDescentSystem`) which is *the stratification of
`ℱ`*: written in the trivialisation of the first vertex `v₀ : T(1)_e ⟶ T(0)_e`, it is the
restriction of `m` along the second vertex `v₁`,

`crystalPointMap v₀ (E m) = v₁^* m_e`.

This file proves that the crystal `...SmallSite.stratCrystal E` built from `(M, E)` in the proof of
[Stacks, Proposition 60.17.4, Tag 07JH] is isomorphic to `ℱ`.

## The argument

Over an affine object `A` with a pointing `h : A ⟶ T(0)_e`, a descended section `z` is read through
`h` as an element of `Γ(A, 𝒪) ⊗_{D,h} M`, and `crystalPointMap h` sends it to `ℱ(A)`
(`...SmallSite.stratPointMap`).  This does not depend on `h`:

* along a level map it is the compatibility of the components of `m ∈ M`
  (`...SmallSite.stratPointMap_levTo`);
* for two pointings at the same level, the evaluations of `z` differ by the comparison of the pair
  `(h, h')`, and the hypothesis on `E` says that `crystalPointMap` turns this comparison into the
  identity (`...SmallSite.crystalPointMap_comparison`, `...SmallSite.stratPointMap_eq`).

The maps commute with restriction, are bijective by `...SmallSite.bijective_crystalPointMap`, and
so give an isomorphism of sheaves on the affine subsite (`...SmallSite.stratAffineIso`), which
the restriction to the affine subsite, an equivalence, carries back to `Cris(X/S)`.

## Main definitions and results

* `...SmallSite.stratCrystalIso` — **the isomorphism `stratCrystal E ≅ ℱ`**.
* `...SmallSite.stratCrystalIso_hom_app` — its component over an affine object `A`, read through
  any pointing `h` of `A`, is `crystalPointMap h ∘ evalEquiv h ∘ stratSectionsEquiv E A`.
* `...SmallSite.stratCrystalIso_naturality` — it is natural in the pair `(ℱ, E)`.

## References

* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry Simplicial
open scoped TensorProduct

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline.StratifiedDescent

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  {hp : IsNilpotent (S.p : Γ(S.X, ⊤))} [WholeSpacePresentation S hp]

/-- The pointing `A ⟶ T(0)_e` of the descent system, as a morphism of `Cris(X/S)` to the level
`...SmallSite.levelObj hp 0 e`. -/
def descentPointHom {A : AffineCrystallineThickening S} {e : ℕ}
    (h : A ⟶ (wholeSpaceDescentSystem S hp).T0 e) : A.obj ⟶ levelObj hp 0 e :=
  h.hom

/-- The underlying morphism of a composite pointing. -/
theorem descentPointHom_comp {A B : AffineCrystallineThickening S} {e : ℕ} (k : A ⟶ B)
    (h : B ⟶ (wholeSpaceDescentSystem S hp).T0 e) :
    descentPointHom (k ≫ h) = k.hom ≫ descentPointHom h := rfl

/-- The underlying morphism of a pointing followed by a level map. -/
theorem descentPointHom_lev {A : AffineCrystallineThickening S} {e : ℕ}
    (h : A ⟶ (wholeSpaceDescentSystem S hp).T0 e) :
    descentPointHom (h ≫ (wholeSpaceDescentSystem S hp).lev e) =
      descentPointHom h ≫ ((wholeSpaceSystem S hp).obj (op ⦋0⦌)).map (homOfLE (Nat.le_succ e)) :=
  rfl

/-- **The ring map of a pointing in the descent system is that of `...SmallSite.ptRing`**, on the
nose. -/
theorem ptRing_wholeSpaceDescentSystem {A : AffineCrystallineThickening S} {e : ℕ}
    (h : A ⟶ (wholeSpaceDescentSystem S hp).T0 e) :
    (wholeSpaceDescentSystem S hp).ptRing h = ptRing hp (descentPointHom h) := rfl

/-- The identification of the twisted tensor product along the ring map of a pointing of the
descent system with the one along `...SmallSite.ptRing` (the identity). -/
def descentPointTwist {M : Type u} [AddCommGroup M] [Module (envD S hp) M]
    {A : AffineCrystallineThickening S} {e : ℕ}
    (h : A ⟶ (wholeSpaceDescentSystem S hp).T0 e) :
    TwistedScalars ((wholeSpaceDescentSystem S hp).ptRing h) ⊗[envD S hp] M ≃+
      TwistedScalars (ptRing hp (descentPointHom h)) ⊗[envD S hp] M :=
  AddEquiv.refl _

/-- `...SmallSite.descentPointTwist` on a pure tensor. -/
theorem descentPointTwist_tmul {M : Type u} [AddCommGroup M] [Module (envD S hp) M]
    {A : AffineCrystallineThickening S} {e : ℕ}
    (h : A ⟶ (wholeSpaceDescentSystem S hp).T0 e)
    (b : TwistedScalars ((wholeSpaceDescentSystem S hp).ptRing h)) (m : M) :
    descentPointTwist h (b ⊗ₜ[envD S hp] m) =
      TwistedScalars.mk (ptRing hp (descentPointHom h)) b.val ⊗ₜ[envD S hp] m := rfl

/-- `...SmallSite.descentPointTwist` commutes with the scalars. -/
theorem descentPointTwist_smul {M : Type u} [AddCommGroup M] [Module (envD S hp) M]
    {A : AffineCrystallineThickening S} {e : ℕ}
    (h : A ⟶ (wholeSpaceDescentSystem S hp).T0 e) (r : (affineSectionsRing S).obj (op A))
    (y : TwistedScalars ((wholeSpaceDescentSystem S hp).ptRing h) ⊗[envD S hp] M) :
    descentPointTwist h (r • y) =
      RingHom.id (crysSheafRing S A.obj.obj) r • descentPointTwist h y :=
  rfl

variable (F : QuasiCoherentCrystal S)

/-- **`crystalPointMap` is natural along a morphism of affine objects**: for `k : A ⟶ B` and a
pointing `g` of `B`, the change of ring along `k` followed by `crystalPointMap (k ≫ g)` is
`crystalPointMap g` followed by restriction along `k`. -/
theorem crystalPointMap_twistMap {A B : AffineCrystallineThickening S} {e : ℕ} (k : A ⟶ B)
    (g : B ⟶ (wholeSpaceDescentSystem S hp).T0 e) (h : A ⟶ (wholeSpaceDescentSystem S hp).T0 e)
    (hk : k ≫ g = h)
    (y : TwistedScalars ((wholeSpaceDescentSystem S hp).ptRing g) ⊗[envD S hp]
      wholeSpaceSections hp F ⦋0⦌) :
    crystalPointMap hp F (descentPointHom h) (descentPointTwist h
      (twistMap ((affineSectionsRing S).map k.op).hom
        ((wholeSpaceDescentSystem S hp).map_comp_ptRing hk) y)) =
      crysRestrict F.obj k.hom
        (crystalPointMap hp F (descentPointHom g) (descentPointTwist g y)) := by
  subst hk
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul b m =>
    rw [twistMap_tmul, descentPointTwist_tmul, descentPointTwist_tmul, crystalPointMap_tmul,
      crystalPointMap_tmul, map_smulₛₗ, crysRestrict_comp, descentPointHom_comp]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **`crystalPointMap` does not see a level map**: at `h ≫ lev e` it is `crystalPointMap h`, the
two twisted tensor products being identified. -/
theorem crystalPointMap_lev {A : AffineCrystallineThickening S} {e : ℕ}
    (h : A ⟶ (wholeSpaceDescentSystem S hp).T0 e)
    (y : TwistedScalars ((wholeSpaceDescentSystem S hp).ptRing h) ⊗[envD S hp]
      wholeSpaceSections hp F ⦋0⦌) :
    crystalPointMap hp F (descentPointHom (h ≫ (wholeSpaceDescentSystem S hp).lev e))
      (descentPointTwist _ (twistCongr ((wholeSpaceDescentSystem S hp).ptRing_lev h).symm y)) =
      crystalPointMap hp F (descentPointHom h) (descentPointTwist h y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul b m =>
    rw [twistCongr_tmul, descentPointTwist_tmul, descentPointTwist_tmul, crystalPointMap_tmul,
      crystalPointMap_tmul, descentPointHom_lev, ← crysRestrict_comp]
    congr 2
    exact wholeSpaceSectionsVal_restrict hp F m (homOfLE (Nat.le_succ e))
  | add x y hx hy => simp only [map_add, hx, hy]

variable {F} (E : Stratification (wholeSpaceDescentSystem S hp) (wholeSpaceSections hp F ⦋0⦌))

/-- **For the stratification of `ℱ`, `crystalPointMap` turns the comparisons into the identity**:
for `φ : A ⟶ T(1)_e` with vertices `h` and `h'`, `crystalPointMap h ∘ c_φ = crystalPointMap h'`. -/
theorem crystalPointMap_comparison
    (hE : ∀ e m, crystalPointMap hp F ((wholeSpaceDescentSystem S hp).v e 0).hom (E.str e m) =
      crysRestrict F.obj ((wholeSpaceDescentSystem S hp).v e 1).hom
        (wholeSpaceSectionsVal hp F m e))
    {A : AffineCrystallineThickening S} {e : ℕ}
    (φ : A ⟶ (wholeSpaceDescentSystem S hp).T1 e) (h h' : A ⟶ (wholeSpaceDescentSystem S hp).T0 e)
    (H₀ : φ ≫ (wholeSpaceDescentSystem S hp).v e 0 = h)
    (H₁ : φ ≫ (wholeSpaceDescentSystem S hp).v e 1 = h')
    (x : TwistedScalars ((wholeSpaceDescentSystem S hp).ptRing h') ⊗[envD S hp]
      wholeSpaceSections hp F ⦋0⦌) :
    crystalPointMap hp F (descentPointHom h) (descentPointTwist h
      ((wholeSpaceDescentSystem S hp).comparison E.str φ _ _
        ((wholeSpaceDescentSystem S hp).map_comp_ptRing H₀)
        ((wholeSpaceDescentSystem S hp).map_comp_ptRing H₁) x)) =
      crystalPointMap hp F (descentPointHom h') (descentPointTwist h' x) := by
  have hE' : ∀ m, crystalPointMap hp F (descentPointHom ((wholeSpaceDescentSystem S hp).v e 0))
      (descentPointTwist _ (E.str e m)) =
      crysRestrict F.obj (descentPointHom ((wholeSpaceDescentSystem S hp).v e 1))
        (wholeSpaceSectionsVal hp F m e) := fun m ↦ hE e m
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul b m =>
    rw [System.comparison, semilinearBaseChange_tmul, descentPointTwist_smul, map_smul,
      System.pullStrat_apply, crystalPointMap_twistMap F φ _ h H₀, hE', crysRestrict_comp,
      ← descentPointHom_comp, H₁, descentPointTwist_tmul, crystalPointMap_tmul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **The value in `ℱ(A)` of a descended section read through a pointing** `h : A ⟶ T(0)_e`:
`crystalPointMap h (evalEquiv h z)`.  For the stratification of `ℱ` it does not depend on `h`
(`...SmallSite.stratPointMap_eq`). -/
def stratPointMap {A : AffineCrystallineThickening S} {e : ℕ}
    (h : A ⟶ (wholeSpaceDescentSystem S hp).T0 e) (z : E.sections A) : F.obj.val.obj (op A.obj) :=
  crystalPointMap hp F (descentPointHom h) (descentPointTwist h (E.evalEquiv h z))

/-- `...SmallSite.stratPointMap` does not change under a level map. -/
theorem stratPointMap_lev {A : AffineCrystallineThickening S} {e : ℕ}
    (h : A ⟶ (wholeSpaceDescentSystem S hp).T0 e) (z : E.sections A) :
    stratPointMap E (h ≫ (wholeSpaceDescentSystem S hp).lev e) z = stratPointMap E h z := by
  rw [stratPointMap, stratPointMap, E.evalEquiv_lev, crystalPointMap_lev]

/-- `...SmallSite.stratPointMap` does not change under a composite level map. -/
theorem stratPointMap_levTo {A : AffineCrystallineThickening S} {e : ℕ}
    (h : A ⟶ (wholeSpaceDescentSystem S hp).T0 e) (n : ℕ) (hn : e ≤ n) (z : E.sections A) :
    stratPointMap E (h ≫ (wholeSpaceDescentSystem S hp).levTo e n hn) z = stratPointMap E h z := by
  induction n, hn using Nat.le_induction with
  | base => rw [System.levTo_self, Category.comp_id]
  | succ n hen ih =>
    rw [(wholeSpaceDescentSystem S hp).levTo_succ e n hen, ← Category.assoc, stratPointMap_lev,
      ih]

variable {E} in
/-- **`...SmallSite.stratPointMap` does not depend on the pointing**, for the stratification of
`ℱ`. -/
theorem stratPointMap_eq
    (hE : ∀ e m, crystalPointMap hp F ((wholeSpaceDescentSystem S hp).v e 0).hom (E.str e m) =
      crysRestrict F.obj ((wholeSpaceDescentSystem S hp).v e 1).hom
        (wholeSpaceSectionsVal hp F m e))
    {A : AffineCrystallineThickening S} {e e' : ℕ}
    (h : A ⟶ (wholeSpaceDescentSystem S hp).T0 e) (h' : A ⟶ (wholeSpaceDescentSystem S hp).T0 e')
    (z : E.sections A) : stratPointMap E h z = stratPointMap E h' z := by
  rw [← stratPointMap_levTo E h (max e e') (le_max_left _ _),
    ← stratPointMap_levTo E h' (max e e') (le_max_right _ _), stratPointMap,
    ← E.comparison_evalEquiv _ _ _ ((wholeSpaceDescentSystem S hp).pair_v_zero _ _)
      ((wholeSpaceDescentSystem S hp).pair_v_one _ _),
    crystalPointMap_comparison E hE _ _ _ ((wholeSpaceDescentSystem S hp).pair_v_zero _ _)
      ((wholeSpaceDescentSystem S hp).pair_v_one _ _)]
  rfl

/-- `...SmallSite.stratPointMap` is additive. -/
theorem stratPointMap_add {A : AffineCrystallineThickening S} {e : ℕ}
    (h : A ⟶ (wholeSpaceDescentSystem S hp).T0 e) (z z' : E.sections A) :
    stratPointMap E h (z + z') = stratPointMap E h z + stratPointMap E h z' := by
  simp only [stratPointMap, map_add]

/-- `...SmallSite.stratPointMap` is linear over `Γ(A, 𝒪)`. -/
theorem stratPointMap_smul {A : AffineCrystallineThickening S} {e : ℕ}
    (h : A ⟶ (wholeSpaceDescentSystem S hp).T0 e) (r : (affineSectionsRing S).obj (op A))
    (z : E.sections A) :
    stratPointMap E h (r • z) = RingHom.id (crysSheafRing S A.obj.obj) r • stratPointMap E h z := by
  rw [stratPointMap, stratPointMap, map_smul, descentPointTwist_smul, map_smul]

/-- The restriction of sheaves of `𝒪_{X/S}`-modules from `Cris(X/S)` to its affine subsite, the
functor of `...SmallSite.affineModuleEquivalence`. -/
abbrev crysAffineModuleRestriction :
    SheafOfModules.{u} (structureSheaf S) ⥤ SheafOfModules.{u} (affineStructureSheaf S) :=
  Stacks.DenseSubsiteModules.moduleRestriction (affineTopology S) (smallTopology S)
    (affineι S) (structureSheaf S)

/-- The component over an affine object `A` of the morphism from the descended sheaf to the
restriction of `ℱ`: `...SmallSite.stratPointMap` at the chosen pointing of `A`. -/
def stratAffineLinearMap (A : AffineCrystallineThickening S) :
    (stratAffineSheaf E).val.obj (op A) →ₗ[affineSectionRing A]
      ((crysAffineModuleRestriction (S := S)).obj F.obj).val.obj (op A) where
  toFun z := stratPointMap E (wholeSpaceDescentSystem S hp |>.point A).2 z
  map_add' z z' := stratPointMap_add E _ z z'
  map_smul' r z := stratPointMap_smul E _ r z

/-- `...SmallSite.stratAffineLinearMap` is `...SmallSite.stratPointMap` at the chosen pointing. -/
theorem stratAffineLinearMap_apply (A : AffineCrystallineThickening S) (z : E.sections A) :
    stratAffineLinearMap E A z = stratPointMap E (wholeSpaceDescentSystem S hp |>.point A).2 z :=
  rfl

/-- **`...SmallSite.stratAffineLinearMap` is bijective**, by
`...SmallSite.bijective_crystalPointMap`. -/
theorem bijective_stratAffineLinearMap (A : AffineCrystallineThickening S) :
    Function.Bijective (stratAffineLinearMap E A) :=
  (bijective_crystalPointMap hp F _ A.property).comp
    ((descentPointTwist _).bijective.comp (E.evalEquiv _).bijective)

/-- `...SmallSite.stratAffineLinearMap` as a linear equivalence. -/
def stratAffineLinearEquiv (A : AffineCrystallineThickening S) :
    (stratAffineSheaf E).val.obj (op A) ≃ₗ[affineSectionRing A]
      ((crysAffineModuleRestriction (S := S)).obj F.obj).val.obj (op A) :=
  LinearEquiv.ofBijective (stratAffineLinearMap E A) (bijective_stratAffineLinearMap E A)

/-- **`...SmallSite.stratPointMap` commutes with restriction**: the value at `k ≫ g` of the
restriction of `z` along `k` is the restriction of the value at `g`. -/
theorem stratPointMap_restrict {A B : AffineCrystallineThickening S} (k : A ⟶ B) {e : ℕ}
    (g : B ⟶ (wholeSpaceDescentSystem S hp).T0 e) (z : E.sections B) :
    stratPointMap E (k ≫ g) (E.restrict k z) = crysRestrict F.obj k.hom (stratPointMap E g z) := by
  rw [stratPointMap, stratPointMap, E.evalEquiv_restrict]
  exact crystalPointMap_twistMap F k g (k ≫ g) rfl _

variable {E} in
/-- **`...SmallSite.stratAffineLinearMap` commutes with restriction**, for the stratification of
`ℱ`. -/
theorem stratAffineLinearMap_restrict
    (hE : ∀ e m, crystalPointMap hp F ((wholeSpaceDescentSystem S hp).v e 0).hom (E.str e m) =
      crysRestrict F.obj ((wholeSpaceDescentSystem S hp).v e 1).hom
        (wholeSpaceSectionsVal hp F m e))
    {A B : AffineCrystallineThickening S} (k : A ⟶ B) (z : E.sections B) :
    stratAffineLinearMap E A (E.restrict k z) =
      crysRestrict F.obj k.hom (stratAffineLinearMap E B z) := by
  rw [stratAffineLinearMap_apply, stratAffineLinearMap_apply,
    stratPointMap_eq hE _ (k ≫ ((wholeSpaceDescentSystem S hp).point B).2),
    stratPointMap_restrict]

variable {E} in
/-- **On the affine subsite, the descended sheaf of the stratification of `ℱ` is the restriction of
`ℱ`.** -/
def stratAffineIso
    (hE : ∀ e m, crystalPointMap hp F ((wholeSpaceDescentSystem S hp).v e 0).hom (E.str e m) =
      crysRestrict F.obj ((wholeSpaceDescentSystem S hp).v e 1).hom
        (wholeSpaceSectionsVal hp F m e)) :
    stratAffineSheaf E ≅ (crysAffineModuleRestriction (S := S)).obj F.obj :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun X ↦ (stratAffineLinearEquiv E X.unop).toModuleIso)
      (fun X Y f ↦ by
        ext z
        exact stratAffineLinearMap_restrict hE f.unop z))

variable {E} in
/-- **The sheaf of the stratification of `ℱ` is `ℱ`**: the isomorphism
`...SmallSite.stratAffineIso` of restrictions to the affine subsite, carried back along the
restriction, which is fully faithful. -/
def stratSheafIso
    (hE : ∀ e m, crystalPointMap hp F ((wholeSpaceDescentSystem S hp).v e 0).hom (E.str e m) =
      crysRestrict F.obj ((wholeSpaceDescentSystem S hp).v e 1).hom
        (wholeSpaceSectionsVal hp F m e)) :
    stratSheaf E ≅ F.obj :=
  (crysAffineModuleRestriction (S := S)).preimageIso
    (affineModuleEquivalenceInverseObjRestrictionIso S (stratAffineSheaf E) ≪≫
      stratAffineIso hE)

variable (F) in
/-- **A quasi-coherent crystal is the crystal of its stratification**: for the stratification `E`
of `M = lim_e Γ(T(0)_e, ℱ)` given by `ℱ` (the hypothesis `hE`), `stratCrystal E ≅ ℱ`. -/
def stratCrystalIso
    (hE : ∀ e m, crystalPointMap hp F ((wholeSpaceDescentSystem S hp).v e 0).hom (E.str e m) =
      crysRestrict F.obj ((wholeSpaceDescentSystem S hp).v e 1).hom
        (wholeSpaceSectionsVal hp F m e)) :
    stratCrystal E ≅ F :=
  ObjectProperty.isoMk _ (stratSheafIso hE)

variable {E} in
/-- The component of `...SmallSite.stratSheafIso` over an affine object, read through any
pointing. -/
theorem stratSheafIso_hom_app
    (hE : ∀ e m, crystalPointMap hp F ((wholeSpaceDescentSystem S hp).v e 0).hom (E.str e m) =
      crysRestrict F.obj ((wholeSpaceDescentSystem S hp).v e 1).hom
        (wholeSpaceSectionsVal hp F m e))
    (A : AffineCrystallineThickening S) {e : ℕ} (h : A ⟶ (wholeSpaceDescentSystem S hp).T0 e)
    (x : (stratSheaf E).val.obj (op A.obj)) :
    ((stratSheafIso hE).hom.val.app (op A.obj)).hom x =
      crystalPointMap hp F (descentPointHom h)
        (descentPointTwist h (E.evalEquiv h (stratSectionsEquiv E A x))) := by
  have key : (crysAffineModuleRestriction (S := S)).map (stratSheafIso hE).hom =
      (affineModuleEquivalenceInverseObjRestrictionIso S (stratAffineSheaf E) ≪≫
        stratAffineIso hE).hom :=
    Functor.map_preimage _ _
  have hx : ((stratSheafIso hE).hom.val.app (op A.obj)).hom x =
      (((crysAffineModuleRestriction (S := S)).map (stratSheafIso hE).hom).val.app
        (op A)).hom x := rfl
  rw [hx, key]
  exact stratPointMap_eq hE _ h _

/-- **The component of `...SmallSite.stratCrystalIso` over an affine object `A`**, read through any
pointing `h : A ⟶ T(0)_e`, is `crystalPointMap h ∘ evalEquiv h ∘ stratSectionsEquiv E A`. -/
theorem stratCrystalIso_hom_app
    (hE : ∀ e m, crystalPointMap hp F ((wholeSpaceDescentSystem S hp).v e 0).hom (E.str e m) =
      crysRestrict F.obj ((wholeSpaceDescentSystem S hp).v e 1).hom
        (wholeSpaceSectionsVal hp F m e))
    (A : AffineCrystallineThickening S) {e : ℕ} (h : A ⟶ (wholeSpaceDescentSystem S hp).T0 e)
    (x : (stratCrystal E).obj.val.obj (op A.obj)) :
    ((stratCrystalIso F E hE).hom.hom.val.app (op A.obj)).hom x =
      crystalPointMap hp F h.hom (E.evalEquiv h (stratSectionsEquiv E A x)) :=
  stratSheafIso_hom_app hE A h x

/-- Two morphisms of sheaves of `𝒪_{X/S}`-modules agreeing on the sections over the affine objects
are equal. -/
theorem sheafOfModules_hom_ext_affine {P Q : SheafOfModules.{u} (structureSheaf S)} {f g : P ⟶ Q}
    (H : ∀ (A : AffineCrystallineThickening S) (x : P.val.obj (op A.obj)),
      (f.val.app (op A.obj)).hom x = (g.val.app (op A.obj)).hom x) : f = g :=
  (crysAffineModuleRestriction (S := S)).map_injective (SheafOfModules.hom_ext
    (PresheafOfModules.hom_ext fun X ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦ H X.unop x)))

/-- The components of a composite of morphisms of sheaves of modules, on elements. -/
theorem sheafOfModules_comp_app_apply {P Q R : SheafOfModules.{u} (structureSheaf S)}
    (f : P ⟶ Q) (g : Q ⟶ R) (X : (CrystallineThickening S)ᵒᵖ) (x : P.val.obj X) :
    ((f ≫ g).val.app X).hom x = (g.val.app X).hom ((f.val.app X).hom x) :=
  rfl

/-- `...SmallSite.stratSectionsEquiv` is natural in the descended sheaf. -/
theorem stratSectionsEquiv_map {M M' : Type u} [AddCommGroup M] [Module (envD S hp) M]
    [AddCommGroup M'] [Module (envD S hp) M'] {E₁ : Stratification (wholeSpaceDescentSystem S hp) M}
    {E₂ : Stratification (wholeSpaceDescentSystem S hp) M'}
    (β : stratAffineSheaf E₁ ⟶ stratAffineSheaf E₂) (A : AffineCrystallineThickening S)
    (x : (stratSheaf E₁).val.obj (op A.obj)) :
    stratSectionsEquiv E₂ A ((((affineModuleEquivalence S).inverse.map β).val.app
      (op A.obj)).hom x) = (β.val.app (op A)).hom (stratSectionsEquiv E₁ A x) :=
  congr_arg (fun f ↦ (f.val.app (op A)).hom x) ((affineModuleEquivalence S).counit_naturality β)

/-- `...SmallSite.stratSectionsEquiv` intertwines the map of crystals induced by a map of
stratified modules with `mapSections`. -/
theorem stratSectionsEquiv_presheafMap {M M' : Type u} [AddCommGroup M] [Module (envD S hp) M]
    [AddCommGroup M'] [Module (envD S hp) M'] (E₁ : Stratification (wholeSpaceDescentSystem S hp) M)
    (E₂ : Stratification (wholeSpaceDescentSystem S hp) M') (φ : M →ₗ[envD S hp] M')
    (hφ : ∀ e m, E₂.str e (φ m) = LinearMap.lTensor _ φ (E₁.str e m))
    (A : AffineCrystallineThickening S) (x : (stratSheaf E₁).val.obj (op A.obj)) :
    stratSectionsEquiv E₂ A ((((affineModuleEquivalence S).inverse.map
      (⟨E₁.presheafMap E₂ φ hφ⟩ : stratAffineSheaf E₁ ⟶ stratAffineSheaf E₂)).val.app
        (op A.obj)).hom x) = E₁.mapSections E₂ φ hφ A (stratSectionsEquiv E₁ A x) :=
  stratSectionsEquiv_map _ A x

/-- `...SmallSite.stratSheafIso` is natural in the pair `(ℱ, E)`. -/
theorem stratSheafIso_naturality {G : QuasiCoherentCrystal S}
    {E' : Stratification (wholeSpaceDescentSystem S hp) (wholeSpaceSections hp G ⦋0⦌)}
    (hE : ∀ e m, crystalPointMap hp F ((wholeSpaceDescentSystem S hp).v e 0).hom (E.str e m) =
      crysRestrict F.obj ((wholeSpaceDescentSystem S hp).v e 1).hom
        (wholeSpaceSectionsVal hp F m e))
    (hE' : ∀ e m, crystalPointMap hp G ((wholeSpaceDescentSystem S hp).v e 0).hom (E'.str e m) =
      crysRestrict G.obj ((wholeSpaceDescentSystem S hp).v e 1).hom
        (wholeSpaceSectionsVal hp G m e))
    (ψ : F ⟶ G)
    (hφ : ∀ e m, E'.str e (wholeSpaceSectionsLinearMap hp ψ m) =
      LinearMap.lTensor _ (wholeSpaceSectionsLinearMap hp ψ) (E.str e m)) :
    (affineModuleEquivalence S).inverse.map
        (⟨E.presheafMap E' (wholeSpaceSectionsLinearMap hp ψ) hφ⟩ :
          stratAffineSheaf E ⟶ stratAffineSheaf E') ≫ (stratSheafIso hE').hom =
      (stratSheafIso hE).hom ≫ ψ.hom := by
  refine sheafOfModules_hom_ext_affine fun A x ↦ ?_
  have h := ((wholeSpaceDescentSystem S hp).point A).2
  refine (sheafOfModules_comp_app_apply _ _ _ x).trans
    (Eq.trans ?_ (sheafOfModules_comp_app_apply _ _ _ x).symm)
  refine (stratSheafIso_hom_app hE' A h _).trans ?_
  refine Eq.trans ?_ (congrArg (ψ.hom.val.app (op A.obj)).hom (stratSheafIso_hom_app hE A h x)).symm
  refine Eq.trans ?_ (crystalPointMap_naturality hp (descentPointHom h) ψ _).symm
  exact congrArg (fun y ↦ crystalPointMap hp G (descentPointHom h)
    (descentPointTwist h (E'.evalEquiv h y))) (stratSectionsEquiv_presheafMap E E' _ hφ A x)

/-- **`...SmallSite.stratCrystalIso` is natural in the pair `(ℱ, E)`**: for `ψ : ℱ ⟶ 𝒢` and a map
`φ : M(ℱ) → M(𝒢)` commuting with the stratifications and equal to the map induced by `ψ`, the
square formed by `stratCrystalFunctor.map φ`, the two isomorphisms and `ψ` commutes. -/
theorem stratCrystalIso_naturality {G : QuasiCoherentCrystal S}
    {E' : Stratification (wholeSpaceDescentSystem S hp) (wholeSpaceSections hp G ⦋0⦌)}
    (hE : ∀ e m, crystalPointMap hp F ((wholeSpaceDescentSystem S hp).v e 0).hom (E.str e m) =
      crysRestrict F.obj ((wholeSpaceDescentSystem S hp).v e 1).hom
        (wholeSpaceSectionsVal hp F m e))
    (hE' : ∀ e m, crystalPointMap hp G ((wholeSpaceDescentSystem S hp).v e 0).hom (E'.str e m) =
      crysRestrict G.obj ((wholeSpaceDescentSystem S hp).v e 1).hom
        (wholeSpaceSectionsVal hp G m e))
    (ψ : F ⟶ G) (φ : wholeSpaceSections hp F ⦋0⦌ →ₗ[envD S hp] wholeSpaceSections hp G ⦋0⦌)
    (hφ : ∀ e m, E'.str e (φ m) = LinearMap.lTensor _ φ (E.str e m))
    (hψ : ∀ m, φ m = wholeSpaceSectionsLinearMap hp ψ m) :
    stratCrystalFunctor.map (X := StratModule.mk _ E) (Y := StratModule.mk _ E') ⟨φ, hφ⟩ ≫
        (stratCrystalIso G E' hE').hom = (stratCrystalIso F E hE).hom ≫ ψ := by
  obtain rfl : φ = wholeSpaceSectionsLinearMap hp ψ := LinearMap.ext hψ
  exact ObjectProperty.hom_ext _ (stratSheafIso_naturality E hE hE' ψ hφ)

end Crystalline.GlobalCrystallineSituation.SmallSite

end
