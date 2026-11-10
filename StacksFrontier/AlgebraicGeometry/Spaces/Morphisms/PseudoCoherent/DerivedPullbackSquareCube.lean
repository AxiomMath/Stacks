module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativelyPerfectHomDescentLocalization

/-!
# The identifications of the faces of a commutative cube of derived pullbacks

A pseudofunctoriality datum `P` for the derived pullback of modules on the small étale ringed
topoi of algebraic spaces (`AlgebraicGeometry.Space.DerivedPullbackComposition`) attaches to every
commutative square `u' ≫ t = t' ≫ u` the identification
`P.squareIso u' t t' u : Lu^* ⋙ Lt'^* ≅ Lt^* ⋙ Lu'^*`.  This file records that these
identifications paste coherently around a commutative cube

```
P' --snd'--> V'            P --snd--> V
|fst'        |etale'       |fst       |etale
v            v             v          v
U' --open'-> W'  --p-->    U --open-> W
```

whose vertical faces are given by `pU : U' ⟶ U`, `pV : V' ⟶ V` and `pP : P' ⟶ P`: going around
the four faces through `U` and `P` from `Lfst'^* Lopen'^* Lp^*` to `Lsnd'^* LpV^* Letale^*` is
going through the top face and the face through `V`.  Both are the identification of the two
threefold composites with the derived pullback along the diagonal of the cube, by the
associativity coherence of `P`.

This is the bookkeeping needed to compare glueing data of an elementary distinguished square
with their derived pullbacks along a base change of the square.

## Main results

* `AlgebraicGeometry.Space.DerivedPullbackComposition.iso_hom_app_comp_iso_hom_app`: the
  associativity coherence of `P` on components.
* `AlgebraicGeometry.Space.DerivedPullbackComposition.squareIso_cube`: the pasting identity.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] SheafOfModules.instAbelian
attribute [local instance 3000] Abelian.toPreadditive

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace DerivedPullbackComposition

variable (P : DerivedPullbackComposition B S hS)

/-- **The associativity coherence of a pseudofunctoriality datum, on components.** -/
theorem iso_hom_app_comp_iso_hom_app {V W Y Z : AlgebraicSpaces B S hS} (p : V ⟶ W) (t : W ⟶ Y)
    (a : Y ⟶ Z) (b : W ⟶ Z) (q : V ⟶ Y) (c : V ⟶ Z) (hb : t ≫ a = b) (hq : p ≫ t = q)
    (hc : q ≫ a = c) (hpb : p ≫ b = c)
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))) :
    (P.iso p t q hq).hom.app ((smallEtaleDerivedModulePullback B S hS a).obj M) ≫
        (P.iso q a c hc).hom.app M =
      (smallEtaleDerivedModulePullback B S hS p).map ((P.iso t a b hb).hom.app M) ≫
        (P.iso p b c hpb).hom.app M := by
  simpa using congrArg Iso.hom (P.iso_assoc p t a b q c hb hq hc hpb M)

/-- **The identifications of the faces of a commutative cube paste coherently.**  For a
commutative cube of algebraic spaces with top face `snd' ≫ etale' = fst' ≫ open'`, bottom face
`snd ≫ etale = fst ≫ open`, and vertical maps `p`, `pU`, `pV`, `pP`, the two composites of face
identifications from `Lfst'^*(Lopen'^*(Lp^* F))` to `Lsnd'^*(LpV^*(Letale^* F))` agree. -/
theorem squareIso_cube {P' U' V' W' Pb U V W : AlgebraicSpaces B S hS}
    (fst' : P' ⟶ U') (snd' : P' ⟶ V') (open' : U' ⟶ W') (etale' : V' ⟶ W')
    (fst : Pb ⟶ U) (snd : Pb ⟶ V) (open_ : U ⟶ W) (etale : V ⟶ W)
    (p : W' ⟶ W) (pU : U' ⟶ U) (pV : V' ⟶ V) (pP : P' ⟶ Pb)
    (h₀' : snd' ≫ etale' = fst' ≫ open') (h₀ : snd ≫ etale = fst ≫ open_)
    (hU : open' ≫ p = pU ≫ open_) (hV : etale' ≫ p = pV ≫ etale)
    (hPU : fst' ≫ pU = pP ≫ fst) (hPV : snd' ≫ pV = pP ≫ snd)
    (F : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS W))) :
    (smallEtaleDerivedModulePullback B S hS fst').map
        ((P.squareIso open' p pU open_ hU).inv.app F) ≫
      (P.squareIso fst' pU pP fst hPU).inv.app
        ((smallEtaleDerivedModulePullback B S hS open_).obj F) ≫
      (smallEtaleDerivedModulePullback B S hS pP).map
        ((P.squareIso snd etale fst open_ h₀).hom.app F) ≫
      (P.squareIso snd' pV pP snd hPV).hom.app
        ((smallEtaleDerivedModulePullback B S hS etale).obj F) =
    (P.squareIso snd' etale' fst' open' h₀').hom.app
        ((smallEtaleDerivedModulePullback B S hS p).obj F) ≫
      (smallEtaleDerivedModulePullback B S hS snd').map
        ((P.squareIso etale' p pV etale hV).inv.app F) := by
  -- the diagonal of the cube
  let m := open' ≫ p
  let e := etale' ≫ p
  let T := fst' ≫ m
  have hT : snd' ≫ e = T := by
    simp only [e, T, m, ← Category.assoc, h₀']
  have hsT : (snd' ≫ etale') ≫ p = T := by
    simp only [T, m, h₀', Category.assoc]
  have hnT : (snd' ≫ pV) ≫ etale = T := by
    rw [Category.assoc, ← hV, ← Category.assoc, h₀', Category.assoc]
  have hsnT : pP ≫ (snd ≫ etale) = T := by
    rw [← Category.assoc, ← hPV, Category.assoc, ← hV, ← Category.assoc, h₀', Category.assoc]
  have hrT : (fst' ≫ pU) ≫ open_ = T := by
    rw [Category.assoc, ← hU]
  -- the identification of both sides with the derived pullback along the diagonal
  let Ψ := (smallEtaleDerivedModulePullback B S hS snd').map
      ((P.iso pV etale e hV.symm).hom.app F) ≫ (P.iso snd' e T hT).hom.app F
  let Ψiso := (smallEtaleDerivedModulePullback B S hS snd').mapIso
      ((P.iso pV etale e hV.symm).app F) ≪≫ (P.iso snd' e T hT).app F
  refine (Iso.cancel_iso_hom_right _ _ Ψiso).1 ?_
  change _ ≫ Ψ = _ ≫ Ψ
  have hR₁ : (smallEtaleDerivedModulePullback B S hS snd').map
        ((P.squareIso etale' p pV etale hV).inv.app F) ≫ Ψ =
      (P.iso snd' etale' (snd' ≫ etale') rfl).hom.app
          ((smallEtaleDerivedModulePullback B S hS p).obj F) ≫
        (P.iso (snd' ≫ etale') p T hsT).hom.app F := by
    dsimp only [Ψ]
    rw [P.iso_hom_app_comp_iso_hom_app snd' etale' p e (snd' ≫ etale') T rfl rfl hsT hT,
      ← Functor.map_comp_assoc]
    congr 2
    simp [squareIso, e]
  have hL₁ : (P.squareIso snd' pV pP snd hPV).hom.app
        ((smallEtaleDerivedModulePullback B S hS etale).obj F) ≫ Ψ =
      (smallEtaleDerivedModulePullback B S hS pP).map
          ((P.iso snd etale (snd ≫ etale) rfl).hom.app F) ≫
        (P.iso pP (snd ≫ etale) T hsnT).hom.app F := by
    dsimp only [Ψ]
    rw [← P.iso_hom_app_comp_iso_hom_app snd' pV etale e (snd' ≫ pV) T hV.symm rfl hnT hT,
      ← P.iso_hom_app_comp_iso_hom_app pP snd etale (snd ≫ etale) (snd' ≫ pV) T rfl
        hPV.symm hnT hsnT]
    simp [squareIso]
  have hL₂ : (P.squareIso fst' pU pP fst hPU).inv.app
        ((smallEtaleDerivedModulePullback B S hS open_).obj F) ≫
      (smallEtaleDerivedModulePullback B S hS pP).map
          ((P.squareIso snd etale fst open_ h₀).hom.app F) ≫
      (smallEtaleDerivedModulePullback B S hS pP).map
          ((P.iso snd etale (snd ≫ etale) rfl).hom.app F) ≫
        (P.iso pP (snd ≫ etale) T hsnT).hom.app F =
      (smallEtaleDerivedModulePullback B S hS fst').map
          ((P.iso pU open_ m hU.symm).hom.app F) ≫ (P.iso fst' m T rfl).hom.app F := by
    rw [← Functor.map_comp_assoc]
    have hκ : (P.squareIso snd etale fst open_ h₀).hom.app F ≫
        (P.iso snd etale (snd ≫ etale) rfl).hom.app F =
        (P.iso fst open_ (snd ≫ etale) h₀.symm).hom.app F := by
      simp [squareIso]
    rw [hκ, ← P.iso_hom_app_comp_iso_hom_app pP fst open_ (snd ≫ etale) (fst' ≫ pU) T h₀.symm
      hPU.symm hrT hsnT]
    simp only [squareIso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Category.assoc,
      Iso.inv_hom_id_app_assoc]
    exact P.iso_hom_app_comp_iso_hom_app fst' pU open_ m (fst' ≫ pU) T hU.symm rfl hrT rfl F
  have hR₂ : (P.squareIso snd' etale' fst' open' h₀').hom.app
        ((smallEtaleDerivedModulePullback B S hS p).obj F) ≫
      (P.iso snd' etale' (snd' ≫ etale') rfl).hom.app
          ((smallEtaleDerivedModulePullback B S hS p).obj F) ≫
        (P.iso (snd' ≫ etale') p T hsT).hom.app F =
      (smallEtaleDerivedModulePullback B S hS fst').map
          ((P.iso open' p m rfl).hom.app F) ≫ (P.iso fst' m T rfl).hom.app F := by
    rw [← P.iso_hom_app_comp_iso_hom_app fst' open' p m (snd' ≫ etale') T rfl h₀'.symm hsT rfl]
    simp [squareIso]
  have hL₃ : (smallEtaleDerivedModulePullback B S hS fst').map
        ((P.squareIso open' p pU open_ hU).inv.app F) ≫
      (smallEtaleDerivedModulePullback B S hS fst').map
          ((P.iso pU open_ m hU.symm).hom.app F) =
      (smallEtaleDerivedModulePullback B S hS fst').map ((P.iso open' p m rfl).hom.app F) := by
    rw [← Functor.map_comp]
    congr 1
    simp [squareIso, m]
  simp only [Category.assoc]
  rw [hL₁, hL₂, ← Category.assoc, hL₃, hR₁, ← hR₂]

end DerivedPullbackComposition

end AlgebraicGeometry.Space

end
