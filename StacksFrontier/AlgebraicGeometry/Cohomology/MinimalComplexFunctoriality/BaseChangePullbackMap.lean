module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangePasting
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionAlongAComposite

/-!
# Base change of the pullback map on derived direct images

Let `i : X ⟶ P` be a morphism of ringed spaces over `p : P ⟶ S`, and let

```
X' --gX--> X
|i'        |i
P' --gP--> P
|p'        |p
S' --g---> S
```

be two commutative squares. For `K ∈ D(𝒪_P)` there is the *pullback map*

`Rp_* K ⟶ Rp_* Ri_* Li^* K ≅ R(i ≫ p)_* Li^* K`,

`Rp_*` of the unit of `Li^* ⊣ Ri_*` followed by the composition isomorphism of Tag 079W. It is the
map "by functoriality of cohomology" `E ⟶ E_i` of the proofs of
[Stacks, Tag 0BF1](https://stacks.math.columbia.edu/tag/0BF1) and
[Stacks, Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2), and the source asserts that its
formation commutes with change of base. This file proves that assertion, in the form of a
commutative square with the derived base change maps of Tag 08HY of the lower square and of the
outer rectangle.

## Main results

* `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_pullbackMap`: the derived pullback
  along `g` of the pullback map, followed by the base change map of the rectangle, is the base
  change map of the lower square followed by the pullback map along `i'` and the comparison
  `Li'^* LgP^* K ≅ LgX^* Li^* K` of the upper square.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace Stacks.Cohomology.DerivedBaseChange

attribute [local instance 10000] HasDerivedCategory.standard

section Abstract

variable {CS CS' CP CP' CX CX' : Type*} [Category CS] [Category CS'] [Category CP]
  [Category CP'] [Category CX] [Category CX']

/-- An abstract form of `derivedBaseChangeMap_pullbackMap`, with every functor a variable: if the
rectangle's base change map `bB` is the pasting `hB` of the lower square's `bA` and the upper
square's `bC`, `bA` is natural (`hA`) and `bC` is compatible with the units of `adjI` and `adjI'`
through `αK` (`hC`), then `Lg` of the unit followed by `cI` and `bB` equals `bA` followed by the
unit of `adjI'`, `cI'` and `RIP'.map αK`. -/
theorem pullbackMap_chase (Lg : CS ⥤ CS') (LgP : CP ⥤ CP') (LgX : CX ⥤ CX')
    (Rp : CP ⥤ CS) (Rp' : CP' ⥤ CS') {Li : CP ⥤ CX} {Ri : CX ⥤ CP} {Li' : CP' ⥤ CX'}
    {Ri' : CX' ⥤ CP'} (adjI : Li ⊣ Ri) (adjI' : Li' ⊣ Ri') (RIP : CX ⥤ CS) (RIP' : CX' ⥤ CS')
    (cI : Ri ⋙ Rp ≅ RIP) (cI' : Ri' ⋙ Rp' ≅ RIP')
    (bA : ∀ Y : CP, Lg.obj (Rp.obj Y) ⟶ Rp'.obj (LgP.obj Y))
    (hA : ∀ {Y Y' : CP} (v : Y ⟶ Y'), Lg.map (Rp.map v) ≫ bA Y' = bA Y ≫ Rp'.map (LgP.map v))
    (K : CP) (bC : LgP.obj (Ri.obj (Li.obj K)) ⟶ Ri'.obj (LgX.obj (Li.obj K)))
    (αK : Li'.obj (LgP.obj K) ⟶ LgX.obj (Li.obj K))
    (hC : LgP.map (adjI.unit.app K) ≫ bC = adjI'.unit.app (LgP.obj K) ≫ Ri'.map αK)
    (bB : Lg.obj (RIP.obj (Li.obj K)) ⟶ RIP'.obj (LgX.obj (Li.obj K)))
    (hB : Lg.map (cI.inv.app (Li.obj K)) ≫ bA (Ri.obj (Li.obj K)) ≫
      Rp'.map bC ≫ cI'.hom.app (LgX.obj (Li.obj K)) = bB) :
    Lg.map (Rp.map (adjI.unit.app K) ≫ cI.hom.app (Li.obj K)) ≫ bB =
      bA K ≫ (Rp'.map (adjI'.unit.app (LgP.obj K)) ≫ cI'.hom.app (Li'.obj (LgP.obj K))) ≫
        RIP'.map αK := by
  subst hB
  have hnat := hA (adjI.unit.app K)
  have hc := cI'.hom.naturality αK
  simp only [Functor.comp_map] at hc
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc Lg (cI.hom.app (Li.obj K)), Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, reassoc_of% hnat,
    ← Functor.map_comp_assoc Rp', hC, Functor.map_comp, Category.assoc]
  exact congrArg (fun t => bA K ≫ Rp'.map (adjI'.unit.app (LgP.obj K)) ≫ t) hc

/-- `CategoryTheory.unit_mateEquiv`, with the identity functor evaluated away and the
components written through `TwoSquare.natTrans`. -/
theorem unit_mateEquiv_natTrans_app {C D E F : Type*} [Category C] [Category D] [Category E]
    [Category F] {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : TwoSquare G L₁ L₂ H) (c : C) :
    G.map (adj₁.unit.app c) ≫ (mateEquiv adj₁ adj₂ α).natTrans.app (L₁.obj c) =
      adj₂.unit.app (G.obj c) ≫ R₂.map (α.natTrans.app c) :=
  unit_mateEquiv adj₁ adj₂ α c

end Abstract

variable {X' X P' P S' S : RingedSpace.{u, u}} (i : X ⟶ P) (p : P ⟶ S) (i' : X' ⟶ P')
  (p' : P' ⟶ S') (gX : X' ⟶ X) (gP : P' ⟶ P) (g : S' ⟶ S)

/-- **The pullback map commutes with derived base change.** For two vertically composable
commutative squares as in the module documentation and `K ∈ D(𝒪_P)`,

`Lg^*(Rp_* K ⟶ R(i ≫ p)_* Li^* K)` followed by the base change map of the rectangle equals the base
change map of the lower square followed by the pullback map along `i'` at `LgP^* K` and by
`R(i' ≫ p')_*` of the comparison `Li'^* LgP^* K ⟶ LgX^* Li^* K` of the upper square. -/
theorem derivedBaseChangeMap_pullbackMap (sqC : gX ≫ i = i' ≫ gP) (sqA : gP ≫ p = p' ≫ g)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing P))) :
    (derivedPullback g).map ((derivedPushforward p).map ((derivedAdjunction i).unit.app K) ≫
        (derivedPushforwardCompIso i p).hom.app ((derivedPullback i).obj K)) ≫
      derivedBaseChangeMap gX (i' ≫ p') (i ≫ p) g (comp_square gX i' i gP p' p g sqC sqA)
        ((derivedPullback i).obj K) =
    derivedBaseChangeMap gP p' p g sqA K ≫
      ((derivedPushforward p').map ((derivedAdjunction i').unit.app ((derivedPullback gP).obj K)) ≫
        (derivedPushforwardCompIso i' p').hom.app
          ((derivedPullback i').obj ((derivedPullback gP).obj K))) ≫
      (derivedPushforward (i' ≫ p')).map
        ((derivedPullbackSquare gX i' i gP sqC).natTrans.app K) := by
  have hC : (derivedPullback gP).map ((derivedAdjunction i).unit.app K) ≫
      derivedBaseChangeMap gX i' i gP sqC ((derivedPullback i).obj K) =
      (derivedAdjunction i').unit.app ((derivedPullback gP).obj K) ≫
        (derivedPushforward i').map ((derivedPullbackSquare gX i' i gP sqC).natTrans.app K) := by
    rw [show derivedBaseChangeMap gX i' i gP sqC ((derivedPullback i).obj K) =
        (derivedBaseChangeSquare gX i' i gP sqC).natTrans.app ((derivedPullback i).obj K) from rfl,
      derivedBaseChangeSquare_eq_mateEquiv]
    exact unit_mateEquiv_natTrans_app (derivedAdjunction i) (derivedAdjunction i')
      (derivedPullbackSquare gX i' i gP sqC) K
  exact pullbackMap_chase (derivedPullback g) (derivedPullback gP) (derivedPullback gX)
    (derivedPushforward p) (derivedPushforward p') (derivedAdjunction i) (derivedAdjunction i')
    (derivedPushforward (i ≫ p)) (derivedPushforward (i' ≫ p')) (derivedPushforwardCompIso i p)
    (derivedPushforwardCompIso i' p') (fun Y => derivedBaseChangeMap gP p' p g sqA Y)
    (fun v => derivedBaseChangeMap_naturality gP p' p g sqA v) K _ _ hC _
    (derivedBaseChangeMap_comp gX i' i gP p' p g sqC sqA ((derivedPullback i).obj K))

end Stacks.Cohomology.DerivedBaseChange

end
