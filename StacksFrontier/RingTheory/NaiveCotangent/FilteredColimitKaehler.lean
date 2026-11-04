module

public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Kaehler.Basic
public import StacksFrontier.RingTheory.NaiveCotangent.FilteredColimitH1
public import StacksFrontier.RingTheory.NaiveCotangent.H1IndEtaleSquare

/-!
# Kähler differentials along a commutative square, a filtered colimit and an ind-étale square

A commutative square of ring maps
```
R ──fR──▸ R'
│          │
▼          ▼
S ──fS──▸ S'
```
induces an additive map `Ω_{S/R} → Ω_{S'/R'}`, `d s ↦ d (fS s)`.  This file defines that map
for a square given by bare ring homomorphisms, in the same way as `h1CotangentMapOfSquare` does
for `H₁` of the naive cotangent complex, and proves two facts about it: compatibility with
filtered colimits, and base change along a square of ind-étale maps.

## Main definitions

* `Stacks.NaiveCotangent.kaehlerMapOfSquare`: the map `Ω_{S/R} → Ω_{S'/R'}` of a square.
* `Stacks.NaiveCotangent.kaehlerBaseChangeOfSquare`: its `A'`-linear extension
  `A' ⊗_A Ω_{A/R} → Ω_{A'/R'}`, `a' ⊗ ω ↦ a' • kaehlerMapOfSquare ω`.

## Main results

* `Stacks.NaiveCotangent.kaehlerMapOfSquare_comp`, `Stacks.NaiveCotangent.kaehlerMapOfSquare_id`:
  functoriality in the square.
* `Stacks.NaiveCotangent.exists_kaehlerMapOfSquare_eq_zero_of_isColimit`: a differential of a
  stage of a filtered diagram which vanishes in the colimit already vanishes at a later stage.
* `Stacks.NaiveCotangent.bijective_kaehlerMapOfSquare_liftBaseChange_of_ind_etale`: along a square
  whose horizontal maps are filtered colimits of étale maps, `A' ⊗_A Ω_{A/R} → Ω_{A'/R'}` is
  bijective.

## Implementation notes

The map is defined by installing the square as `Algebra` instances with `letI` and applying
`KaehlerDifferential.map`.  Every further property is derived from its value
`kaehlerMapOfSquare_D` on the generators `d s` and its semilinearity `kaehlerMapOfSquare_smul`,
by induction over the generators, so that no two `Algebra` instances on the same pair of rings
are ever compared.

The filtered-colimit statement is reduced to a directed system of rings exactly as
`exists_h1CotangentMapOfSquare_eq_zero_of_isColimit` is.  There a differential `z` of a stage is
the image `toKaehler w` of an element `w` of the cotangent space of the canonical presentation;
vanishing of `z` in the limit puts the image of `w` in the image of the differential of the
limit's naive cotangent complex, which comes from a stage (`comparisonCotangent_surjective`), and
injectivity of the comparison in degree `0` (`comparisonCotangentSpace_injective`) moves the
resulting identity to a later stage.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Algebra TensorProduct

universe w v u

namespace Stacks.NaiveCotangent

section Induction

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- **Induction over the generators of the Kähler differentials.**  A property of elements of
`Ω_{S/R}` which holds for every `d s`, for `0`, and is stable under sums and under multiplication
by elements of `S`, holds for every element. -/
theorem kaehlerDifferential_induction {P : Ω[S⁄R] → Prop}
    (D : ∀ s : S, P (KaehlerDifferential.D R S s)) (zero : P 0)
    (add : ∀ x y, P x → P y → P (x + y)) (smul : ∀ (s : S) x, P x → P (s • x))
    (x : Ω[S⁄R]) : P x := by
  have hx : x ∈ Submodule.span S (Set.range (KaehlerDifferential.D R S)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨s, rfl⟩ := hy
    exact D s
  | zero => exact zero
  | add y z _ _ hy hz => exact add y z hy hz
  | smul s y _ hy => exact smul s y hy

/-- **Induction over the basis of the cotangent space of the canonical presentation.**  A
property of elements of `S ⊗_{R[S]} Ω_{R[S]/R}` which holds for every basis vector `d[s]`, for
`0`, and is stable under sums and under multiplication by elements of `S`, holds for every
element. -/
theorem cotangentSpace_induction
    {P : (Generators.self R S).toExtension.CotangentSpace → Prop}
    (basis : ∀ b : S, P ((Generators.self R S).cotangentSpaceBasis b)) (zero : P 0)
    (add : ∀ x y, P x → P y → P (x + y)) (smul : ∀ (s : S) x, P x → P (s • x))
    (x : (Generators.self R S).toExtension.CotangentSpace) : P x := by
  have hx : x ∈ Submodule.span S (Set.range (Generators.self R S).cotangentSpaceBasis) :=
    (Generators.self R S).cotangentSpaceBasis.mem_span x
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, rfl⟩ := hy
    exact basis b
  | zero => exact zero
  | add y z _ _ hy hz => exact add y z hy hz
  | smul s y _ hy => exact smul s y hy

end Induction

section Square

variable {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
  [Algebra R S] [Algebra R' S']

section Map

variable (fR : R →+* R') (fS : S →+* S')
  (h : ∀ r : R, fS (algebraMap R S r) = algebraMap R' S' (fR r))

/-- The map `Ω_{S/R} → Ω_{S'/R'}` of Kähler differentials induced by a commutative square of
ring maps, `d s ↦ d (fS s)`. -/
noncomputable def kaehlerMapOfSquare : Ω[S⁄R] →+ Ω[S'⁄R'] :=
  letI := fR.toAlgebra
  letI := fS.toAlgebra
  letI := (fS.comp (algebraMap R S)).toAlgebra
  haveI : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq fun r => h r
  haveI : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  (KaehlerDifferential.map R R' S S').toAddMonoidHom

/-- **The map of a square on generators.** -/
theorem kaehlerMapOfSquare_D (s : S) :
    kaehlerMapOfSquare fR fS h (KaehlerDifferential.D R S s) =
      KaehlerDifferential.D R' S' (fS s) := by
  let := fR.toAlgebra
  let := fS.toAlgebra
  let := (fS.comp (algebraMap R S)).toAlgebra
  have : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq fun r => h r
  have : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact KaehlerDifferential.map_D R R' S S' s

/-- The map of a square is semilinear over the top edge `fS` of the square. -/
theorem kaehlerMapOfSquare_smul (s : S) (x : Ω[S⁄R]) :
    kaehlerMapOfSquare fR fS h (s • x) = fS s • kaehlerMapOfSquare fR fS h x := by
  let := fR.toAlgebra
  let := fS.toAlgebra
  let := (fS.comp (algebraMap R S)).toAlgebra
  have : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq fun r => h r
  have : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact ((KaehlerDifferential.map R R' S S').map_smul s x).trans
    (algebraMap_smul S' s _).symm

/-- **The map of a square and the projection from the cotangent space.**  An additive map of the
cotangent spaces of the canonical presentations which sends `d[b]` to `d[fS b]` and is semilinear
over `fS` is compatible, through `toKaehler`, with the map of the square on differentials. -/
theorem kaehlerMapOfSquare_toKaehler
    (φ : (Generators.self R S).toExtension.CotangentSpace →+
      (Generators.self R' S').toExtension.CotangentSpace)
    (hφ : ∀ b : S, φ ((Generators.self R S).cotangentSpaceBasis b) =
      (Generators.self R' S').cotangentSpaceBasis (fS b))
    (hφs : ∀ (s : S) x, φ (s • x) = fS s • φ x)
    (x : (Generators.self R S).toExtension.CotangentSpace) :
    kaehlerMapOfSquare fR fS h ((Generators.self R S).toExtension.toKaehler x) =
      (Generators.self R' S').toExtension.toKaehler (φ x) := by
  induction x using cotangentSpace_induction with
  | basis b =>
    rw [hφ, Generators.toKaehler_cotangentSpaceBasis, Generators.toKaehler_cotangentSpaceBasis]
    exact kaehlerMapOfSquare_D fR fS h b
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul s x hx => rw [map_smul, kaehlerMapOfSquare_smul, hx, hφs, map_smul]

end Map

section Comp

variable {R'' S'' : Type*} [CommRing R''] [CommRing S''] [Algebra R'' S'']
  (fR : R →+* R') (fS : S →+* S')
  (h : ∀ r : R, fS (algebraMap R S r) = algebraMap R' S' (fR r))
  (gR : R' →+* R'') (gS : S' →+* S'')
  (h' : ∀ r : R', gS (algebraMap R' S' r) = algebraMap R'' S'' (gR r))

/-- **Pasting squares, on Kähler differentials.** -/
theorem kaehlerMapOfSquare_comp (x : Ω[S⁄R]) :
    kaehlerMapOfSquare gR gS h' (kaehlerMapOfSquare fR fS h x) =
      kaehlerMapOfSquare (gR.comp fR) (gS.comp fS)
        (fun r => by simp only [RingHom.comp_apply, h, h']) x := by
  induction x using kaehlerDifferential_induction with
  | D s =>
    rw [kaehlerMapOfSquare_D, kaehlerMapOfSquare_D, kaehlerMapOfSquare_D]
    rfl
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul s x hx =>
    rw [kaehlerMapOfSquare_smul, kaehlerMapOfSquare_smul, kaehlerMapOfSquare_smul, hx]
    rfl

end Comp

/-- The maps induced by two squares with the same ring maps agree. -/
theorem kaehlerMapOfSquare_congr {fR fR' : R →+* R'} {fS fS' : S →+* S'}
    (h : ∀ r : R, fS (algebraMap R S r) = algebraMap R' S' (fR r))
    (h' : ∀ r : R, fS' (algebraMap R S r) = algebraMap R' S' (fR' r)) (eR : fR = fR')
    (eS : fS = fS') (x : Ω[S⁄R]) :
    kaehlerMapOfSquare fR fS h x = kaehlerMapOfSquare fR' fS' h' x := by
  subst eR eS
  rfl

/-- The identity square induces the identity on Kähler differentials. -/
theorem kaehlerMapOfSquare_id (x : Ω[S⁄R]) :
    kaehlerMapOfSquare (RingHom.id R) (RingHom.id S) (fun _ => rfl) x = x := by
  induction x using kaehlerDifferential_induction with
  | D s => exact kaehlerMapOfSquare_D _ _ _ s
  | zero => exact map_zero _
  | add x y hx hy => rw [map_add, hx, hy]
  | smul s x hx =>
    rw [kaehlerMapOfSquare_smul, hx]
    rfl

end Square

section DirectedSystem

variable {Λ : Type*} [Preorder Λ] (sys : RingMapSystemUnbundled Λ)

/-- The cocone maps of a directed system of ring maps are compatible, through `toKaehler`, with
the maps of Kähler differentials of the cocone squares. -/
theorem kaehlerMapOfSquare_toKaehler_cotSpaceMapInf (i : Λ) (x : (sys.NL i).CotangentSpace) :
    kaehlerMapOfSquare (sys.toRinf i) (sys.toSinf i) (fun r => sys.toSinf_g i r)
        ((sys.NL i).toKaehler x) =
      sys.NLinf.toKaehler (sys.cotSpaceMapInf i x) :=
  kaehlerMapOfSquare_toKaehler _ _ _ (sys.cotSpaceMapInf i).toAddMonoidHom
    (sys.cotSpaceMapInf_basis i) (sys.cotSpaceMapInf_smul i) x

/-- The transition maps of a directed system of ring maps are compatible, through `toKaehler`,
with the maps of Kähler differentials of the transition squares. -/
theorem kaehlerMapOfSquare_toKaehler_cotSpaceMap {i j : Λ} (hij : i ≤ j)
    (x : (sys.NL i).CotangentSpace) :
    kaehlerMapOfSquare (sys.fR hij) (sys.fS hij) (fun r => sys.square hij r)
        ((sys.NL i).toKaehler x) =
      (sys.NL j).toKaehler (sys.cotSpaceMap hij x) :=
  kaehlerMapOfSquare_toKaehler _ _ _ (sys.cotSpaceMap hij).toAddMonoidHom
    (sys.cotSpaceMap_basis hij) (sys.cotSpaceMap_smul hij) x

/-- The transition maps of the cotangent spaces of a directed system of ring maps compose. -/
theorem cotSpaceMap_cotSpaceMap {i j k : Λ} (hij : i ≤ j) (hjk : j ≤ k)
    (x : (sys.NL i).CotangentSpace) :
    sys.cotSpaceMap hjk (sys.cotSpaceMap hij x) = sys.cotSpaceMap (hij.trans hjk) x := by
  induction x using cotangentSpace_induction with
  | basis b =>
    rw [sys.cotSpaceMap_basis, sys.cotSpaceMap_basis, sys.cotSpaceMap_basis, sys.fS_comp]
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul s x hx =>
    rw [sys.cotSpaceMap_smul, sys.cotSpaceMap_smul, sys.cotSpaceMap_smul, hx, sys.fS_comp]

/-- The identity transition map of the cotangent spaces of a directed system of ring maps is the
identity. -/
theorem cotSpaceMap_self (i : Λ) (x : (sys.NL i).CotangentSpace) :
    sys.cotSpaceMap (le_refl i) x = x := by
  induction x using cotangentSpace_induction with
  | basis b => rw [sys.cotSpaceMap_basis, sys.fS_id]
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul s x hx => rw [sys.cotSpaceMap_smul, hx, sys.fS_id]

/-- The cotangent spaces of the stages of a directed system of ring maps form a directed
system. -/
theorem directedSystem_cotSpaceMap :
    DirectedSystem (fun i => (sys.NL i).CotangentSpace) (fun _ _ h => ⇑(sys.cotSpaceMap h)) where
  map_self i x := cotSpaceMap_self sys i x
  map_map _ _ _ hij hjk x := cotSpaceMap_cotSpaceMap sys hij hjk x

/-- **A differential of a stage which vanishes in the direct limit vanishes at a later
stage.** -/
theorem exists_kaehlerMapOfSquare_eq_zero_of_directLimit [IsDirected Λ (· ≤ ·)] [Nonempty Λ]
    (a : Λ) (z : Ω[sys.S a⁄sys.R a])
    (hz : kaehlerMapOfSquare (sys.toRinf a) (sys.toSinf a) (fun r => sys.toSinf_g a r) z = 0) :
    ∃ (d : Λ) (had : a ≤ d),
      kaehlerMapOfSquare (sys.fR had) (sys.fS had) (fun r => sys.square had r) z = 0 := by
  classical
  have : IsDirectedOrder Λ := inferInstance
  have := directedSystem_cotSpaceMap sys
  obtain ⟨w, rfl⟩ := (sys.NL a).toKaehler_surjective z
  rw [kaehlerMapOfSquare_toKaehler_cotSpaceMapInf] at hz
  obtain ⟨ξ, hξ⟩ := (sys.NLinf.exact_cotangentComplex_toKaehler (sys.cotSpaceMapInf a w)).mp hz
  obtain ⟨c, rfl⟩ := sys.comparisonCotangent_surjective ξ
  obtain ⟨b, y, rfl⟩ := Module.DirectLimit.exists_of c
  have hby : sys.cotSpaceMapInf b ((sys.NL b).cotangentComplex y) = sys.cotSpaceMapInf a w := by
    rw [← sys.cotMapInf_cotangentComplex, ← hξ]
    exact congrArg _ (sys.comparisonCotangent_toColim b y).symm
  obtain ⟨c, hac, hbc⟩ := exists_ge_ge a b
  have hu0 : sys.cotSpaceMapInf c
      (sys.cotSpaceMap hac w - sys.cotSpaceMap hbc ((sys.NL b).cotangentComplex y)) = 0 := by
    rw [map_sub, sys.cotSpaceMapInf_comp_cotSpaceMap, sys.cotSpaceMapInf_comp_cotSpaceMap, hby,
      sub_self]
  have hcol : sys.toColimCotangentSpace c
      (sys.cotSpaceMap hac w - sys.cotSpaceMap hbc ((sys.NL b).cotangentComplex y)) = 0 := by
    apply sys.comparisonCotangentSpace_injective
    rw [sys.comparisonCotangentSpace_toColim, hu0, map_zero]
  obtain ⟨d, hcd, hd⟩ := Module.DirectLimit.of.zero_exact hcol
  have hd' : sys.cotSpaceMap hcd
      (sys.cotSpaceMap hac w - sys.cotSpaceMap hbc ((sys.NL b).cotangentComplex y)) = 0 := hd
  rw [map_sub, sub_eq_zero, cotSpaceMap_cotSpaceMap sys, cotSpaceMap_cotSpaceMap sys,
    ← sys.cotMap_cotangentComplex] at hd'
  refine ⟨d, hac.trans hcd, ?_⟩
  rw [kaehlerMapOfSquare_toKaehler_cotSpaceMap, hd']
  exact (sys.NL d).exact_cotangentComplex_toKaehler.apply_apply_eq_zero _

end DirectedSystem

section Vanishing

variable {I : Type u} [Category.{v} I] [IsFiltered I] [LocallySmall.{w} I] [FinallySmall.{w} I]
  {R S : I ⥤ CommRingCat.{w}} (g : R ⟶ S) {cR : Cocone R} (hR : IsColimit cR)
  {cS : Cocone S} (hS : IsColimit cS) (gInf : cR.pt ⟶ cS.pt)
  (hg : ∀ i, cR.ι.app i ≫ gInf = g.app i ≫ cS.ι.app i)

include hR hS in
/-- **A differential of a stage which vanishes in the colimit vanishes at a later stage.**  For a
morphism `g : R ⟶ S` of filtered diagrams of rings with colimits `R∞`, `S∞`, a Kähler
differential of `S i` over `R i` whose image in `Ω_{S∞/R∞}` vanishes already vanishes in
`Ω_{S j/R j}` for some `t : i ⟶ j`. -/
theorem exists_kaehlerMapOfSquare_eq_zero_of_isColimit (i : I)
    (z : @KaehlerDifferential (R.obj i) (S.obj i) _ _ (g.app i).hom.toAlgebra)
    (hz : @kaehlerMapOfSquare _ _ _ _ _ _ _ _ (g.app i).hom.toAlgebra gInf.hom.toAlgebra
      (coconeLeg cR i) (coconeLeg cS i) (coconeSquare_comm g gInf hg i) z = 0) :
    ∃ (j : I) (t : i ⟶ j), @kaehlerMapOfSquare _ _ _ _ _ _ _ _
      (g.app i).hom.toAlgebra (g.app j).hom.toAlgebra (R.map t).hom (S.map t).hom
      (diagramSquare_comm g t) z = 0 := by
  obtain ⟨α, _, _, _, F, _⟩ := exists_directed_final.{w} I
  obtain ⟨eR₀, heR₀⟩ := exists_ringEquiv_directLimit_of_final F hR
  obtain ⟨eS₀, heS₀⟩ := exists_ringEquiv_directLimit_of_final F hS
  let : ∀ k : I, Algebra (R.obj k) (S.obj k) := fun k => (g.app k).hom.toAlgebra
  let : Algebra cR.pt cS.pt := gInf.hom.toAlgebra
  let a := Functor.Final.lift F i
  let s : i ⟶ F.obj a := Functor.Final.homToLift F i
  let z' := kaehlerMapOfSquare (R.map s).hom (S.map s).hom (diagramSquare_comm g s) z
  let sys := diagramSystem F g
  let eR : sys.Rinf ≃+* cR.pt := eR₀
  let eS : sys.Sinf ≃+* cS.pt := eS₀
  have heR : ∀ b x, eR (sys.toRinf b x) = coconeLeg cR (F.obj b) x := heR₀
  have heS : ∀ b x, eS (sys.toSinf b x) = coconeLeg cS (F.obj b) x := heS₀
  have hsq : ∀ r : sys.Rinf, eS (algebraMap sys.Rinf sys.Sinf r) =
      algebraMap cR.pt cS.pt (eR r) := by
    intro r
    obtain ⟨b, x, rfl⟩ := Ring.DirectLimit.exists_of r
    show eS (sys.gInf (sys.toRinf b x)) = gInf.hom (eR (sys.toRinf b x))
    rw [← sys.toSinf_g b x]
    exact (heS b _).trans ((ConcreteCategory.congr_hom (hg (F.obj b)) x).symm.trans
      (congrArg gInf.hom (heR b x).symm))
  have hfac : ∀ y : Ω[S.obj (F.obj a)⁄R.obj (F.obj a)],
      kaehlerMapOfSquare (coconeLeg cR (F.obj a)) (coconeLeg cS (F.obj a))
        (coconeSquare_comm g gInf hg (F.obj a)) y =
      kaehlerMapOfSquare eR.toRingHom eS.toRingHom hsq
        (kaehlerMapOfSquare (sys.toRinf a) (sys.toSinf a)
          (fun x => sys.toSinf_g a x) y) := fun y =>
    (kaehlerMapOfSquare_congr _ _ (RingHom.ext fun x => heR a x).symm
      (RingHom.ext fun x => heS a x).symm y).trans (kaehlerMapOfSquare_comp _ _ _ _ _ hsq y).symm
  have hlegs : (coconeLeg cR (F.obj a)).comp (R.map s).hom = coconeLeg cR i :=
    RingHom.ext fun x => ConcreteCategory.congr_hom (cR.w s) x
  have hlegsS : (coconeLeg cS (F.obj a)).comp (S.map s).hom = coconeLeg cS i :=
    RingHom.ext fun x => ConcreteCategory.congr_hom (cS.w s) x
  have hz' : kaehlerMapOfSquare (sys.toRinf a) (sys.toSinf a) (fun x => sys.toSinf_g a x) z'
      = 0 := by
    have hinj : Function.Injective (kaehlerMapOfSquare eR.toRingHom eS.toRingHom hsq) := by
      have h' : ∀ r : cR.pt, eS.symm (algebraMap cR.pt cS.pt r) =
          algebraMap sys.Rinf sys.Sinf (eR.symm r) := fun r =>
        eS.injective ((eS.apply_symm_apply _).trans
          ((hsq (eR.symm r)).trans (congrArg _ (eR.apply_symm_apply r))).symm)
      have hidR : RingHom.id sys.Rinf = eR.symm.toRingHom.comp eR.toRingHom :=
        RingHom.ext fun x => (eR.symm_apply_apply x).symm
      have hidS : RingHom.id sys.Sinf = eS.symm.toRingHom.comp eS.toRingHom :=
        RingHom.ext fun x => (eS.symm_apply_apply x).symm
      refine Function.LeftInverse.injective (g := kaehlerMapOfSquare eR.symm.toRingHom
        eS.symm.toRingHom h') fun x => ?_
      refine (kaehlerMapOfSquare_comp _ _ hsq _ _ h' x).trans ?_
      exact (kaehlerMapOfSquare_congr _ _ hidR hidS x).symm.trans (kaehlerMapOfSquare_id x)
    refine hinj <| (hfac z').symm.trans <|
      (kaehlerMapOfSquare_comp _ _ (diagramSquare_comm g s) _ _
        (coconeSquare_comm g gInf hg (F.obj a)) z).trans ?_
    exact ((kaehlerMapOfSquare_congr _ _ hlegs hlegsS z).trans hz).trans (map_zero _).symm
  obtain ⟨b, hab, hb⟩ := exists_kaehlerMapOfSquare_eq_zero_of_directLimit sys a z' hz'
  exact ⟨F.obj b, s ≫ F.map (homOfLE hab), ((kaehlerMapOfSquare_congr _ _
    (by rw [R.map_comp]; rfl) (by rw [S.map_comp]; rfl) z).trans
      (kaehlerMapOfSquare_comp (R.map s).hom (S.map s).hom (diagramSquare_comm g s)
      (R.map (F.map (homOfLE hab))).hom (S.map (F.map (homOfLE hab))).hom
      (diagramSquare_comm g (F.map (homOfLE hab))) z).symm).trans hb⟩

end Vanishing

section IndEtale

variable {R R' A A' : Type u} [CommRing R] [CommRing R'] [CommRing A] [CommRing A']
  [Algebra R A] [Algebra R' A'] (fR : R →+* R') (fA : A →+* A')
  (h : ∀ r : R, fA (algebraMap R A r) = algebraMap R' A' (fR r))

/-- The `A'`-linear extension `A' ⊗_A Ω_{A/R} → Ω_{A'/R'}`, `a' ⊗ ω ↦ a' • kaehlerMapOfSquare ω`,
of the map of Kähler differentials of a commutative square. -/
noncomputable def kaehlerBaseChangeOfSquare :
    letI := fA.toAlgebra
    A' ⊗[A] Ω[A⁄R] →+ Ω[A'⁄R'] :=
  letI := fA.toAlgebra
  TensorProduct.liftAddHom
    { toFun := fun a' =>
        { toFun := fun ω => a' • kaehlerMapOfSquare fR fA h ω
          map_zero' := by rw [map_zero, smul_zero]
          map_add' := fun ω₁ ω₂ => by rw [map_add, smul_add] }
      map_zero' := AddMonoidHom.ext fun ω => zero_smul A' (kaehlerMapOfSquare fR fA h ω)
      map_add' := fun a₁ a₂ => AddMonoidHom.ext fun ω => add_smul a₁ a₂ _ }
    (fun a a' ω => by
      change (fA a * a') • kaehlerMapOfSquare fR fA h ω =
        a' • kaehlerMapOfSquare fR fA h (a • ω)
      rw [kaehlerMapOfSquare_smul, smul_smul, mul_comm])

/-- The value of `kaehlerBaseChangeOfSquare` on a pure tensor. -/
theorem kaehlerBaseChangeOfSquare_tmul (a' : A') (ω : Ω[A⁄R]) :
    letI := fA.toAlgebra
    kaehlerBaseChangeOfSquare fR fA h (a' ⊗ₜ ω) = a' • kaehlerMapOfSquare fR fA h ω :=
  rfl

/-- **Kähler differentials along a square of ind-étale maps.**  For a commutative square of ring
maps whose horizontal maps `R → R'` and `A → A'` are filtered colimits of étale maps, the
`A'`-linear extension `A' ⊗_A Ω_{A/R} → Ω_{A'/R'}` of the map of the square is bijective. -/
theorem bijective_kaehlerMapOfSquare_liftBaseChange_of_ind_etale
    (hR : letI := fR.toAlgebra
      (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R R'))
    (hA : letI := fA.toAlgebra
      (CommAlgCat.etale.{u} A).ind.{u} (CommAlgCat.of A A')) :
    Function.Bijective (kaehlerBaseChangeOfSquare fR fA h) := by
  let := fR.toAlgebra
  let := fA.toAlgebra
  let := (fA.comp (algebraMap R A)).toAlgebra
  have : IsScalarTower R R' A' := IsScalarTower.of_algebraMap_eq fun r => h r
  have : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : FormallyEtale R R' := FormallyEtale.of_ind_etale R R' hR
  have : FormallyEtale A A' := FormallyEtale.of_ind_etale A A' hA
  have hmap : ∀ ω : Ω[A⁄R],
      kaehlerMapOfSquare fR fA h ω = KaehlerDifferential.map R R' A A' ω := fun _ => rfl
  have heq : ⇑(kaehlerBaseChangeOfSquare fR fA h) =
      ⇑((KaehlerDifferential.map R R' A A').liftBaseChange A') := by
    funext t
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a' ω => rw [kaehlerBaseChangeOfSquare_tmul, LinearMap.liftBaseChange_tmul, hmap]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have heq₂ : (KaehlerDifferential.map R R' A A').liftBaseChange A' =
      KaehlerDifferential.map R R' A' A' ∘ₗ KaehlerDifferential.mapBaseChange R A A' := by
    ext x
    simp [KaehlerDifferential.map_D, KaehlerDifferential.mapBaseChange_tmul]
  rw [heq, heq₂, LinearMap.coe_comp]
  refine Function.Bijective.comp ⟨?_, KaehlerDifferential.map_surjective R R' A'⟩
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A A').bijective
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (KaehlerDifferential.exact_mapBaseChange_map R R' A' x).mp hx
  rw [Subsingleton.elim y 0, map_zero]

end IndEtale

end Stacks.NaiveCotangent

end
