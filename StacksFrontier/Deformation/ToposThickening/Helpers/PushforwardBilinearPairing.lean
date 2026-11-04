module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorBilinear

/-!
# The image of a bilinear pairing under a finite-product-preserving functor

Let `Φ : Sh(D) ⥤ Sh(C)` be a functor between categories of sheaves of sets preserving finite
products (the direct image or the inverse image of a morphism of topoi), let `O` be a sheaf of
rings on `D` and let `q : A × B ⟶ N` be an `O`-bilinear pairing of the underlying sheaves of sets
of three `O`-modules. Then `Φ(A) × Φ(B) ≅ Φ(A × B) ⟶ Φ(N)` is a bilinear pairing of the modules
`Φ(A)`, `Φ(B)`, `Φ(N)` over `Φ(O)` of Stacks 03D2: the four commuting squares expressing
bilinearity are carried along `Φ`.

## Main definitions

* `Stacks.SheafOfModules.pushPairing`: the pairing `Φ(A) × Φ(B) ⟶ Φ(N)`.

## Main results

* `Stacks.SheafOfModules.pairingApp_pushPairing`: its value on a pair of local sections.
* `Stacks.SheafOfModules.isBilinearPairing_pushPairing`: it is bilinear.

## References

* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 0GIG](https://stacks.math.columbia.edu/tag/0GIG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open Stacks.Sheaves.ToposPullback (pullbackRingSheaf pullbackModuleObj)

universe ww ww' vv uu vv' uu'

namespace CategoryTheory.Functor

variable {E : Type*} [Category E] [HasFiniteProducts E] (P : E ⥤ Type*) [PreservesFiniteProducts P]

/-- A square expressing additivity in the first argument, read on elements after `P`. -/
lemma map_pairing_addLeft {X Y N : E} (add : X ⨯ X ⟶ X) (addN : N ⨯ N ⟶ N) (q : X ⨯ Y ⟶ N)
    (h : prod.map add (𝟙 Y) ≫ q = prod.lift (prod.lift (prod.fst ≫ prod.fst) prod.snd ≫ q)
      (prod.lift (prod.fst ≫ prod.snd) prod.snd ≫ q) ≫ addN)
    (a a' : P.obj X) (b : P.obj Y) :
    P.map q (prodObjMk (P.map add (prodObjMk a a')) b) =
      P.map addN (prodObjMk (P.map q (prodObjMk a b)) (P.map q (prodObjMk a' b))) := by
  simpa using congrArg (fun m => P.map m (prodObjMk (prodObjMk a a') b)) h

/-- A square expressing additivity in the second argument, read on elements after `P`. -/
lemma map_pairing_addRight {X Y N : E} (add : Y ⨯ Y ⟶ Y) (addN : N ⨯ N ⟶ N) (q : X ⨯ Y ⟶ N)
    (h : prod.map (𝟙 X) add ≫ q = prod.lift (prod.lift prod.fst (prod.snd ≫ prod.fst) ≫ q)
      (prod.lift prod.fst (prod.snd ≫ prod.snd) ≫ q) ≫ addN)
    (a : P.obj X) (b b' : P.obj Y) :
    P.map q (prodObjMk a (P.map add (prodObjMk b b'))) =
      P.map addN (prodObjMk (P.map q (prodObjMk a b)) (P.map q (prodObjMk a b'))) := by
  simpa using congrArg (fun m => P.map m (prodObjMk a (prodObjMk b b'))) h

/-- A square expressing compatibility with scalars in the first argument, read on elements after
`P`. -/
lemma map_pairing_smulLeft {R X Y N : E} (smul : R ⨯ X ⟶ X) (smulN : R ⨯ N ⟶ N)
    (q : X ⨯ Y ⟶ N)
    (h : prod.map smul (𝟙 Y) ≫ q =
      prod.lift (prod.fst ≫ prod.fst) (prod.lift (prod.fst ≫ prod.snd) prod.snd ≫ q) ≫ smulN)
    (r : P.obj R) (a : P.obj X) (b : P.obj Y) :
    P.map q (prodObjMk (P.map smul (prodObjMk r a)) b) =
      P.map smulN (prodObjMk r (P.map q (prodObjMk a b))) := by
  simpa using congrArg (fun m => P.map m (prodObjMk (prodObjMk r a) b)) h

/-- A square expressing compatibility with scalars in the second argument, read on elements
after `P`. -/
lemma map_pairing_smulRight {R X Y N : E} (smul : R ⨯ Y ⟶ Y) (smulN : R ⨯ N ⟶ N)
    (q : X ⨯ Y ⟶ N)
    (h : prod.map (𝟙 X) smul ≫ q =
      prod.lift (prod.snd ≫ prod.fst) (prod.lift prod.fst (prod.snd ≫ prod.snd) ≫ q) ≫ smulN)
    (r : P.obj R) (a : P.obj X) (b : P.obj Y) :
    P.map q (prodObjMk a (P.map smul (prodObjMk r b))) =
      P.map smulN (prodObjMk r (P.map q (prodObjMk a b))) := by
  simpa using congrArg (fun m => P.map m (prodObjMk a (prodObjMk r b))) h

/-- `P` of a product of two morphisms followed by a morphism, on a pair of elements. -/
lemma map_prodMap_comp_prodObjMk {X Y X' Y' Z : E} (f : X ⟶ X') (g : Y ⟶ Y') (h : X' ⨯ Y' ⟶ Z)
    (a : P.obj X) (b : P.obj Y) :
    P.map (prod.map f g ≫ h) (prodObjMk a b) = P.map h (prodObjMk (P.map f a) (P.map g b)) := by
  simp

end CategoryTheory.Functor

namespace Stacks.SheafOfModules

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]
  {O : Sheaf K RingCat.{ww'}} {A B N : SheafOfModules.{ww'} O}

/-- **The image of a pairing under `Φ`**: `Φ(A) × Φ(B) ≅ Φ(A × B) ⟶ Φ(N)`. -/
def pushPairing (q : moduleSheaf O A ⨯ moduleSheaf O B ⟶ moduleSheaf O N) :
    moduleSheaf (pullbackRingSheaf J Φ O) (pullbackModuleObj J Φ O A) ⨯
        moduleSheaf (pullbackRingSheaf J Φ O) (pullbackModuleObj J Φ O B) ⟶
      moduleSheaf (pullbackRingSheaf J Φ O) (pullbackModuleObj J Φ O N) :=
  (PreservesLimitPair.iso Φ (moduleSheaf O A) (moduleSheaf O B)).inv ≫ Φ.map q

omit [J.HasSheafCompose (forget RingCat.{ww})] in
/-- The image of a pairing under `Φ`, on a pair of local sections: `q` read through `Φ` on the
pair of sections of `Φ(A ⨯ B)` they determine. -/
lemma pairingApp_pushPairing (q : moduleSheaf O A ⨯ moduleSheaf O B ⟶ moduleSheaf O N)
    (U : Cᵒᵖ)
    (a : (sectionsFunctor J U).obj
      (moduleSheaf (pullbackRingSheaf J Φ O) (pullbackModuleObj J Φ O A)))
    (b : (sectionsFunctor J U).obj
      (moduleSheaf (pullbackRingSheaf J Φ O) (pullbackModuleObj J Φ O B))) :
    pairingApp (pullbackRingSheaf J Φ O) (pushPairing J Φ q) U a b =
      (Φ ⋙ sectionsFunctor J U).map q
        (Functor.prodObjMk (P := Φ ⋙ sectionsFunctor J U) (A := moduleSheaf O A)
          (B := moduleSheaf O B) a b) := by
  let p := Functor.prodObjMk (P := Φ ⋙ sectionsFunctor J U) (A := moduleSheaf O A)
    (B := moduleSheaf O B) a b
  have hp : (sectionsFunctor J U).map
      (PreservesLimitPair.iso Φ (moduleSheaf O A) (moduleSheaf O B)).hom p =
      Functor.prodObjMk (P := sectionsFunctor.{ww} J U) (A := Φ.obj (moduleSheaf O A))
        (B := Φ.obj (moduleSheaf O B)) a b := by
    rw [PreservesLimitPair.iso_hom, Functor.map_prodComparison_apply]
    exact congrArg₂ _ (Functor.map_fst_prodObjMk (P := Φ ⋙ sectionsFunctor J U) a b)
      (Functor.map_snd_prodObjMk (P := Φ ⋙ sectionsFunctor J U) a b)
  have hinv : (sectionsFunctor J U).map
      (PreservesLimitPair.iso Φ (moduleSheaf O A) (moduleSheaf O B)).inv
        (Functor.prodObjMk (P := sectionsFunctor.{ww} J U) (A := Φ.obj (moduleSheaf O A))
          (B := Φ.obj (moduleSheaf O B)) a b) = p := by
    rw [← hp, ← (sectionsFunctor J U).map_comp_apply, Iso.hom_inv_id,
      (sectionsFunctor J U).map_id_apply]
  exact ((sectionsFunctor J U).map_comp_apply _ (Φ.map q) _).trans
    (congrArg ((sectionsFunctor J U).map (Φ.map q)) hinv)

omit [J.HasSheafCompose (forget RingCat.{ww})] in
variable {J Φ} in
/-- Addition of sections of `Φ(M)` is `Φ` of the addition map. -/
lemma add_eq_map_moduleAddHom (U : Cᵒᵖ) {M : SheafOfModules.{ww'} O}
    (a a' : (sectionsFunctor J U).obj (moduleSheaf (pullbackRingSheaf J Φ O)
      (pullbackModuleObj J Φ O M))) :
    a + a' =
      (Φ ⋙ sectionsFunctor J U).map (moduleAddHom O M)
        (Functor.prodObjMk (P := Φ ⋙ sectionsFunctor J U) a a') :=
  (sectionsFunctor_map_moduleAddHom (pullbackRingSheaf J Φ O) (pullbackModuleObj J Φ O M) U a
    a').symm.trans (Stacks.Sheaves.ToposPullback.moduleAddHom_pullback_apply J Φ O M U a a')

variable {J Φ} in
/-- Scalar multiplication of sections of `Φ(M)` is `Φ` of the scalar multiplication map. -/
lemma smul_eq_map_moduleSMulHom (U : Cᵒᵖ) {M : SheafOfModules.{ww'} O}
    (r : (sectionsFunctor J U).obj (ringSheaf (pullbackRingSheaf J Φ O)))
    (a : (sectionsFunctor J U).obj (moduleSheaf (pullbackRingSheaf J Φ O)
      (pullbackModuleObj J Φ O M))) :
    r • a =
      (Φ ⋙ sectionsFunctor J U).map (moduleSMulHom O M)
        (Functor.prodObjMk (P := Φ ⋙ sectionsFunctor J U) r a) :=
  (sectionsFunctor_map_moduleSMulHom (pullbackRingSheaf J Φ O) (pullbackModuleObj J Φ O M) U r
    a).symm.trans (Stacks.Sheaves.ToposPullback.moduleSMulHom_pullback_apply J Φ O M U r a)

/-- **The image under `Φ` of a bilinear pairing is bilinear**: the four squares expressing
bilinearity are carried along `Φ`, which preserves finite products. -/
lemma isBilinearPairing_pushPairing {q : moduleSheaf O A ⨯ moduleSheaf O B ⟶ moduleSheaf O N}
    (hq : IsBilinearPairing O q) :
    IsBilinearPairing (pullbackRingSheaf J Φ O) (pushPairing J Φ q) := by
  obtain ⟨hal, har, hsl, hsr⟩ := (isBilinearPairing_iff_squares O q).1 hq
  refine ⟨fun U a a' b => ?_, fun U a b b' => ?_, fun U r a b => ?_, fun U r a b => ?_⟩
  · simp only [pairingApp_pushPairing]
    rw [add_eq_map_moduleAddHom U a a',
      Functor.map_pairing_addLeft (Φ ⋙ sectionsFunctor J U) _ _ q hal a a' b]
    exact (add_eq_map_moduleAddHom U _ _).symm
  · simp only [pairingApp_pushPairing]
    rw [add_eq_map_moduleAddHom U b b',
      Functor.map_pairing_addRight (Φ ⋙ sectionsFunctor J U) _ _ q har a b b']
    exact (add_eq_map_moduleAddHom U _ _).symm
  · simp only [pairingApp_pushPairing]
    rw [smul_eq_map_moduleSMulHom U r a,
      Functor.map_pairing_smulLeft (Φ ⋙ sectionsFunctor J U) _ _ q hsl r a b]
    exact (smul_eq_map_moduleSMulHom U _ _).symm
  · simp only [pairingApp_pushPairing]
    rw [smul_eq_map_moduleSMulHom U r b,
      Functor.map_pairing_smulRight (Φ ⋙ sectionsFunctor J U) _ _ q hsr r a b]
    exact (smul_eq_map_moduleSMulHom U _ _).symm

end Stacks.SheafOfModules

end
