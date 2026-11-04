module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearStalk

/-!
# The Yoneda characterisation of bilinearity

A pairing `q : F × G → H` of the underlying sheaves of sets of three sheaves of modules is
bilinear if and only if, for every sheaf of sets `S`, the induced rule
`Mor(S, F) × Mor(S, G) → Mor(S, H)` is bilinear over the ring `Mor(S, O_X)`. This is the fourth
assertion of the section [Stacks, Tag 0GIG].

Both directions come from the framework of `BilinearStalk.lean`: `Mor(S, -)` preserves all
limits, so `IsBilinearPairingObj` applies to it, and bilinearity passes to it for free. For the
converse the sheaf `S` is taken to be the source of each of the four commuting squares of
`TensorBilinear.lean`, and the three generalized elements are the projections out of it, so that
the condition at that one `S` is the square itself. This is the universal generalized element,
and it is why no quantification over all of `S` has to be inverted.

## Main results

* `Stacks.SheafOfModules.isBilinearPairing_iff_forall_coyoneda` — the Yoneda characterisation of
  [Stacks, Tag 0GIG].

## References

* [Stacks Project, Tag 0GIG](https://stacks.math.columbia.edu/tag/0GIG)
-/

@[expose] public noncomputable section

open CategoryTheory Limits CategoryTheory.Sheaf Opposite
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules

universe w v u

namespace Stacks.SheafOfModules

section ProdLift

variable {D : Type*} [Category D] [HasFiniteProducts D]

/-- The two components of the first projection out of `(X ⨯ Y) ⨯ Z` rebuild it. -/
lemma prod_lift_fst_fst_snd {X Y Z : D} :
    prod.lift (prod.fst ≫ prod.fst) (prod.fst ≫ prod.snd) =
      (prod.fst : (X ⨯ Y) ⨯ Z ⟶ X ⨯ Y) := by
  refine prod.hom_ext ?_ ?_ <;> simp

/-- The two components of the second projection out of `X ⨯ (Y ⨯ Z)` rebuild it. -/
lemma prod_lift_snd_fst_snd {X Y Z : D} :
    prod.lift (prod.snd ≫ prod.fst) (prod.snd ≫ prod.snd) =
      (prod.snd : X ⨯ (Y ⨯ Z) ⟶ Y ⨯ Z) := by
  refine prod.hom_ext ?_ ?_ <;> simp

end ProdLift

section Yoneda

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (R : Sheaf J RingCat.{w}) {A B N : SheafOfModules.{w} R}

omit [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- An element of `Mor(S, Y ⨯ Z)` is the pair of its two components. -/
lemma coyoneda_prodObjMk {S Y Z : Sheaf J (Type w)} (a : S ⟶ Y) (b : S ⟶ Z) :
    Functor.prodObjMk (P := coyoneda.obj (op S)) a b = prod.lift a b := by
  refine Functor.prodObjMk_ext ?_ ?_ <;>
    simp only [Functor.map_fst_prodObjMk, Functor.map_snd_prodObjMk] <;> simp

variable (q : moduleSheaf R A ⨯ moduleSheaf R B ⟶ moduleSheaf R N)

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- On `Mor(S, -)` the induced pairing is composition with `q`. -/
lemma coyoneda_pairingObj {S : Sheaf J (Type w)} (x : S ⟶ moduleSheaf R A)
    (y : S ⟶ moduleSheaf R B) :
    pairingObj R q (coyoneda.obj (op S)) x y = prod.lift x y ≫ q := by
  rw [pairingObj, coyoneda_prodObjMk]
  rfl

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- On `Mor(S, -)` the transported addition is composition with the addition of the sheaf. -/
lemma coyoneda_moduleAddObj (G : SheafOfModules.{w} R) {S : Sheaf J (Type w)}
    (x y : S ⟶ moduleSheaf R G) :
    Sheaf.moduleAddObj R G (coyoneda.obj (op S)) x y = prod.lift x y ≫ moduleAddHom R G := by
  rw [Sheaf.moduleAddObj, coyoneda_prodObjMk]
  rfl

/-- On `Mor(S, -)` the transported scalar action is composition with the action of the sheaf. -/
lemma coyoneda_moduleSMulObj (G : SheafOfModules.{w} R) {S : Sheaf J (Type w)}
    (r : S ⟶ Sheaf.ringSheaf R) (x : S ⟶ moduleSheaf R G) :
    Sheaf.moduleSMulObj R G (coyoneda.obj (op S)) r x =
      prod.lift r x ≫ moduleSMulHom R G := by
  rw [Sheaf.moduleSMulObj, coyoneda_prodObjMk]
  rfl

/-- **The Yoneda characterisation of bilinearity.** A pairing of the underlying sheaves of sets
is bilinear if and only if the rule it induces on morphisms from an arbitrary sheaf of sets `S`
is bilinear over the ring of morphisms from `S` to the sheaf of rings. -/
@[stacks 0GIG "the fourth characterisation of the section: a pairing is bilinear if and only if
for every sheaf of sets `S` the induced rule `Mor(S, F) x Mor(S, G) -> Mor(S, H)` is bilinear
over the ring `Mor(S, O_X)`. The ring and module structures on those morphism sets are the ones
`CategoryTheory.Sheaf.ringObjRing` and `CategoryTheory.Sheaf.moduleObjModule` transport along
`Mor(S, -)`, which preserves finite products. Over an arbitrary site rather than only the opens
of a ringed space, and over a not necessarily commutative sheaf of rings. The forward direction
is `IsBilinearPairing.isBilinearPairingObj`; the converse needs only the single `S` which is the
source of each of the four squares, with the three arguments taken to be the projections out of
it"]
theorem isBilinearPairing_iff_forall_coyoneda :
    IsBilinearPairing R q ↔
      ∀ S : Sheaf J (Type w), IsBilinearPairingObj R q (coyoneda.obj (op S)) := by
  refine ⟨fun h S ↦ h.isBilinearPairingObj R q _, fun h ↦ ?_⟩
  rw [isBilinearPairing_iff_squares]
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨hal, -, -, -⟩ := (isBilinearPairingObj_iff R q _).1
      (h ((moduleSheaf R A ⨯ moduleSheaf R A) ⨯ moduleSheaf R B))
    have e := hal (prod.fst ≫ prod.fst) (prod.fst ≫ prod.snd) prod.snd
    simp only [coyoneda_pairingObj, coyoneda_moduleAddObj] at e
    rw [addLeftSquare, ← e]
    congr 1
    refine prod.hom_ext ?_ ?_ <;> simp [prod_lift_fst_fst_snd]
  · obtain ⟨-, har, -, -⟩ := (isBilinearPairingObj_iff R q _).1
      (h (moduleSheaf R A ⨯ (moduleSheaf R B ⨯ moduleSheaf R B)))
    have e := har prod.fst (prod.snd ≫ prod.fst) (prod.snd ≫ prod.snd)
    simp only [coyoneda_pairingObj, coyoneda_moduleAddObj] at e
    rw [addRightSquare, ← e]
    congr 1
    refine prod.hom_ext ?_ ?_ <;> simp [prod_lift_snd_fst_snd]
  · obtain ⟨-, -, hsl, -⟩ := (isBilinearPairingObj_iff R q _).1
      (h ((Sheaf.ringSheaf R ⨯ moduleSheaf R A) ⨯ moduleSheaf R B))
    have e := hsl (prod.fst ≫ prod.fst) (prod.fst ≫ prod.snd) prod.snd
    simp only [coyoneda_pairingObj, coyoneda_moduleSMulObj] at e
    rw [smulLeftSquare, ← e]
    congr 1
    refine prod.hom_ext ?_ ?_ <;> simp [prod_lift_fst_fst_snd]
  · obtain ⟨-, -, -, hsr⟩ := (isBilinearPairingObj_iff R q _).1
      (h (moduleSheaf R A ⨯ (Sheaf.ringSheaf R ⨯ moduleSheaf R B)))
    have e := hsr (prod.snd ≫ prod.fst) prod.fst (prod.snd ≫ prod.snd)
    simp only [coyoneda_pairingObj, coyoneda_moduleSMulObj] at e
    rw [smulRightSquare, ← e]
    congr 1
    refine prod.hom_ext ?_ ?_ <;> simp [prod_lift_snd_fst_snd]

end Yoneda

end Stacks.SheafOfModules

end
