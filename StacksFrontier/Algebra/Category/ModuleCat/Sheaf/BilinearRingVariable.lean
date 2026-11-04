module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearSourceNaturality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageRestrictScalars
public import StacksCore.Tactic.StacksAttribute

/-!
# The ring variable of the universal property of the tensor product sheaf

`Stacks.SheafOfModules.bilinearEquivTensorSheafHom` is the universal property of the tensor
product sheaf of Tag 05NA,

`Bilin_A(F × G, N) = Hom_A(F ⊗_A G, N)`,

and it comes with naturality in the sheaf of values and in the two source modules, for one
fixed sheaf of rings `A`. This file supplies the law in the remaining variable, the *sheaf of
rings*: how the universal property over `A₁` is related to the universal property over `A₂`
along a morphism `a : A₁ ⟶ A₂` of sheaves of rings.

Only restriction of scalars along `a` is involved, and that is what makes the law elementary:
`Stacks.Sheaves.RingedToposModules.moduleSheaf_restrictScalars` holds by `rfl`, so a pairing of
two sheaves of `A₂`-modules *is* a pairing of their restrictions, and the only content is that
`A₂`-bilinearity implies `A₁`-bilinearity.

## Main definitions

* `Stacks.SheafOfModules.tensorSheafUniversalPairing`: the universal bilinear pairing of the
  tensor product sheaf, the pairing the universal property carries to the identity.
* `Stacks.SheafOfModules.tensorSheafRestrictScalarsHom`: the comparison
  `(F|_{A₁}) ⊗_{A₁} (G|_{A₁}) ⟶ (F ⊗_{A₂} G)|_{A₁}` of the two tensor products, the lax
  structure map of restriction of scalars.

## Main results

* `Stacks.SheafOfModules.IsBilinearPairing.restrictScalars`: **a bilinear pairing stays
  bilinear after restriction of scalars.** Scalars act on a restricted module through `a`, so
  each of the two scalar conditions is the corresponding condition over `A₂` precomposed
  with `a`.
* `Stacks.SheafOfModules.bilinearEquivTensorSheafHom_restrictScalars`: **the universal property
  of the tensor product sheaf is compatible with restriction of scalars.** The morphism out of
  `F ⊗_{A₂} G` that a pairing `q` determines, restricted to `A₁` and precomposed with the
  comparison of the two tensor products, is the morphism out of `(F|_{A₁}) ⊗_{A₁} (G|_{A₁})`
  that the *same* pairing determines over `A₁`.

## Implementation notes

*The two scalar squares are transported by a lemma about an abstract category.* Bilinearity is
equivalent to four commuting squares of morphisms of sheaves of sets
(`Stacks.SheafOfModules.isBilinearPairing_iff_squares`), and
`Stacks.Sheaves.RingedToposModules.moduleSMulHom_restrictScalars` factors the scalar action of
`A₁` on a restricted module through the one of `A₂`. Substituting that factorization into the
two scalar squares and reassociating is pure algebra of binary products, and it is stated below
as `smulLeftSquare_restrict` and `smulRightSquare_restrict` for an arbitrary category with
binary products. Written directly for sheaves of sets the reassociations would have to cross
the seam between two spellings of a transported ring structure, where the rewrite motive is not
type-correct at `implicit` transparency; in the abstract statement the sheaf of rings is a plain
object and the specialization is made once, by the elaborator, at default transparency.

The two *additivity* squares need no transport at all: restriction of scalars leaves the
addition of a sheaf of modules alone, on the nose
(`Stacks.Sheaves.RingedToposModules.moduleAddHom_restrictScalars` is `rfl`), so the square over
`A₁` and the square over `A₂` are the same proposition.

*The same seam forbids `rw`.* `Stacks.Sheaves.RingedToposModules.moduleSheaf_restrictScalars`
holds by `rfl`, so the restricted statement of bilinearity type-checks as written; but it is not
type-correct at `implicit` transparency, and `rw [isBilinearPairing_iff_squares]` therefore
reports no occurrence of a pattern which is the whole goal. The equivalence is used through
`Iff.mpr` with the three modules named, and every other step of this file is `congrArg` and
`Eq.trans` for the same reason.

*Why the comparison of tensor products goes this way.* Restriction of scalars is not monoidal;
only the lax structure map exists, because the `A₁`-bilinear pairing which produces it is the
universal `A₂`-bilinear pairing with its scalars restricted, and there is no `A₂`-bilinear
pairing to be made out of an `A₁`-bilinear one. For an `a` which is an isomorphism the
comparison is an isomorphism too, but nothing below needs that.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open Stacks.Sheaves.RingedToposModules

namespace Stacks.SheafOfModules

universe w v u

/-! ## The two scalar squares, for an abstract category -/

section AbstractSquares

variable {𝒜 : Type u} [Category.{v} 𝒜] [HasBinaryProducts 𝒜] {R₀ R₁ A B N : 𝒜}

/-- The square expressing compatibility with scalars in the first argument of a pairing is
carried along by a morphism `α : R₀ ⟶ R₁` of the objects of scalars, provided the scalar action
of `R₀` factors through `α` and the action of `R₁`. This is the abstract form of the
`smulLeftSquare` half of `Stacks.SheafOfModules.IsBilinearPairing.restrictScalars`. -/
private lemma smulLeftSquare_restrict (α : R₀ ⟶ R₁) (sA : R₁ ⨯ A ⟶ A) (sN : R₁ ⨯ N ⟶ N)
    (q : A ⨯ B ⟶ N) (tA : R₀ ⨯ A ⟶ A) (tN : R₀ ⨯ N ⟶ N)
    (hA : tA = prod.map α (𝟙 A) ≫ sA) (hN : tN = prod.map α (𝟙 N) ≫ sN)
    (h : prod.map sA (𝟙 B) ≫ q =
      prod.lift (prod.fst ≫ prod.fst) (prod.lift (prod.fst ≫ prod.snd) prod.snd ≫ q) ≫ sN) :
    prod.map tA (𝟙 B) ≫ q =
      prod.lift (prod.fst ≫ prod.fst) (prod.lift (prod.fst ≫ prod.snd) prod.snd ≫ q) ≫ tN := by
  subst hA
  subst hN
  have hL : prod.map (prod.map α (𝟙 A) ≫ sA) (𝟙 B) ≫ q =
      prod.map (prod.map α (𝟙 A)) (𝟙 B) ≫ (prod.map sA (𝟙 B) ≫ q) := by
    rw [← Category.assoc, prod.map_map, Category.comp_id]
  have e₁ : prod.map (prod.map α (𝟙 A)) (𝟙 B) ≫ (prod.fst ≫ prod.fst) =
      (prod.fst ≫ prod.fst) ≫ α := by
    simp
  have e₂ : prod.map (prod.map α (𝟙 A)) (𝟙 B) ≫
      prod.lift (prod.fst ≫ prod.snd) prod.snd =
      prod.lift (prod.fst ≫ prod.snd) prod.snd := by
    simp
  have hm : prod.map (prod.map α (𝟙 A)) (𝟙 B) ≫
        prod.lift (prod.fst ≫ prod.fst)
          (prod.lift (prod.fst ≫ prod.snd) prod.snd ≫ q) =
      prod.lift (prod.fst ≫ prod.fst) (prod.lift (prod.fst ≫ prod.snd) prod.snd ≫ q) ≫
        prod.map α (𝟙 N) := by
    rw [prod.comp_lift, prod.lift_map, Category.comp_id, e₁, ← Category.assoc, e₂]
  exact hL.trans ((congrArg (fun m ↦ prod.map (prod.map α (𝟙 A)) (𝟙 B) ≫ m) h).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun m ↦ m ≫ sN) hm).trans (Category.assoc _ _ _))))

/-- The same transport for the square expressing compatibility with scalars in the second
argument of a pairing. -/
private lemma smulRightSquare_restrict (α : R₀ ⟶ R₁) (sB : R₁ ⨯ B ⟶ B) (sN : R₁ ⨯ N ⟶ N)
    (q : A ⨯ B ⟶ N) (tB : R₀ ⨯ B ⟶ B) (tN : R₀ ⨯ N ⟶ N)
    (hB : tB = prod.map α (𝟙 B) ≫ sB) (hN : tN = prod.map α (𝟙 N) ≫ sN)
    (h : prod.map (𝟙 A) sB ≫ q =
      prod.lift (prod.snd ≫ prod.fst) (prod.lift prod.fst (prod.snd ≫ prod.snd) ≫ q) ≫ sN) :
    prod.map (𝟙 A) tB ≫ q =
      prod.lift (prod.snd ≫ prod.fst) (prod.lift prod.fst (prod.snd ≫ prod.snd) ≫ q) ≫ tN := by
  subst hB
  subst hN
  have hL : prod.map (𝟙 A) (prod.map α (𝟙 B) ≫ sB) ≫ q =
      prod.map (𝟙 A) (prod.map α (𝟙 B)) ≫ (prod.map (𝟙 A) sB ≫ q) := by
    rw [← Category.assoc, prod.map_map, Category.comp_id]
  have e₁ : prod.map (𝟙 A) (prod.map α (𝟙 B)) ≫ (prod.snd ≫ prod.fst) =
      (prod.snd ≫ prod.fst) ≫ α := by
    simp
  have e₂ : prod.map (𝟙 A) (prod.map α (𝟙 B)) ≫
      prod.lift prod.fst (prod.snd ≫ prod.snd) =
      prod.lift prod.fst (prod.snd ≫ prod.snd) := by
    simp
  have hm : prod.map (𝟙 A) (prod.map α (𝟙 B)) ≫
        prod.lift (prod.snd ≫ prod.fst)
          (prod.lift prod.fst (prod.snd ≫ prod.snd) ≫ q) =
      prod.lift (prod.snd ≫ prod.fst) (prod.lift prod.fst (prod.snd ≫ prod.snd) ≫ q) ≫
        prod.map α (𝟙 N) := by
    rw [prod.comp_lift, prod.lift_map, Category.comp_id, e₁, ← Category.assoc, e₂]
  exact hL.trans ((congrArg (fun m ↦ prod.map (𝟙 A) (prod.map α (𝟙 B)) ≫ m) h).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun m ↦ m ≫ sN) hm).trans (Category.assoc _ _ _))))

end AbstractSquares

/-! ## Bilinearity under restriction of scalars -/

section Bilinear

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  {R R' : Sheaf J RingCat.{w}} (a : R ⟶ R') {A B N : SheafOfModules.{w} R'}

/-- **A bilinear pairing stays bilinear after restriction of scalars.** Let `a : R ⟶ R'` be a
morphism of sheaves of rings and let `q` be an `R'`-bilinear pairing of `A` and `B` with values
in `N`. Restriction of scalars along `a` does not change the underlying sheaves of sets, so `q`
is also a pairing of `A|_R` and `B|_R` with values in `N|_R`, and it is `R`-bilinear: a scalar
of `R` acts on a restricted module as its image under `a` acts on the module itself. -/
lemma IsBilinearPairing.restrictScalars
    {q : Sheaf.moduleSheaf R' A ⨯ Sheaf.moduleSheaf R' B ⟶ Sheaf.moduleSheaf R' N}
    (hq : IsBilinearPairing R' q) :
    IsBilinearPairing R (A := (SheafOfModules.restrictScalars a).obj A)
      (B := (SheafOfModules.restrictScalars a).obj B)
      (N := (SheafOfModules.restrictScalars a).obj N) q := by
  obtain ⟨hadd, hadd', hsmul, hsmul'⟩ := (isBilinearPairing_iff_squares R' q).1 hq
  refine (isBilinearPairing_iff_squares R (A := (SheafOfModules.restrictScalars a).obj A)
    (B := (SheafOfModules.restrictScalars a).obj B)
    (N := (SheafOfModules.restrictScalars a).obj N) q).2 ⟨hadd, hadd', ?_, ?_⟩
  · exact smulLeftSquare_restrict ((sheafCompose J (forget RingCat.{w})).map a)
      (Sheaf.moduleSMulHom R' A) (Sheaf.moduleSMulHom R' N) q
      (Sheaf.moduleSMulHom R ((SheafOfModules.restrictScalars a).obj A))
      (Sheaf.moduleSMulHom R ((SheafOfModules.restrictScalars a).obj N))
      (moduleSMulHom_restrictScalars a A) (moduleSMulHom_restrictScalars a N) hsmul
  · exact smulRightSquare_restrict ((sheafCompose J (forget RingCat.{w})).map a)
      (Sheaf.moduleSMulHom R' B) (Sheaf.moduleSMulHom R' N) q
      (Sheaf.moduleSMulHom R ((SheafOfModules.restrictScalars a).obj B))
      (Sheaf.moduleSMulHom R ((SheafOfModules.restrictScalars a).obj N))
      (moduleSMulHom_restrictScalars a B) (moduleSMulHom_restrictScalars a N) hsmul'

end Bilinear

/-! ## The universal pairing of the tensor product sheaf -/

section UniversalPairing

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {A : Cᵒᵖ ⥤ CommRingCat.{w}}
  {hA : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A)}
  (F G : SheafOfModules.{w} (commRingSheaf J A hA))

/-- The universal bilinear pairing of the tensor product sheaf `F ⊗_A G`: the pairing which the
universal property of Tag 05NA carries to the identity.

It is named because it is the pairing the comparison of two tensor products over different
sheaves of rings is built from, and an unnamed occurrence of it is what makes the elaboration of
that comparison expensive. -/
abbrev tensorSheafUniversalPairing :
    { q : Sheaf.moduleSheaf (commRingSheaf J A hA) F ⨯
          Sheaf.moduleSheaf (commRingSheaf J A hA) G ⟶
        Sheaf.moduleSheaf (commRingSheaf J A hA)
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨A, Presheaf.isSheaf_of_isSheaf_comp _ A
            (forget₂ CommRingCat RingCat) hA⟩).obj F).obj G)) //
      IsBilinearPairing (commRingSheaf J A hA) q } :=
  (bilinearEquivTensorSheafHom (hA := hA) (F := F) (G := G)
    (N := (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨A, Presheaf.isSheaf_of_isSheaf_comp _ A
      (forget₂ CommRingCat RingCat) hA⟩).obj F).obj G))).symm (𝟙 _)

end UniversalPairing

/-! ## The universal property of the tensor product sheaf in the ring variable -/

section TensorRing

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {A₁ A₂ : Cᵒᵖ ⥤ CommRingCat.{w}}
  {h₁ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₁)}
  {h₂ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₂)}
  (a : commRingSheaf J A₁ h₁ ⟶ commRingSheaf J A₂ h₂)
  (F G : SheafOfModules.{w} (commRingSheaf J A₂ h₂))

/-- **The comparison of the two tensor products**, for a morphism `a : A₁ ⟶ A₂` of sheaves of
rings: the tensor product over `A₁` of the restrictions of `F` and `G` maps to the restriction
of their tensor product over `A₂`.

This is the universal property over `A₁` applied to the universal `A₂`-bilinear pairing of
`F ⊗_{A₂} G` with its scalars restricted, which is `A₁`-bilinear by
`Stacks.SheafOfModules.IsBilinearPairing.restrictScalars`. -/
def tensorSheafRestrictScalarsHom :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨A₁, Presheaf.isSheaf_of_isSheaf_comp _ A₁
          (forget₂ CommRingCat RingCat) h₁⟩).obj ((SheafOfModules.restrictScalars a).obj F)).obj
        ((SheafOfModules.restrictScalars a).obj G)) ⟶
      (SheafOfModules.restrictScalars a).obj ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨A₂, Presheaf.isSheaf_of_isSheaf_comp _ A₂
          (forget₂ CommRingCat RingCat) h₂⟩).obj F).obj G)) :=
  bilinearEquivTensorSheafHom (hA := h₁)
    (F := (SheafOfModules.restrictScalars a).obj F)
    (G := (SheafOfModules.restrictScalars a).obj G)
    (N := (SheafOfModules.restrictScalars a).obj ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨A₂, Presheaf.isSheaf_of_isSheaf_comp _ A₂ (forget₂ CommRingCat RingCat) h₂⟩).obj F).obj G)))
    ⟨(tensorSheafUniversalPairing F G).1,
      (tensorSheafUniversalPairing F G).2.restrictScalars a⟩

/-- **The universal property of the tensor product sheaf is compatible with restriction of
scalars.** Let `a : A₁ ⟶ A₂` be a morphism of sheaves of rings, let `F`, `G` and `N` be sheaves
of `A₂`-modules and let `q` be an `A₂`-bilinear pairing of `F` and `G` with values in `N`. The
morphism `F ⊗_{A₂} G ⟶ N` that `q` determines, restricted to `A₁` and precomposed with the
comparison of the two tensor products, is the morphism
`(F|_{A₁}) ⊗_{A₁} (G|_{A₁}) ⟶ N|_{A₁}` that the *same* pairing `q` determines over `A₁`. -/
theorem bilinearEquivTensorSheafHom_restrictScalars
    {N : SheafOfModules.{w} (commRingSheaf J A₂ h₂)}
    (q : { q : Sheaf.moduleSheaf (commRingSheaf J A₂ h₂) F ⨯
            Sheaf.moduleSheaf (commRingSheaf J A₂ h₂) G ⟶
          Sheaf.moduleSheaf (commRingSheaf J A₂ h₂) N //
        IsBilinearPairing (commRingSheaf J A₂ h₂) q }) :
    tensorSheafRestrictScalarsHom a F G ≫
        (SheafOfModules.restrictScalars a).map (bilinearEquivTensorSheafHom (hA := h₂) q) =
      bilinearEquivTensorSheafHom (hA := h₁)
        (F := (SheafOfModules.restrictScalars a).obj F)
        (G := (SheafOfModules.restrictScalars a).obj G)
        (N := (SheafOfModules.restrictScalars a).obj N)
        ⟨q.1, q.2.restrictScalars a⟩ := by
  have hk := bilinearEquivTensorSheafHom_symm_naturality (hA := h₂) (F := F) (G := G)
    (N := (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨A₂, Presheaf.isSheaf_of_isSheaf_comp _ A₂
      (forget₂ CommRingCat RingCat) h₂⟩).obj F).obj G)) (N' := N)
    (𝟙 ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨A₂, Presheaf.isSheaf_of_isSheaf_comp _ A₂
      (forget₂ CommRingCat RingCat) h₂⟩).obj F).obj G)))
    (bilinearEquivTensorSheafHom (hA := h₂) q)
  have hid : (bilinearEquivTensorSheafHom (hA := h₂) (F := F) (G := G) (N := N)).symm
        (𝟙 ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨A₂, Presheaf.isSheaf_of_isSheaf_comp _ A₂
            (forget₂ CommRingCat RingCat) h₂⟩).obj F).obj G)) ≫
          bilinearEquivTensorSheafHom (hA := h₂) q) = q :=
    (congrArg (bilinearEquivTensorSheafHom (hA := h₂) (F := F) (G := G) (N := N)).symm
        (Category.id_comp (bilinearEquivTensorSheafHom (hA := h₂) q))).trans
      ((bilinearEquivTensorSheafHom (hA := h₂) (F := F) (G := G) (N := N)).symm_apply_apply q)
  refine Eq.trans (bilinearEquivTensorSheafHom_naturality (hA := h₁)
    (F := (SheafOfModules.restrictScalars a).obj F)
    (G := (SheafOfModules.restrictScalars a).obj G)
    (N := (SheafOfModules.restrictScalars a).obj ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨A₂, Presheaf.isSheaf_of_isSheaf_comp _ A₂ (forget₂ CommRingCat RingCat) h₂⟩).obj F).obj G)))
    (N' := (SheafOfModules.restrictScalars a).obj N)
    ⟨(tensorSheafUniversalPairing F G).1,
      (tensorSheafUniversalPairing F G).2.restrictScalars a⟩
    ((SheafOfModules.restrictScalars a).map (bilinearEquivTensorSheafHom (hA := h₂) q))).symm ?_
  exact congrArg (bilinearEquivTensorSheafHom (hA := h₁)
      (F := (SheafOfModules.restrictScalars a).obj F)
      (G := (SheafOfModules.restrictScalars a).obj G)
      (N := (SheafOfModules.restrictScalars a).obj N))
    (Subtype.ext (congrArg Subtype.val (hid.symm.trans hk)).symm)

end TensorRing

end Stacks.SheafOfModules

end
