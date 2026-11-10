module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules
public import StacksFrontier.CategoryTheory.Sites.Modules.Tensor
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparison
public import Mathlib.CategoryTheory.Sites.Limits

/-! # Bilinear pairings and the tensor product of sheaves of modules

Let `(C, J)` be a site, let `O` be a presheaf of commutative rings on it whose underlying
presheaf of rings is a sheaf, and let `A`, `B`, `N` be sheaves of modules over the resulting
sheaf of rings. Stacks 18.26 introduces, just before Tag 03EL, the set
`Bilin_O(A × B, N)` of morphisms `A × B ⟶ N` of the *underlying sheaves of sets* which are
`O`-bilinear, and records that the tensor product represents it:
`Hom_O(A ⊗_O B, N) = Bilin_O(A × B, N)`.

This file formalizes that. `Stacks.SheafOfModules.IsBilinearPairing` is the bilinearity
condition and `Stacks.SheafOfModules.bilinearEquivTensorHom` is the bijection with the
morphisms out of the tensor product sheaf of Tag 0GMW.

The point of the form "a morphism of the underlying sheaves of sets, together with commuting
squares for the operations", rather than "a family of bilinear maps on sections", is that it
is the form which transports across the adjunction `f⁻¹ ⊣ f_*` of a morphism of topoi, where
neither `f⁻¹` nor `f_*` has any description on sections. That transport is the mechanism of
Tag 03EL.

## Main definitions

* `Stacks.SheafOfModules.pairingApp`: the value of a pairing of the underlying sheaves of sets
  on a pair of local sections.
* `Stacks.SheafOfModules.IsBilinearPairing`: bilinearity of such a pairing.
* `Stacks.SheafOfModules.addLeftSquare`, `addRightSquare`, `smulLeftSquare`,
  `smulRightSquare`: the four bilinearity conditions as commuting squares of morphisms of
  sheaves of sets.
* `Stacks.SheafOfModules.pairingOfTensorHom`: the pairing determined by a morphism out of the
  objectwise tensor product presheaf, and `Stacks.SheafOfModules.tensorHomOfPairing` its
  inverse.
* `Stacks.SheafOfModules.tensorSectionPairing`: the universal bilinear pairing, with values in
  the tensor product sheaf of Tag 0GMW.

## Main results

* `Stacks.SheafOfModules.bilinearEquivPresheafTensorHom`: bilinear pairings of `A` and `B`
  with values in `N` are the same thing as morphisms of presheaves of modules out of the
  objectwise tensor product `A ⊗ B`.
* `Stacks.SheafOfModules.bilinearEquivTensorHom`: bilinear pairings of `A` and `B` with values
  in `N` are the same thing as morphisms of sheaves of modules out of the tensor product sheaf
  `A ⊗_O B`. This is the displayed formula of Stacks 18.26, and the universal property that
  `tensorSectionPairing` realizes.
* `Stacks.SheafOfModules.isBilinearPairing_iff_squares`: bilinearity on sections is equivalent
  to the four commuting squares.
* `Stacks.SheafOfModules.prodObjMk_eq_inv_prodComparison`: the pairing of two local sections
  into the product sheaf, written through the inverse of the product comparison.

## Implementation notes

Local sections are spelled `(sectionsFunctor J U).obj (moduleSheaf R A)` throughout, not
`A.val.obj U`. The two are definitionally equal, but they are not interchangeable for `simp`:
the rewrite rules of the element calculus of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullback` are stated in the former
spelling, and with a section written at the latter type not one of them fires, because `simp`
unifies below default transparency. The two spellings meet in exactly one place — the passage
between a pairing and a morphism out of the objectwise tensor product — where the tensor is
formed at the `A.val.obj U` types.

Bilinearity is defined on sections, because that is how it is verified, and the four commuting
squares — the form in which it transports along a morphism of topoi — are proved equivalent to
it. The squares are stated at the universal generalized element, i.e. with the projections of
the relevant triple product as their arguments; precomposing recovers the condition for all
generalized elements, so no auxiliary sheaf has to be quantified over.

Everything is stated over a sheaf of rings presented as `commRingSheaf J O h`, the underlying
sheaf of rings of a presheaf of commutative rings `O`. This spelling, rather than
`Stacks.SheafOfModules.Tensor.ringSheaf` of a sheaf of commutative rings, is what makes Mathlib's
monoidal structure on `PresheafOfModules (O ⋙ forget₂ CommRingCat RingCat)` available to instance
search, and it is also the spelling in which the inverse image of a structure sheaf along a
morphism of topoi is presented (`pullbackRingSheaf_eq_commRingSheaf`).

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules

universe w v u

namespace Stacks.SheafOfModules

/-! ## Scalars through a linear map out of a tensor product

These two lemmas are stated for a linear map between plain types over a single `[CommRing R]`
instance, following
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparison` and for the same
reason: a ring of sections of a presheaf of commutative rings, read through
`forget₂ CommRingCat RingCat`, carries two definitionally equal `CommRing` structures, and a
`map_smul` elaborated against the goal picks the wrong one. -/

section Aux

open scoped TensorProduct

variable {R : Type w} [CommRing R] {M N P : Type w} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

/-- A linear map out of a tensor product is additive in the first factor. -/
private lemma map_add_tmul (g : (M ⊗[R] N) →ₗ[R] P) (m m' : M) (n : N) :
    g ((m + m') ⊗ₜ[R] n) = g (m ⊗ₜ[R] n) + g (m' ⊗ₜ[R] n) := by
  rw [TensorProduct.add_tmul, map_add]

/-- A linear map out of a tensor product is additive in the second factor. -/
private lemma map_tmul_add (g : (M ⊗[R] N) →ₗ[R] P) (m : M) (n n' : N) :
    g (m ⊗ₜ[R] (n + n')) = g (m ⊗ₜ[R] n) + g (m ⊗ₜ[R] n') := by
  rw [TensorProduct.tmul_add, map_add]

end Aux

/-! ## Extensionality for morphisms out of a triple product of sheaves of sets -/

section Ext

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Two morphisms out of `(X ⨯ Y) ⨯ Z` agree as soon as they agree on all triples of local
sections. -/
lemma hom_ext_prodProd {X Y Z E : Sheaf J (Type w)} {m m' : (X ⨯ Y) ⨯ Z ⟶ E}
    (h : ∀ (U : Cᵒᵖ) (x : (sectionsFunctor J U).obj X) (y : (sectionsFunctor J U).obj Y)
      (z : (sectionsFunctor J U).obj Z),
      (sectionsFunctor J U).map m (Functor.prodObjMk (Functor.prodObjMk x y) z) =
        (sectionsFunctor J U).map m' (Functor.prodObjMk (Functor.prodObjMk x y) z)) :
    m = m' := by
  refine hom_ext_sections fun U s ↦ ?_
  have e : s = Functor.prodObjMk (P := sectionsFunctor J U)
      (Functor.prodObjMk
        ((sectionsFunctor J U).map prod.fst ((sectionsFunctor J U).map prod.fst s))
        ((sectionsFunctor J U).map prod.snd ((sectionsFunctor J U).map prod.fst s)))
      ((sectionsFunctor J U).map prod.snd s) := by simp
  rw [e]
  exact h U _ _ _

/-- Two morphisms out of `X ⨯ (Y ⨯ Z)` agree as soon as they agree on all triples of local
sections. -/
lemma hom_ext_prodProd' {X Y Z E : Sheaf J (Type w)} {m m' : X ⨯ (Y ⨯ Z) ⟶ E}
    (h : ∀ (U : Cᵒᵖ) (x : (sectionsFunctor J U).obj X) (y : (sectionsFunctor J U).obj Y)
      (z : (sectionsFunctor J U).obj Z),
      (sectionsFunctor J U).map m (Functor.prodObjMk x (Functor.prodObjMk y z)) =
        (sectionsFunctor J U).map m' (Functor.prodObjMk x (Functor.prodObjMk y z))) :
    m = m' := by
  refine hom_ext_sections fun U s ↦ ?_
  have e : s = Functor.prodObjMk (P := sectionsFunctor J U)
      ((sectionsFunctor J U).map prod.fst s)
      (Functor.prodObjMk
        ((sectionsFunctor J U).map prod.fst ((sectionsFunctor J U).map prod.snd s))
        ((sectionsFunctor J U).map prod.snd ((sectionsFunctor J U).map prod.snd s))) := by simp
  rw [e]
  exact h U _ _ _

/-- Two morphisms out of `(X ⨯ Y) ⨯ Z` are equal if and only if they agree on all triples of
local sections. -/
private lemma eq_iff_forall_prodProd {X Y Z E : Sheaf J (Type w)} {m m' : (X ⨯ Y) ⨯ Z ⟶ E} :
    m = m' ↔ ∀ (U : Cᵒᵖ) (x : (sectionsFunctor J U).obj X) (y : (sectionsFunctor J U).obj Y)
      (z : (sectionsFunctor J U).obj Z),
      (sectionsFunctor J U).map m (Functor.prodObjMk (Functor.prodObjMk x y) z) =
        (sectionsFunctor J U).map m' (Functor.prodObjMk (Functor.prodObjMk x y) z) :=
  ⟨fun h _ _ _ _ ↦ by rw [h], hom_ext_prodProd⟩

/-- Two morphisms out of `X ⨯ (Y ⨯ Z)` are equal if and only if they agree on all triples of
local sections. -/
private lemma eq_iff_forall_prodProd' {X Y Z E : Sheaf J (Type w)} {m m' : X ⨯ (Y ⨯ Z) ⟶ E} :
    m = m' ↔ ∀ (U : Cᵒᵖ) (x : (sectionsFunctor J U).obj X) (y : (sectionsFunctor J U).obj Y)
      (z : (sectionsFunctor J U).obj Z),
      (sectionsFunctor J U).map m (Functor.prodObjMk x (Functor.prodObjMk y z)) =
        (sectionsFunctor J U).map m' (Functor.prodObjMk x (Functor.prodObjMk y z)) :=
  ⟨fun h _ _ _ _ ↦ by rw [h], hom_ext_prodProd'⟩

set_option synthInstance.maxHeartbeats 1000000 in
-- The instance search for the binary products in the statement became slow in Mathlib v4.35.0.
set_option maxHeartbeats 2000000 in
-- Elaborating the statement and proof with these slow instance searches needs more heartbeats.
/-- The element of a binary product of sheaves of sets determined by a pair of local sections,
written through the inverse of the product comparison of the sections functor. This records
that `CategoryTheory.Functor.prodObjMk` for the sections functor is the pairing of sections
used in the statement of Tag 03EL. -/
lemma prodObjMk_eq_inv_prodComparison {A B : Sheaf J (Type w)} (U : Cᵒᵖ)
    (a : (sectionsFunctor J U).obj A) (b : (sectionsFunctor J U).obj B) :
    Functor.prodObjMk (P := sectionsFunctor J U) a b =
      inv (prodComparison (sheafToPresheaf J (Type w) ⋙ (evaluation Cᵒᵖ (Type w)).obj U) A B)
        ((Types.binaryProductIso (A.obj.obj U) (B.obj.obj U)).inv (a, b)) := by
  have h : inv (prodComparison
        (sheafToPresheaf J (Type w) ⋙ (evaluation Cᵒᵖ (Type w)).obj U) A B) =
      (PreservesLimitPair.iso
        (sheafToPresheaf J (Type w) ⋙ (evaluation Cᵒᵖ (Type w)).obj U) A B).inv :=
    IsIso.inv_eq_of_hom_inv_id (by rw [← PreservesLimitPair.iso_hom]; exact Iso.hom_inv_id _)
  rw [h]
  rfl

end Ext

/-! ## Bilinear pairings of the underlying sheaves of sets -/

section Pairing

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (R : Sheaf J RingCat.{w})

variable {A B N : SheafOfModules.{w} R}

/-- The value on a pair of local sections of a morphism from the product of the underlying
sheaves of sets of two sheaves of modules. -/
def pairingApp (q : moduleSheaf R A ⨯ moduleSheaf R B ⟶ moduleSheaf R N) (U : Cᵒᵖ)
    (a : (sectionsFunctor J U).obj (moduleSheaf R A))
    (b : (sectionsFunctor J U).obj (moduleSheaf R B)) :
    (sectionsFunctor J U).obj (moduleSheaf R N) :=
  (sectionsFunctor J U).map q (Functor.prodObjMk a b)

variable (q : moduleSheaf R A ⨯ moduleSheaf R B ⟶ moduleSheaf R N)

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- A pairing of the underlying sheaves of sets is compatible with restriction of sections. -/
lemma pairingApp_sectionsRestrict {U V : Cᵒᵖ} (g : U ⟶ V)
    (a : (sectionsFunctor J U).obj (moduleSheaf R A))
    (b : (sectionsFunctor J U).obj (moduleSheaf R B)) :
    (sectionsRestrict (J := J) g).app (moduleSheaf R N) (pairingApp R q U a b) =
      pairingApp R q V ((sectionsRestrict (J := J) g).app (moduleSheaf R A) a)
        ((sectionsRestrict (J := J) g).app (moduleSheaf R B) b) := by
  let θ : sectionsFunctor.{w} J U ⟶ sectionsFunctor.{w} J V := sectionsRestrict (J := J) g
  have h₁ := Functor.natTrans_app_map_apply θ q
    (Functor.prodObjMk (P := sectionsFunctor J U)
      (A := moduleSheaf R A) (B := moduleSheaf R B) a b)
  have h₂ := Functor.prodObjMk_naturality (Q := sectionsFunctor J V) θ
    (A := moduleSheaf R A) (B := moduleSheaf R B) a b
  rwa [h₂] at h₁

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- A pairing of the underlying sheaves of sets is compatible with restriction of sections,
spelled through the restriction maps of the sheaves of modules themselves. -/
lemma pairingApp_naturality {U V : Cᵒᵖ} (g : U ⟶ V)
    (a : (sectionsFunctor J U).obj (moduleSheaf R A))
    (b : (sectionsFunctor J U).obj (moduleSheaf R B)) :
    N.val.map g (pairingApp R q U a b) =
      pairingApp R q V (A.val.map g a) (B.val.map g b) :=
  pairingApp_sectionsRestrict R q g a b

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- Two pairings of the underlying sheaves of sets agree as soon as they agree on all pairs of
local sections. -/
lemma pairing_ext {q q' : moduleSheaf R A ⨯ moduleSheaf R B ⟶ moduleSheaf R N}
    (h : ∀ (U : Cᵒᵖ) (a : (sectionsFunctor J U).obj (moduleSheaf R A))
      (b : (sectionsFunctor J U).obj (moduleSheaf R B)),
      pairingApp R q U a b = pairingApp R q' U a b) : q = q' := by
  refine hom_ext_sections fun U s ↦ ?_
  rw [← Functor.prodObjMk_map_fst_map_snd (P := sectionsFunctor J U)
    (A := moduleSheaf R A) (B := moduleSheaf R B) s]
  exact h U _ _

/-- A morphism from the product of the underlying sheaves of sets of two sheaves of modules to
that of a third is **bilinear** when, on local sections, it is additive and compatible with
scalar multiplication in each of its two arguments. This is the condition defining
`Bilin_O(A × B, N)` in Stacks 18.26. -/
@[stacks_fixed 0GIG "the definition of the section: a bilinear map `F × G → H` of sheaves of
modules is a map of the underlying sheaves of sets whose induced map `F(U) × G(U) → H(U)` on
sections is `O_X(U)`-bilinear for every `U`. Over an arbitrary site rather than only the opens
of a ringed space, and over a not necessarily commutative sheaf of rings"]
structure IsBilinearPairing (q : moduleSheaf R A ⨯ moduleSheaf R B ⟶ moduleSheaf R N) :
    Prop where
  /-- The pairing is additive in its first argument. -/
  add_left : ∀ (U : Cᵒᵖ) (a a' : (sectionsFunctor J U).obj (moduleSheaf R A))
    (b : (sectionsFunctor J U).obj (moduleSheaf R B)),
    pairingApp R q U (a + a') b = pairingApp R q U a b + pairingApp R q U a' b
  /-- The pairing is additive in its second argument. -/
  add_right : ∀ (U : Cᵒᵖ) (a : (sectionsFunctor J U).obj (moduleSheaf R A))
    (b b' : (sectionsFunctor J U).obj (moduleSheaf R B)),
    pairingApp R q U a (b + b') = pairingApp R q U a b + pairingApp R q U a b'
  /-- Scalars come out of the first argument of the pairing. -/
  smul_left : ∀ (U : Cᵒᵖ) (r : (sectionsFunctor J U).obj (Sheaf.ringSheaf R))
    (a : (sectionsFunctor J U).obj (moduleSheaf R A))
    (b : (sectionsFunctor J U).obj (moduleSheaf R B)),
    pairingApp R q U (r • a) b = r • pairingApp R q U a b
  /-- Scalars come out of the second argument of the pairing. -/
  smul_right : ∀ (U : Cᵒᵖ) (r : (sectionsFunctor J U).obj (Sheaf.ringSheaf R))
    (a : (sectionsFunctor J U).obj (moduleSheaf R A))
    (b : (sectionsFunctor J U).obj (moduleSheaf R B)),
    pairingApp R q U a (r • b) = r • pairingApp R q U a b

end Pairing

/-! ## Bilinearity as four commuting squares -/

section Squares

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (R : Sheaf J RingCat.{w}) {A B N : SheafOfModules.{w} R}
  (q : moduleSheaf R A ⨯ moduleSheaf R B ⟶ moduleSheaf R N)

/-- Additivity in the first argument of a pairing, as a commuting square of morphisms of
sheaves of sets out of `(A ⨯ A) ⨯ B`. -/
def addLeftSquare : Prop :=
  prod.map (moduleAddHom R A) (𝟙 (moduleSheaf R B)) ≫ q =
    prod.lift (prod.lift (prod.fst ≫ prod.fst) prod.snd ≫ q)
        (prod.lift (prod.fst ≫ prod.snd) prod.snd ≫ q) ≫ moduleAddHom R N

/-- Additivity in the second argument of a pairing, as a commuting square of morphisms of
sheaves of sets out of `A ⨯ (B ⨯ B)`. -/
def addRightSquare : Prop :=
  prod.map (𝟙 (moduleSheaf R A)) (moduleAddHom R B) ≫ q =
    prod.lift (prod.lift prod.fst (prod.snd ≫ prod.fst) ≫ q)
        (prod.lift prod.fst (prod.snd ≫ prod.snd) ≫ q) ≫ moduleAddHom R N

/-- Compatibility with scalars in the first argument of a pairing, as a commuting square of
morphisms of sheaves of sets out of `(R ⨯ A) ⨯ B`. -/
def smulLeftSquare : Prop :=
  prod.map (moduleSMulHom R A) (𝟙 (moduleSheaf R B)) ≫ q =
    prod.lift (prod.fst ≫ prod.fst) (prod.lift (prod.fst ≫ prod.snd) prod.snd ≫ q) ≫
      moduleSMulHom R N

/-- Compatibility with scalars in the second argument of a pairing, as a commuting square of
morphisms of sheaves of sets out of `A ⨯ (R ⨯ B)`. -/
def smulRightSquare : Prop :=
  prod.map (𝟙 (moduleSheaf R A)) (moduleSMulHom R B) ≫ q =
    prod.lift (prod.snd ≫ prod.fst) (prod.lift prod.fst (prod.snd ≫ prod.snd) ≫ q) ≫
      moduleSMulHom R N

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- The square form of additivity in the first argument holds if and only if the pairing is
additive in its first argument on local sections. -/
lemma addLeftSquare_iff :
    addLeftSquare R q ↔ ∀ (U : Cᵒᵖ) (a a' : (sectionsFunctor J U).obj (moduleSheaf R A))
      (b : (sectionsFunctor J U).obj (moduleSheaf R B)),
      pairingApp R q U (a + a') b = pairingApp R q U a b + pairingApp R q U a' b := by
  unfold addLeftSquare
  rw [eq_iff_forall_prodProd]
  simp only [pairingApp, Functor.map_comp_apply, Functor.map_prodMap_apply,
    Functor.map_lift_apply, Functor.map_fst_prodObjMk, Functor.map_snd_prodObjMk,
    CategoryTheory.Functor.map_id, types_id_apply, sectionsFunctor_map_moduleAddHom]

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- The square form of additivity in the second argument holds if and only if the pairing is
additive in its second argument on local sections. -/
lemma addRightSquare_iff :
    addRightSquare R q ↔ ∀ (U : Cᵒᵖ) (a : (sectionsFunctor J U).obj (moduleSheaf R A))
      (b b' : (sectionsFunctor J U).obj (moduleSheaf R B)),
      pairingApp R q U a (b + b') = pairingApp R q U a b + pairingApp R q U a b' := by
  unfold addRightSquare
  rw [eq_iff_forall_prodProd']
  simp only [pairingApp, Functor.map_comp_apply, Functor.map_prodMap_apply,
    Functor.map_lift_apply, Functor.map_fst_prodObjMk, Functor.map_snd_prodObjMk,
    CategoryTheory.Functor.map_id, types_id_apply, sectionsFunctor_map_moduleAddHom]

/-- The square form of compatibility with scalars in the first argument holds if and only if
scalars come out of the first argument of the pairing on local sections. -/
lemma smulLeftSquare_iff :
    smulLeftSquare R q ↔ ∀ (U : Cᵒᵖ) (r : (sectionsFunctor J U).obj (Sheaf.ringSheaf R))
      (a : (sectionsFunctor J U).obj (moduleSheaf R A))
      (b : (sectionsFunctor J U).obj (moduleSheaf R B)),
      pairingApp R q U (r • a) b = r • pairingApp R q U a b := by
  unfold smulLeftSquare
  rw [eq_iff_forall_prodProd]
  simp only [pairingApp, Functor.map_comp_apply, Functor.map_prodMap_apply,
    Functor.map_lift_apply, Functor.map_fst_prodObjMk, Functor.map_snd_prodObjMk,
    CategoryTheory.Functor.map_id, types_id_apply, sectionsFunctor_map_moduleSMulHom]

/-- The square form of compatibility with scalars in the second argument holds if and only if
scalars come out of the second argument of the pairing on local sections. -/
lemma smulRightSquare_iff :
    smulRightSquare R q ↔ ∀ (U : Cᵒᵖ) (r : (sectionsFunctor J U).obj (Sheaf.ringSheaf R))
      (a : (sectionsFunctor J U).obj (moduleSheaf R A))
      (b : (sectionsFunctor J U).obj (moduleSheaf R B)),
      pairingApp R q U a (r • b) = r • pairingApp R q U a b := by
  unfold smulRightSquare
  rw [eq_iff_forall_prodProd']
  simp only [pairingApp, Functor.map_comp_apply, Functor.map_prodMap_apply,
    Functor.map_lift_apply, Functor.map_fst_prodObjMk, Functor.map_snd_prodObjMk,
    CategoryTheory.Functor.map_id, types_id_apply, sectionsFunctor_map_moduleSMulHom]
  exact ⟨fun h U r a b ↦ h U a r b, fun h U a r b ↦ h U r a b⟩

/-- Bilinearity of a pairing is equivalent to the four commuting squares. -/
@[stacks 0GIG "the second characterisation of the section: a pairing is bilinear if and only if
certain diagrams of maps of sheaves of sets commute, imitating the usual axioms for bilinear
maps of modules. The diagram displayed in the section, for `f(x + y, z) = f(x, z) + f(y, z)`,
is `addLeftSquare`. Over an arbitrary site rather than only the opens of a ringed space"]
lemma isBilinearPairing_iff_squares :
    IsBilinearPairing R q ↔ addLeftSquare R q ∧ addRightSquare R q ∧
      smulLeftSquare R q ∧ smulRightSquare R q := by
  rw [addLeftSquare_iff, addRightSquare_iff, smulLeftSquare_iff, smulRightSquare_iff]
  exact ⟨fun h ↦ ⟨h.add_left, h.add_right, h.smul_left, h.smul_right⟩,
    fun h ↦ ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩

end Squares

/-! ## Bilinear pairings and the objectwise tensor product -/

section PresheafTensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  {O : Cᵒᵖ ⥤ CommRingCat.{w}} {hO : Presheaf.IsSheaf J
    (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf O)}
  {A B N : SheafOfModules.{w} (commRingSheaf J O hO)}

/-- The pairing of local sections determined by a morphism out of the objectwise tensor
product of the underlying presheaves of modules: pair two sections and take their tensor. -/
def pairingOfTensorHom (t : A.val ⊗ B.val ⟶ N.val) :
    moduleSheaf (commRingSheaf J O hO) A ⨯ moduleSheaf (commRingSheaf J O hO) B ⟶
      moduleSheaf (commRingSheaf J O hO) N :=
  binaryOpHom (fun U (a : A.val.obj U) (b : B.val.obj U) ↦
      t.app U (a ⊗ₜ[(O ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj U] b))
    (fun {U _} g a b ↦ (PresheafOfModules.naturality_apply t g
      (a ⊗ₜ[(O ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj U] b)).symm)

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- The pairing determined by `t` sends local sections `a` and `b` over `U` to `t` applied to
`a ⊗ₜ b`. -/
@[simp]
lemma pairingApp_pairingOfTensorHom (t : A.val ⊗ B.val ⟶ N.val) (U : Cᵒᵖ)
    (a : A.val.obj U) (b : B.val.obj U) :
    pairingApp (commRingSheaf J O hO) (pairingOfTensorHom t) U a b =
      t.app U (a ⊗ₜ[(O ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj U] b) :=
  sectionsFunctor_map_binaryOpHom
    (A := moduleSheaf (commRingSheaf J O hO) A)
    (B := moduleSheaf (commRingSheaf J O hO) B)
    (E := moduleSheaf (commRingSheaf J O hO) N) _ _ U a b

/-- The pairing determined by a morphism out of the objectwise tensor product is bilinear. -/
lemma isBilinearPairing_pairingOfTensorHom (t : A.val ⊗ B.val ⟶ N.val) :
    IsBilinearPairing (commRingSheaf J O hO) (pairingOfTensorHom t) where
  add_left U a a' b := by
    rw [pairingApp_pairingOfTensorHom t U (a + a') b,
      pairingApp_pairingOfTensorHom t U a b, pairingApp_pairingOfTensorHom t U a' b]
    exact map_add_tmul (t.app U).hom a a' b
  add_right U a b b' := by
    rw [pairingApp_pairingOfTensorHom t U a (b + b'),
      pairingApp_pairingOfTensorHom t U a b, pairingApp_pairingOfTensorHom t U a b']
    exact map_tmul_add (t.app U).hom a b b'
  smul_left U r a b := by
    rw [pairingApp_pairingOfTensorHom t U (r • a) b, pairingApp_pairingOfTensorHom t U a b]
    exact Stacks.RingedSpace.map_smul_tmul (t.app U).hom r a b
  smul_right U r a b := by
    rw [pairingApp_pairingOfTensorHom t U a (r • b), pairingApp_pairingOfTensorHom t U a b]
    exact Stacks.RingedSpace.map_tmul_smul (t.app U).hom r a b

/-- The morphism out of the objectwise tensor product of the underlying presheaves of modules
determined by a bilinear pairing of local sections. -/
def tensorHomOfPairing
    {q : moduleSheaf (commRingSheaf J O hO) A ⨯ moduleSheaf (commRingSheaf J O hO) B ⟶
      moduleSheaf (commRingSheaf J O hO) N}
    (hq : IsBilinearPairing (commRingSheaf J O hO) q) : A.val ⊗ B.val ⟶ N.val where
  app U := ModuleCat.MonoidalCategory.tensorLift
    (fun (a : A.val.obj U) (b : B.val.obj U) ↦ pairingApp (commRingSheaf J O hO) q U a b)
    (hq.add_left U) (hq.smul_left U) (hq.add_right U) (hq.smul_right U)
  naturality {_ _} g := ModuleCat.MonoidalCategory.tensor_ext fun a b ↦
    (pairingApp_naturality (commRingSheaf J O hO) q g a b).symm

/-- The morphism determined by a bilinear pairing `q` sends `a ⊗ₜ b` over `U` to the pairing of
`a` and `b` under `q`. -/
@[simp]
lemma tensorHomOfPairing_app_tmul
    {q : moduleSheaf (commRingSheaf J O hO) A ⨯ moduleSheaf (commRingSheaf J O hO) B ⟶
      moduleSheaf (commRingSheaf J O hO) N}
    (hq : IsBilinearPairing (commRingSheaf J O hO) q) (U : Cᵒᵖ)
    (a : A.val.obj U) (b : B.val.obj U) :
    (tensorHomOfPairing hq).app U
        (a ⊗ₜ[(O ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj U] b) =
      pairingApp (commRingSheaf J O hO) q U a b := rfl

/-- **The universal property of the objectwise tensor product**: bilinear pairings of the
underlying sheaves of sets of `A` and `B` with values in `N` are the same thing as morphisms
of presheaves of modules out of the objectwise tensor product `A ⊗ B`. -/
def bilinearEquivPresheafTensorHom :
    { q : moduleSheaf (commRingSheaf J O hO) A ⨯ moduleSheaf (commRingSheaf J O hO) B ⟶
        moduleSheaf (commRingSheaf J O hO) N //
      IsBilinearPairing (commRingSheaf J O hO) q } ≃ (A.val ⊗ B.val ⟶ N.val) where
  toFun q := tensorHomOfPairing q.2
  invFun t := ⟨pairingOfTensorHom t, isBilinearPairing_pairingOfTensorHom t⟩
  left_inv q := Subtype.ext (pairing_ext _ fun U a b ↦
    pairingApp_pairingOfTensorHom (tensorHomOfPairing q.2) U a b)
  right_inv t := PresheafOfModules.hom_ext fun U ↦
    ModuleCat.MonoidalCategory.tensor_ext fun a b ↦
      pairingApp_pairingOfTensorHom t U a b

end PresheafTensor

/-! ## Bilinear pairings and the tensor product sheaf -/

section SheafTensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {O : Sheaf J CommRingCat.{w}}

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- The sheaf of rings underlying a sheaf of commutative rings, presented as the underlying
sheaf of rings of a presheaf of commutative rings; the two agree by definition. -/
lemma commRingSheaf_eq_underlyingRingSheafOfSite :
    commRingSheaf J O.obj (Stacks.SheafOfModules.Tensor.ringSheaf O).property =
      Stacks.SheafOfModules.Tensor.ringSheaf O := rfl

variable {A B N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}

/-- Morphisms of sheaves of modules out of the tensor product sheaf `A ⊗_O B` of Tag 0GMW are
the same thing as morphisms of presheaves of modules out of the objectwise tensor product of
the underlying presheaves: the tensor product sheaf is the sheafification of the latter. -/
def tensorHomEquivPresheafTensorHom :
    (((Stacks.SheafOfModules.Tensor.sheafTensor O).obj A).obj B ⟶ N) ≃ (A.val ⊗ B.val ⟶ N.val) :=
  PresheafOfModules.sheafificationHomEquiv (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)

/-- **The tensor product of sheaves of modules represents bilinear maps.** This is the
identification `Hom_O(A ⊗_O B, N) = Bilin_O(A × B, N)` of bilinear pairings of `A` and `B`
with values in `N` with morphisms out of the tensor product sheaf. -/
def bilinearEquivTensorHom :
    { q : moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O) A ⨯
        moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O) B ⟶
          moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O) N //
      IsBilinearPairing (Stacks.SheafOfModules.Tensor.ringSheaf O) q } ≃
      (((Stacks.SheafOfModules.Tensor.sheafTensor O).obj A).obj B ⟶ N) :=
  (bilinearEquivPresheafTensorHom
    (hO := (Stacks.SheafOfModules.Tensor.ringSheaf O).property)).trans
      tensorHomEquivPresheafTensorHom.symm

/-- **The universal bilinear pairing.** Two local sections of `A` and of `B` are paired to the
image, under the sheafification unit, of their tensor; the result is a local section of the
tensor product sheaf `A ⊗_O B`. Every bilinear pairing factors uniquely through this one, by
`bilinearEquivTensorHom`. -/
def tensorSectionPairing (A B : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O) A ⨯
        moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O) B ⟶
      moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O)
        (((Stacks.SheafOfModules.Tensor.sheafTensor O).obj A).obj B) :=
  pairingOfTensorHom (hO := (Stacks.SheafOfModules.Tensor.ringSheaf O).property)
    ((PresheafOfModules.sheafificationAdjunction (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
      (PresheafOfModules.tensorObj A.val B.val))

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget RingCat.{w})] in
/-- The universal pairing sends a pair of local sections to the sheafification-unit image of
their tensor. -/
lemma pairingApp_tensorSectionPairing
    (A B : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (U : Cᵒᵖ) (a : A.val.obj U) (b : B.val.obj U) :
    pairingApp (Stacks.SheafOfModules.Tensor.ringSheaf O) (tensorSectionPairing A B) U a b =
      ((PresheafOfModules.sheafificationAdjunction (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
      (PresheafOfModules.tensorObj A.val B.val)).app U (a ⊗ₜ[O.obj.obj U] b) :=
  pairingApp_pairingOfTensorHom
    (hO := (Stacks.SheafOfModules.Tensor.ringSheaf O).property) _ U a b

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The universal pairing is bilinear. -/
lemma isBilinearPairing_tensorSectionPairing
    (A B : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    IsBilinearPairing (Stacks.SheafOfModules.Tensor.ringSheaf O) (tensorSectionPairing A B) :=
  isBilinearPairing_pairingOfTensorHom
    (hO := (Stacks.SheafOfModules.Tensor.ringSheaf O).property) _

end SheafTensor

end Stacks.SheafOfModules

end
