module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorBilinear
public import StacksCore.Tactic.StacksAttribute

/-! # Trilinear pairings of the underlying sheaves of sets

Let `(C, J)` be a site, let `R` be a sheaf of rings on it and let `A`, `B`, `D`, `N` be sheaves
of `R`-modules. `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorBilinear` introduces the set
`Bilin_R(A × B, N)` of morphisms `A × B ⟶ N` of the underlying sheaves of sets which are
`R`-bilinear, as `Stacks.SheafOfModules.IsBilinearPairing`, and proves it equivalent to four
commuting squares of morphisms of sheaves of sets.

This file is the **three-variable form**: `Stacks.SheafOfModules.IsTrilinearPairing` is
trilinearity of a morphism `(A ⨯ B) ⨯ D ⟶ N` of underlying sheaves of sets, and
`Stacks.SheafOfModules.isTrilinearPairing_iff_squares` proves it equivalent to **six** commuting
squares. Where the four binary squares live over triple products, the six ternary ones live over
*quadruple* products, in the three shapes `((X ⨯ Y) ⨯ Z) ⨯ T`, `(X ⨯ (Y ⨯ Z)) ⨯ T` and
`(X ⨯ Y) ⨯ (Z ⨯ T)`; one extensionality lemma per shape is proved first, each by bundling two
factors and appealing to the triple-product extensionality
`Stacks.SheafOfModules.hom_ext_prodProd` of the binary file.

The point of the square form, here as in the binary case, is that it is the form which
transports across the adjunction `f⁻¹ ⊣ f_*` of a morphism of topoi, where neither `f⁻¹` nor
`f_*` has any description on sections; the transport of these squares is the binary
`Stacks.SheafOfModules.square_transport_iff`, as carried out in
`Stacks.SheafOfModules.inverseImageTrilinearEquiv`. For the same reason
`SheafOfModules.TrilinearMap` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroBilinear` cannot be used in place of
`IsTrilinearPairing`: it presents a trilinear map by its values on sections, and `f⁻¹F` along a
`CategoryTheory.Sheaf.MorphismOfTopoi` has no description on sections.

## Main definitions

* `Stacks.SheafOfModules.pairingApp₃`: the value of a triple pairing of the underlying sheaves
  of sets on a triple of local sections.
* `Stacks.SheafOfModules.IsTrilinearPairing`: trilinearity of such a pairing.
* `Stacks.SheafOfModules.addLeftSquare₃`, `addMidSquare₃`, `addRightSquare₃`,
  `smulLeftSquare₃`, `smulMidSquare₃`, `smulRightSquare₃`: the six trilinearity conditions as
  commuting squares of morphisms of sheaves of sets out of quadruple products.

## Main results

* `Stacks.SheafOfModules.hom_ext_prodProd_left`, `hom_ext_prodProd_mid`,
  `hom_ext_prodProd_right`: two morphisms out of a quadruple product of sheaves of sets agree as
  soon as they agree on all quadruples of local sections.
* `Stacks.SheafOfModules.isTrilinearPairing_iff_squares`: trilinearity on sections is equivalent
  to the six commuting squares. Each of the six individual equivalences
  (`addLeftSquare₃_iff` and its companions) is also available.
* `Stacks.SheafOfModules.pairingApp₃_naturality` and `Stacks.SheafOfModules.pairing₃_ext`.

## Implementation notes

As in the binary file, local sections are spelled `(sectionsFunctor J U).obj (moduleSheaf R A)`
throughout, and the squares are stated at the universal generalized element, i.e. with the
projections of the relevant quadruple product as their arguments.

The third module is called `D` rather than `C`, which names the site.

Each of the six `..._iff` lemmas evaluates its square at the universal generalized element by
`congrArg`. Every `CategoryTheory.Functor.prodObjMk` in that element carries its `A` and `B`
explicitly: without them the elaborator has to solve for the shape of a quadruple product from
the type of the square, and it either times out or leaves the equation's metavariables
unassigned.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules

universe w v u

namespace Stacks.SheafOfModules

section Ext

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Two morphisms of sheaves of sets out of `((X ⨯ Y) ⨯ Z) ⨯ T` agree as soon as they agree on all
quadruples of local sections. -/
lemma hom_ext_prodProd_left {X Y Z T E : Sheaf J (Type w)} {m m' : ((X ⨯ Y) ⨯ Z) ⨯ T ⟶ E}
    (h : ∀ (U : Cᵒᵖ) (x : (sectionsFunctor J U).obj X) (y : (sectionsFunctor J U).obj Y)
      (z : (sectionsFunctor J U).obj Z) (t : (sectionsFunctor J U).obj T),
      (sectionsFunctor J U).map m
          (Functor.prodObjMk (Functor.prodObjMk (Functor.prodObjMk x y) z) t) =
        (sectionsFunctor J U).map m'
          (Functor.prodObjMk (Functor.prodObjMk (Functor.prodObjMk x y) z) t)) :
    m = m' := by
  refine hom_ext_prodProd fun U p z t ↦ ?_
  have key := h U ((sectionsFunctor J U).map prod.fst p)
    ((sectionsFunctor J U).map prod.snd p) z t
  rwa [Functor.prodObjMk_map_fst_map_snd] at key

/-- Two morphisms of sheaves of sets out of `(X ⨯ (Y ⨯ Z)) ⨯ T` agree as soon as they agree on all
quadruples of local sections. -/
lemma hom_ext_prodProd_mid {X Y Z T E : Sheaf J (Type w)} {m m' : (X ⨯ (Y ⨯ Z)) ⨯ T ⟶ E}
    (h : ∀ (U : Cᵒᵖ) (x : (sectionsFunctor J U).obj X) (y : (sectionsFunctor J U).obj Y)
      (z : (sectionsFunctor J U).obj Z) (t : (sectionsFunctor J U).obj T),
      (sectionsFunctor J U).map m
          (Functor.prodObjMk (Functor.prodObjMk x (Functor.prodObjMk y z)) t) =
        (sectionsFunctor J U).map m'
          (Functor.prodObjMk (Functor.prodObjMk x (Functor.prodObjMk y z)) t)) :
    m = m' := by
  refine hom_ext_prodProd fun U x p t ↦ ?_
  have key := h U x ((sectionsFunctor J U).map prod.fst p)
    ((sectionsFunctor J U).map prod.snd p) t
  rwa [Functor.prodObjMk_map_fst_map_snd] at key

/-- Two morphisms of sheaves of sets out of `(X ⨯ Y) ⨯ (Z ⨯ T)` agree as soon as they agree on all
quadruples of local sections. -/
lemma hom_ext_prodProd_right {X Y Z T E : Sheaf J (Type w)} {m m' : (X ⨯ Y) ⨯ (Z ⨯ T) ⟶ E}
    (h : ∀ (U : Cᵒᵖ) (x : (sectionsFunctor J U).obj X) (y : (sectionsFunctor J U).obj Y)
      (z : (sectionsFunctor J U).obj Z) (t : (sectionsFunctor J U).obj T),
      (sectionsFunctor J U).map m
          (Functor.prodObjMk (Functor.prodObjMk x y) (Functor.prodObjMk z t)) =
        (sectionsFunctor J U).map m'
          (Functor.prodObjMk (Functor.prodObjMk x y) (Functor.prodObjMk z t))) :
    m = m' := by
  refine hom_ext_prodProd fun U x y p ↦ ?_
  have key := h U x y ((sectionsFunctor J U).map prod.fst p)
    ((sectionsFunctor J U).map prod.snd p)
  rwa [Functor.prodObjMk_map_fst_map_snd] at key

/-- Two morphisms out of `((X ⨯ Y) ⨯ Z) ⨯ T` are equal iff they agree on all quadruples of local
sections. -/
private lemma eq_iff_forall_prodProd_left {X Y Z T E : Sheaf J (Type w)}
    {m m' : ((X ⨯ Y) ⨯ Z) ⨯ T ⟶ E} :
    m = m' ↔ ∀ (U : Cᵒᵖ) (x : (sectionsFunctor J U).obj X) (y : (sectionsFunctor J U).obj Y)
      (z : (sectionsFunctor J U).obj Z) (t : (sectionsFunctor J U).obj T),
      (sectionsFunctor J U).map m
          (Functor.prodObjMk (Functor.prodObjMk (Functor.prodObjMk x y) z) t) =
        (sectionsFunctor J U).map m'
          (Functor.prodObjMk (Functor.prodObjMk (Functor.prodObjMk x y) z) t) :=
  ⟨fun h U x y z t ↦ by rw [h], hom_ext_prodProd_left⟩

/-- Two morphisms out of `(X ⨯ (Y ⨯ Z)) ⨯ T` are equal iff they agree on all quadruples of local
sections. -/
private lemma eq_iff_forall_prodProd_mid {X Y Z T E : Sheaf J (Type w)}
    {m m' : (X ⨯ (Y ⨯ Z)) ⨯ T ⟶ E} :
    m = m' ↔ ∀ (U : Cᵒᵖ) (x : (sectionsFunctor J U).obj X) (y : (sectionsFunctor J U).obj Y)
      (z : (sectionsFunctor J U).obj Z) (t : (sectionsFunctor J U).obj T),
      (sectionsFunctor J U).map m
          (Functor.prodObjMk (Functor.prodObjMk x (Functor.prodObjMk y z)) t) =
        (sectionsFunctor J U).map m'
          (Functor.prodObjMk (Functor.prodObjMk x (Functor.prodObjMk y z)) t) :=
  ⟨fun h U x y z t ↦ by rw [h], hom_ext_prodProd_mid⟩

/-- Two morphisms out of `(X ⨯ Y) ⨯ (Z ⨯ T)` are equal iff they agree on all quadruples of local
sections. -/
private lemma eq_iff_forall_prodProd_right {X Y Z T E : Sheaf J (Type w)}
    {m m' : (X ⨯ Y) ⨯ (Z ⨯ T) ⟶ E} :
    m = m' ↔ ∀ (U : Cᵒᵖ) (x : (sectionsFunctor J U).obj X) (y : (sectionsFunctor J U).obj Y)
      (z : (sectionsFunctor J U).obj Z) (t : (sectionsFunctor J U).obj T),
      (sectionsFunctor J U).map m
          (Functor.prodObjMk (Functor.prodObjMk x y) (Functor.prodObjMk z t)) =
        (sectionsFunctor J U).map m'
          (Functor.prodObjMk (Functor.prodObjMk x y) (Functor.prodObjMk z t)) :=
  ⟨fun h U x y z t ↦ by rw [h], hom_ext_prodProd_right⟩

end Ext

/-! ## Trilinear pairings of the underlying sheaves of sets -/

section Pairing

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (R : Sheaf J RingCat.{w})

variable {A B D N : SheafOfModules.{w} R}

/-- The value on a triple of local sections of a morphism from the iterated product of the
underlying sheaves of sets of three sheaves of modules. -/
def pairingApp₃
    (p : (moduleSheaf R A ⨯ moduleSheaf R B) ⨯ moduleSheaf R D ⟶ moduleSheaf R N) (U : Cᵒᵖ)
    (a : (sectionsFunctor J U).obj (moduleSheaf R A))
    (b : (sectionsFunctor J U).obj (moduleSheaf R B))
    (c : (sectionsFunctor J U).obj (moduleSheaf R D)) :
    (sectionsFunctor J U).obj (moduleSheaf R N) :=
  (sectionsFunctor J U).map p (Functor.prodObjMk (Functor.prodObjMk a b) c)

variable (p : (moduleSheaf R A ⨯ moduleSheaf R B) ⨯ moduleSheaf R D ⟶ moduleSheaf R N)

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- A triple pairing of the underlying sheaves of sets is compatible with restriction of
sections, spelled through the restriction maps of the sheaves of modules themselves. -/
lemma pairingApp₃_naturality {U V : Cᵒᵖ} (g : U ⟶ V)
    (a : (sectionsFunctor J U).obj (moduleSheaf R A))
    (b : (sectionsFunctor J U).obj (moduleSheaf R B))
    (c : (sectionsFunctor J U).obj (moduleSheaf R D)) :
    N.val.map g (pairingApp₃ R p U a b c) =
      pairingApp₃ R p V (A.val.map g a) (B.val.map g b) (D.val.map g c) := by
  let θ : sectionsFunctor.{w} J U ⟶ sectionsFunctor.{w} J V := sectionsRestrict (J := J) g
  have h₁ := Functor.natTrans_app_map_apply θ p
    (Functor.prodObjMk (P := sectionsFunctor J U)
      (A := moduleSheaf R A ⨯ moduleSheaf R B) (B := moduleSheaf R D)
      (Functor.prodObjMk (P := sectionsFunctor J U)
        (A := moduleSheaf R A) (B := moduleSheaf R B) a b) c)
  have h₂ := Functor.prodObjMk_naturality (Q := sectionsFunctor J V) θ
    (A := moduleSheaf R A ⨯ moduleSheaf R B) (B := moduleSheaf R D)
    (Functor.prodObjMk (P := sectionsFunctor J U)
      (A := moduleSheaf R A) (B := moduleSheaf R B) a b) c
  have h₃ := Functor.prodObjMk_naturality (Q := sectionsFunctor J V) θ
    (A := moduleSheaf R A) (B := moduleSheaf R B) a b
  rw [h₃] at h₂
  rwa [h₂] at h₁

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- Two triple pairings of the underlying sheaves of sets agree as soon as they agree on all
triples of local sections. -/
lemma pairing₃_ext
    {p p' : (moduleSheaf R A ⨯ moduleSheaf R B) ⨯ moduleSheaf R D ⟶ moduleSheaf R N}
    (h : ∀ (U : Cᵒᵖ) (a : (sectionsFunctor J U).obj (moduleSheaf R A))
      (b : (sectionsFunctor J U).obj (moduleSheaf R B))
      (c : (sectionsFunctor J U).obj (moduleSheaf R D)),
      pairingApp₃ R p U a b c = pairingApp₃ R p' U a b c) : p = p' :=
  hom_ext_prodProd fun U a b c ↦ h U a b c

/-- A morphism from the iterated product of the underlying sheaves of sets of three sheaves of
modules to that of a fourth is **trilinear** when, on local sections, it is additive and
compatible with scalar multiplication in each of its three arguments. This is the condition
defining `Trilin_O(A × B × C, N)`, the three-variable form of
`Stacks.SheafOfModules.IsBilinearPairing`. -/
structure IsTrilinearPairing
    (p : (moduleSheaf R A ⨯ moduleSheaf R B) ⨯ moduleSheaf R D ⟶ moduleSheaf R N) : Prop where
  /-- The pairing is additive in its first argument. -/
  add_left : ∀ (U : Cᵒᵖ) (a a' : (sectionsFunctor J U).obj (moduleSheaf R A))
    (b : (sectionsFunctor J U).obj (moduleSheaf R B))
    (c : (sectionsFunctor J U).obj (moduleSheaf R D)),
    pairingApp₃ R p U (a + a') b c = pairingApp₃ R p U a b c + pairingApp₃ R p U a' b c
  /-- The pairing is additive in its second argument. -/
  add_mid : ∀ (U : Cᵒᵖ) (a : (sectionsFunctor J U).obj (moduleSheaf R A))
    (b b' : (sectionsFunctor J U).obj (moduleSheaf R B))
    (c : (sectionsFunctor J U).obj (moduleSheaf R D)),
    pairingApp₃ R p U a (b + b') c = pairingApp₃ R p U a b c + pairingApp₃ R p U a b' c
  /-- The pairing is additive in its third argument. -/
  add_right : ∀ (U : Cᵒᵖ) (a : (sectionsFunctor J U).obj (moduleSheaf R A))
    (b : (sectionsFunctor J U).obj (moduleSheaf R B))
    (c c' : (sectionsFunctor J U).obj (moduleSheaf R D)),
    pairingApp₃ R p U a b (c + c') = pairingApp₃ R p U a b c + pairingApp₃ R p U a b c'
  /-- Scalars come out of the first argument of the pairing. -/
  smul_left : ∀ (U : Cᵒᵖ) (r : (sectionsFunctor J U).obj (Sheaf.ringSheaf R))
    (a : (sectionsFunctor J U).obj (moduleSheaf R A))
    (b : (sectionsFunctor J U).obj (moduleSheaf R B))
    (c : (sectionsFunctor J U).obj (moduleSheaf R D)),
    pairingApp₃ R p U (r • a) b c = r • pairingApp₃ R p U a b c
  /-- Scalars come out of the second argument of the pairing. -/
  smul_mid : ∀ (U : Cᵒᵖ) (r : (sectionsFunctor J U).obj (Sheaf.ringSheaf R))
    (a : (sectionsFunctor J U).obj (moduleSheaf R A))
    (b : (sectionsFunctor J U).obj (moduleSheaf R B))
    (c : (sectionsFunctor J U).obj (moduleSheaf R D)),
    pairingApp₃ R p U a (r • b) c = r • pairingApp₃ R p U a b c
  /-- Scalars come out of the third argument of the pairing. -/
  smul_right : ∀ (U : Cᵒᵖ) (r : (sectionsFunctor J U).obj (Sheaf.ringSheaf R))
    (a : (sectionsFunctor J U).obj (moduleSheaf R A))
    (b : (sectionsFunctor J U).obj (moduleSheaf R B))
    (c : (sectionsFunctor J U).obj (moduleSheaf R D)),
    pairingApp₃ R p U a b (r • c) = r • pairingApp₃ R p U a b c

end Pairing

/-! ## Trilinearity as six commuting squares -/

section Squares

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (R : Sheaf J RingCat.{w}) {A B D N : SheafOfModules.{w} R}
  (p : (moduleSheaf R A ⨯ moduleSheaf R B) ⨯ moduleSheaf R D ⟶ moduleSheaf R N)

/-- Additivity in the first argument of a triple pairing, as a commuting square of morphisms
of sheaves of sets out of `((A ⨯ A) ⨯ B) ⨯ C`. -/
def addLeftSquare₃ : Prop :=
  prod.map (prod.map (moduleAddHom R A) (𝟙 (moduleSheaf R B))) (𝟙 (moduleSheaf R D)) ≫ p =
    prod.lift
        (prod.lift (prod.lift (prod.fst ≫ prod.fst ≫ prod.fst) (prod.fst ≫ prod.snd))
          prod.snd ≫ p)
        (prod.lift (prod.lift (prod.fst ≫ prod.fst ≫ prod.snd) (prod.fst ≫ prod.snd))
          prod.snd ≫ p) ≫
      moduleAddHom R N

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- The square form of additivity in the first argument holds if and only if the pairing is
additive in its first argument on local sections. -/
lemma addLeftSquare₃_iff :
    addLeftSquare₃ R p ↔ ∀ (U : Cᵒᵖ) (a a' : (sectionsFunctor J U).obj (moduleSheaf R A))
      (b : (sectionsFunctor J U).obj (moduleSheaf R B))
      (c : (sectionsFunctor J U).obj (moduleSheaf R D)),
      pairingApp₃ R p U (a + a') b c = pairingApp₃ R p U a b c + pairingApp₃ R p U a' b c := by
  unfold addLeftSquare₃
  rw [eq_iff_forall_prodProd_left]
  simp only [pairingApp₃, Functor.map_comp_apply, Functor.map_prodMap_apply,
    Functor.map_lift_apply, Functor.map_fst_prodObjMk, Functor.map_snd_prodObjMk,
    CategoryTheory.Functor.map_id, types_id_apply, sectionsFunctor_map_moduleAddHom]

/-- Additivity in the second argument of a triple pairing, as a commuting square of morphisms
of sheaves of sets out of `(A ⨯ (B ⨯ B)) ⨯ C`. -/
def addMidSquare₃ : Prop :=
  prod.map (prod.map (𝟙 (moduleSheaf R A)) (moduleAddHom R B)) (𝟙 (moduleSheaf R D)) ≫ p =
    prod.lift
        (prod.lift (prod.lift (prod.fst ≫ prod.fst) (prod.fst ≫ prod.snd ≫ prod.fst))
          prod.snd ≫ p)
        (prod.lift (prod.lift (prod.fst ≫ prod.fst) (prod.fst ≫ prod.snd ≫ prod.snd))
          prod.snd ≫ p) ≫
      moduleAddHom R N

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- The square form of additivity in the second argument holds if and only if the pairing is
additive in its second argument on local sections. -/
lemma addMidSquare₃_iff :
    addMidSquare₃ R p ↔ ∀ (U : Cᵒᵖ) (a : (sectionsFunctor J U).obj (moduleSheaf R A))
      (b b' : (sectionsFunctor J U).obj (moduleSheaf R B))
      (c : (sectionsFunctor J U).obj (moduleSheaf R D)),
      pairingApp₃ R p U a (b + b') c = pairingApp₃ R p U a b c + pairingApp₃ R p U a b' c := by
  unfold addMidSquare₃
  rw [eq_iff_forall_prodProd_mid]
  simp only [pairingApp₃, Functor.map_comp_apply, Functor.map_prodMap_apply,
    Functor.map_lift_apply, Functor.map_fst_prodObjMk, Functor.map_snd_prodObjMk,
    CategoryTheory.Functor.map_id, types_id_apply, sectionsFunctor_map_moduleAddHom]

/-- Additivity in the third argument of a triple pairing, as a commuting square of morphisms
of sheaves of sets out of `(A ⨯ B) ⨯ (C ⨯ C)`. -/
def addRightSquare₃ : Prop :=
  prod.map (𝟙 (moduleSheaf R A ⨯ moduleSheaf R B)) (moduleAddHom R D) ≫ p =
    prod.lift
        (prod.lift (prod.lift (prod.fst ≫ prod.fst) (prod.fst ≫ prod.snd))
          (prod.snd ≫ prod.fst) ≫ p)
        (prod.lift (prod.lift (prod.fst ≫ prod.fst) (prod.fst ≫ prod.snd))
          (prod.snd ≫ prod.snd) ≫ p) ≫
      moduleAddHom R N

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- The square form of additivity in the third argument holds if and only if the pairing is
additive in its third argument on local sections. -/
lemma addRightSquare₃_iff :
    addRightSquare₃ R p ↔ ∀ (U : Cᵒᵖ) (a : (sectionsFunctor J U).obj (moduleSheaf R A))
      (b : (sectionsFunctor J U).obj (moduleSheaf R B))
      (c c' : (sectionsFunctor J U).obj (moduleSheaf R D)),
      pairingApp₃ R p U a b (c + c') = pairingApp₃ R p U a b c + pairingApp₃ R p U a b c' := by
  unfold addRightSquare₃
  rw [eq_iff_forall_prodProd_right]
  simp only [pairingApp₃, Functor.map_comp_apply, Functor.map_prodMap_apply,
    Functor.map_lift_apply, Functor.map_fst_prodObjMk, Functor.map_snd_prodObjMk,
    CategoryTheory.Functor.map_id, types_id_apply, sectionsFunctor_map_moduleAddHom]

/-- Compatibility with scalars in the first argument of a triple pairing, as a commuting square
of morphisms of sheaves of sets out of `((R ⨯ A) ⨯ B) ⨯ C`. -/
def smulLeftSquare₃ : Prop :=
  prod.map (prod.map (moduleSMulHom R A) (𝟙 (moduleSheaf R B))) (𝟙 (moduleSheaf R D)) ≫ p =
    prod.lift (prod.fst ≫ prod.fst ≫ prod.fst)
        (prod.lift (prod.lift (prod.fst ≫ prod.fst ≫ prod.snd) (prod.fst ≫ prod.snd))
          prod.snd ≫ p) ≫
      moduleSMulHom R N

/-- The square form of compatibility with scalars in the first argument holds if and only if
scalars come out of the first argument of the pairing on local sections. -/
lemma smulLeftSquare₃_iff :
    smulLeftSquare₃ R p ↔ ∀ (U : Cᵒᵖ) (r : (sectionsFunctor J U).obj (Sheaf.ringSheaf R))
      (a : (sectionsFunctor J U).obj (moduleSheaf R A))
      (b : (sectionsFunctor J U).obj (moduleSheaf R B))
      (c : (sectionsFunctor J U).obj (moduleSheaf R D)),
      pairingApp₃ R p U (r • a) b c = r • pairingApp₃ R p U a b c := by
  unfold smulLeftSquare₃
  rw [eq_iff_forall_prodProd_left]
  simp only [pairingApp₃, Functor.map_comp_apply, Functor.map_prodMap_apply,
    Functor.map_lift_apply, Functor.map_fst_prodObjMk, Functor.map_snd_prodObjMk,
    CategoryTheory.Functor.map_id, types_id_apply, sectionsFunctor_map_moduleSMulHom]

/-- Compatibility with scalars in the second argument of a triple pairing, as a commuting
square of morphisms of sheaves of sets out of `(A ⨯ (R ⨯ B)) ⨯ C`. -/
def smulMidSquare₃ : Prop :=
  prod.map (prod.map (𝟙 (moduleSheaf R A)) (moduleSMulHom R B)) (𝟙 (moduleSheaf R D)) ≫ p =
    prod.lift (prod.fst ≫ prod.snd ≫ prod.fst)
        (prod.lift (prod.lift (prod.fst ≫ prod.fst) (prod.fst ≫ prod.snd ≫ prod.snd))
          prod.snd ≫ p) ≫
      moduleSMulHom R N

/-- The square form of compatibility with scalars in the second argument holds if and only if
scalars come out of the second argument of the pairing on local sections. -/
lemma smulMidSquare₃_iff :
    smulMidSquare₃ R p ↔ ∀ (U : Cᵒᵖ) (r : (sectionsFunctor J U).obj (Sheaf.ringSheaf R))
      (a : (sectionsFunctor J U).obj (moduleSheaf R A))
      (b : (sectionsFunctor J U).obj (moduleSheaf R B))
      (c : (sectionsFunctor J U).obj (moduleSheaf R D)),
      pairingApp₃ R p U a (r • b) c = r • pairingApp₃ R p U a b c := by
  unfold smulMidSquare₃
  rw [eq_iff_forall_prodProd_mid]
  simp only [pairingApp₃, Functor.map_comp_apply, Functor.map_prodMap_apply,
    Functor.map_lift_apply, Functor.map_fst_prodObjMk, Functor.map_snd_prodObjMk,
    CategoryTheory.Functor.map_id, types_id_apply, sectionsFunctor_map_moduleSMulHom]
  exact ⟨fun h U r a b c ↦ h U a r b c, fun h U a r b c ↦ h U r a b c⟩

/-- Compatibility with scalars in the third argument of a triple pairing, as a commuting square
of morphisms of sheaves of sets out of `(A ⨯ B) ⨯ (R ⨯ C)`. -/
def smulRightSquare₃ : Prop :=
  prod.map (𝟙 (moduleSheaf R A ⨯ moduleSheaf R B)) (moduleSMulHom R D) ≫ p =
    prod.lift (prod.snd ≫ prod.fst)
        (prod.lift (prod.lift (prod.fst ≫ prod.fst) (prod.fst ≫ prod.snd))
          (prod.snd ≫ prod.snd) ≫ p) ≫
      moduleSMulHom R N

/-- The square form of compatibility with scalars in the third argument holds if and only if
scalars come out of the third argument of the pairing on local sections. -/
lemma smulRightSquare₃_iff :
    smulRightSquare₃ R p ↔ ∀ (U : Cᵒᵖ) (r : (sectionsFunctor J U).obj (Sheaf.ringSheaf R))
      (a : (sectionsFunctor J U).obj (moduleSheaf R A))
      (b : (sectionsFunctor J U).obj (moduleSheaf R B))
      (c : (sectionsFunctor J U).obj (moduleSheaf R D)),
      pairingApp₃ R p U a b (r • c) = r • pairingApp₃ R p U a b c := by
  unfold smulRightSquare₃
  rw [eq_iff_forall_prodProd_right]
  simp only [pairingApp₃, Functor.map_comp_apply, Functor.map_prodMap_apply,
    Functor.map_lift_apply, Functor.map_fst_prodObjMk, Functor.map_snd_prodObjMk,
    CategoryTheory.Functor.map_id, types_id_apply, sectionsFunctor_map_moduleSMulHom]
  exact ⟨fun h U r a b c ↦ h U a b r c, fun h U a b r c ↦ h U r a b c⟩

/-- **Trilinearity of a pairing is equivalent to the six commuting squares.** The
three-variable form of `Stacks.SheafOfModules.isBilinearPairing_iff_squares`. -/
lemma isTrilinearPairing_iff_squares :
    IsTrilinearPairing R p ↔ addLeftSquare₃ R p ∧ addMidSquare₃ R p ∧ addRightSquare₃ R p ∧
      smulLeftSquare₃ R p ∧ smulMidSquare₃ R p ∧ smulRightSquare₃ R p := by
  rw [addLeftSquare₃_iff, addMidSquare₃_iff, addRightSquare₃_iff, smulLeftSquare₃_iff,
    smulMidSquare₃_iff, smulRightSquare₃_iff]
  exact ⟨fun h ↦ ⟨h.add_left, h.add_mid, h.add_right, h.smul_left, h.smul_mid, h.smul_right⟩,
    fun h ↦ ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩⟩

end Squares

end Stacks.SheafOfModules

end

