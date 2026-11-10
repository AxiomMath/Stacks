module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.SimplicialPseudoFamily

/-!
# The category of pairs of a pseudofunctorial family over the simplex category

For a `CategoryTheory.SimplicialPseudoFamily` `P`, a *pair* is an object `F` of `C_0` with an
isomorphism `α : f_{δ¹₁}^* F ≅ f_{δ¹₀}^* F` satisfying the cocycle condition, and a morphism of
pairs is a morphism of the objects of `C_0` intertwining the isomorphisms. A cartesian system
`(N_n, f_φ^* N_m ≅ N_n)` of `P` determines a pair: its object in degree zero with the comparison
`f_{δ¹₁}^* N_0 ≅ N_1 ≅ f_{δ¹₀}^* N_0` of its two transitions to degree one. This file proves that
this comparison satisfies the cocycle condition, once and for all families. It is the part of
the proof of Stacks 07TH that does not depend on the family.

## Main definitions

* `CategoryTheory.SimplicialPseudoFamily.Pair`: the category of pairs.
* `CategoryTheory.SimplicialPseudoFamily.CartesianSystem.pairIso`: the comparison isomorphism of
  a cartesian system.
* `CategoryTheory.SimplicialPseudoFamily.CartesianSystem.toPair`: the pair of a cartesian system.

## Main results

* `CategoryTheory.SimplicialPseudoFamily.CartesianSystem.isCocycle_pairIso`: the comparison
  isomorphism of a cartesian system satisfies the cocycle condition.
* `CategoryTheory.SimplicialPseudoFamily.toPairIsoOfIsoPairSystem`: a cartesian system identified,
  compatibly with the transitions, with the system of a pair has that pair as its pair.

## References

* [Stacks Project, Tag 07TH](https://stacks.math.columbia.edu/tag/07TH)
* [Stacks Project, Tag 0D7I](https://stacks.math.columbia.edu/tag/0D7I)
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

universe v u

namespace CategoryTheory.SimplicialPseudoFamily

variable (P : SimplicialPseudoFamily.{v, u})

/-- The inverse of the identification of two factorizations is the identification taken the
other way. -/
theorem glueOfEq_symm {l m n : SimplexCategory} (ψ ψ' : l ⟶ m) (φ φ' : m ⟶ n) (v : l ⟶ n)
    (h : ψ ≫ φ = v) (h' : ψ' ≫ φ' = v) (X : P.obj l) :
    (P.glueOfEq ψ ψ' φ φ' v h h' X).symm = P.glueOfEq ψ' ψ φ' φ v h' h X := by
  ext
  simp [glueOfEq]

/-- The identification of two factorizations is natural. -/
@[reassoc]
theorem glueOfEq_hom_naturality {l m n : SimplexCategory} (ψ ψ' : l ⟶ m) (φ φ' : m ⟶ n)
    (v : l ⟶ n) (h : ψ ≫ φ = v) (h' : ψ' ≫ φ' = v) {X Y : P.obj l} (f : X ⟶ Y) :
    (P.map φ).map ((P.map ψ).map f) ≫ (P.glueOfEq ψ ψ' φ φ' v h h' Y).hom =
      (P.glueOfEq ψ ψ' φ φ' v h h' X).hom ≫ (P.map φ').map ((P.map ψ').map f) := by
  simp only [glueOfEq, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [reassoc_of% (P.pasteOfEq_naturality ψ φ v h f)]
  congr 1
  rw [Iso.eq_inv_comp, ← reassoc_of% (P.pasteOfEq_naturality ψ' φ' v h' f), Iso.hom_inv_id,
    Category.comp_id]

variable {P} in
/-- **The cocycle condition is invariant under conjugation.** If `α` satisfies the cocycle
condition for `F` and `c : F' ≅ F`, then the conjugate of `α` by the pullbacks of `c` satisfies it
for `F'`. -/
theorem isCocycle_conj {F F' : P.obj ⦋0⦌} (c : F' ≅ F)
    {α : (P.map (SimplexCategory.δ (1 : Fin 2))).obj F ≅
      (P.map (SimplexCategory.δ (0 : Fin 2))).obj F}
    (h : P.IsCocycle F α) :
    P.IsCocycle F' ((P.map (SimplexCategory.δ (1 : Fin 2))).mapIso c ≪≫ α ≪≫
      (P.map (SimplexCategory.δ (0 : Fin 2))).mapIso c.symm) := by
  unfold IsCocycle glueLeft glueMiddle glueRight at h ⊢
  have nL := P.glueOfEq_hom_naturality _ _ _ _ _ SimplexCategory.delta_one_comp_delta_two
    SimplexCategory.delta_one_comp_delta_one c.hom
  have nM := P.glueOfEq_hom_naturality _ _ _ _ _ SimplexCategory.delta_zero_comp_delta_two
    SimplexCategory.delta_one_comp_delta_zero c.inv
  have nR := P.glueOfEq_hom_naturality _ _ _ _ _ SimplexCategory.delta_zero_comp_delta_zero
    SimplexCategory.delta_zero_comp_delta_one c.inv
  have nL' : (P.map (SimplexCategory.δ (1 : Fin 3))).map
        ((P.map (SimplexCategory.δ (1 : Fin 2))).map c.hom) ≫
      (P.glueOfEq _ _ _ _ _ SimplexCategory.delta_one_comp_delta_two
        SimplexCategory.delta_one_comp_delta_one F).inv =
      (P.glueOfEq _ _ _ _ _ SimplexCategory.delta_one_comp_delta_two
        SimplexCategory.delta_one_comp_delta_one F').inv ≫
        (P.map (SimplexCategory.δ (2 : Fin 3))).map
          ((P.map (SimplexCategory.δ (1 : Fin 2))).map c.hom) := by
    rw [Iso.comp_inv_eq, Category.assoc, nL, Iso.inv_hom_id_assoc]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Functor.map_comp, Category.assoc,
    h]
  rw [reassoc_of% nL', reassoc_of% nM, nR]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]

/-- A pair of a pseudofunctorial family: an object `F` in degree zero with an isomorphism
`α : f_{δ¹₁}^* F ≅ f_{δ¹₀}^* F` satisfying the cocycle condition in degree two. -/
structure Pair where
  /-- The object in degree zero. -/
  obj : P.obj ⦋0⦌
  /-- The comparison isomorphism between the two pullbacks to degree one. -/
  iso : (P.map (SimplexCategory.δ (1 : Fin 2))).obj obj ≅
    (P.map (SimplexCategory.δ (0 : Fin 2))).obj obj
  /-- The cocycle condition in degree two. -/
  cocycle : P.IsCocycle obj iso

namespace Pair

variable {P}

/-- A morphism of pairs is a morphism of the objects in degree zero commuting with the
comparison isomorphisms. -/
structure Hom (A B : P.Pair) where
  /-- The morphism of the objects in degree zero. -/
  map : A.obj ⟶ B.obj
  /-- Compatibility with the comparison isomorphisms. -/
  comm : (P.map (SimplexCategory.δ (1 : Fin 2))).map map ≫ B.iso.hom =
    A.iso.hom ≫ (P.map (SimplexCategory.δ (0 : Fin 2))).map map

/-- Pairs form a category, composition being that of the morphisms in degree zero. -/
instance : Category P.Pair where
  Hom A B := Hom A B
  id A := { map := 𝟙 A.obj, comm := by simp }
  comp f g :=
    { map := f.map ≫ g.map
      comm := by simp only [Functor.map_comp, Category.assoc, g.comm, reassoc_of% f.comm] }

/-- The identity morphism of pairs is the identity in degree zero. -/
@[simp] theorem id_map (A : P.Pair) : Hom.map (𝟙 A) = 𝟙 A.obj := rfl

/-- Composition of morphisms of pairs composes the morphisms in degree zero. -/
@[simp] theorem comp_map {A B C : P.Pair} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).map = f.map ≫ g.map := rfl

/-- A morphism of pairs is determined by its morphism in degree zero. -/
theorem hom_ext {A B : P.Pair} {f g : A ⟶ B} (h : f.map = g.map) : f = g := by
  obtain ⟨f, hf⟩ := f
  obtain ⟨g, hg⟩ := g
  subst h
  rfl

/-- An isomorphism of the objects in degree zero compatible with the comparison isomorphisms is
an isomorphism of pairs. -/
def isoMk {A B : P.Pair} (e : A.obj ≅ B.obj)
    (h : (P.map (SimplexCategory.δ (1 : Fin 2))).map e.hom ≫ B.iso.hom =
      A.iso.hom ≫ (P.map (SimplexCategory.δ (0 : Fin 2))).map e.hom) :
    A ≅ B where
  hom := ⟨e.hom, h⟩
  inv :=
    ⟨e.inv, by
      rw [← cancel_epi ((P.map (SimplexCategory.δ (1 : Fin 2))).map e.hom), reassoc_of% h]
      simp only [← Functor.map_comp_assoc, ← Functor.map_comp, e.hom_inv_id,
        CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]⟩
  hom_inv_id := hom_ext (by simp)
  inv_hom_id := hom_ext (by simp)

/-- The isomorphism of the objects in degree zero underlying an isomorphism of pairs. -/
def objIso {A B : P.Pair} (e : A ≅ B) : A.obj ≅ B.obj where
  hom := e.hom.map
  inv := e.inv.map
  hom_inv_id := congrArg Hom.map e.hom_inv_id
  inv_hom_id := congrArg Hom.map e.inv_hom_id

end Pair

/-! ### The pair of a cartesian system -/

namespace CartesianSystem

variable {P} (N : P.CartesianSystem)

/-- The compositor at a factorization carries the composite of two transitions of a cartesian
system to the transition of the factored map. -/
theorem pasteOfEq_comp_trans {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) (θ : l ⟶ n)
    (h : ψ ≫ φ = θ) :
    (P.pasteOfEq ψ φ θ h (N.obj l)).hom ≫ (N.trans θ).hom =
      (P.map φ).map (N.trans ψ).hom ≫ (N.trans φ).hom := by
  subst h
  rw [P.pasteOfEq_rfl]
  exact N.trans_comp ψ φ

/-- The two composites of transitions attached to two factorizations of one simplex map agree
under the identification of the two factorizations. -/
theorem glueOfEq_comp_trans {l m n : SimplexCategory} (ψ ψ' : l ⟶ m) (φ φ' : m ⟶ n)
    (v : l ⟶ n) (h : ψ ≫ φ = v) (h' : ψ' ≫ φ' = v) :
    (P.glueOfEq ψ ψ' φ φ' v h h' (N.obj l)).hom ≫
        ((P.map φ').map (N.trans ψ').hom ≫ (N.trans φ').hom) =
      (P.map φ).map (N.trans ψ).hom ≫ (N.trans φ).hom := by
  rw [← N.pasteOfEq_comp_trans ψ' φ' v h', ← N.pasteOfEq_comp_trans ψ φ v h]
  simp [glueOfEq]

/-- **The comparison isomorphism of a cartesian system**, `f_{δ¹₁}^* N_0 ≅ N_1 ≅ f_{δ¹₀}^* N_0`. -/
def pairIso :
    (P.map (SimplexCategory.δ (1 : Fin 2))).obj (N.obj ⦋0⦌) ≅
      (P.map (SimplexCategory.δ (0 : Fin 2))).obj (N.obj ⦋0⦌) :=
  N.trans (SimplexCategory.δ (1 : Fin 2)) ≪≫ (N.trans (SimplexCategory.δ (0 : Fin 2))).symm

/-- The comparison isomorphism of a cartesian system, written out. -/
theorem pairIso_hom :
    N.pairIso.hom = (N.trans (SimplexCategory.δ (1 : Fin 2))).hom ≫
      (N.trans (SimplexCategory.δ (0 : Fin 2))).inv := rfl

/-- The pullback of the comparison isomorphism, followed by the composite of transitions along
`δ¹₀`, is the composite of transitions along `δ¹₁`. -/
theorem map_pairIso_comp_trans {n : SimplexCategory} (φ : ⦋1⦌ ⟶ n) :
    (P.map φ).map N.pairIso.hom ≫
        ((P.map φ).map (N.trans (SimplexCategory.δ (0 : Fin 2))).hom ≫ (N.trans φ).hom) =
      (P.map φ).map (N.trans (SimplexCategory.δ (1 : Fin 2))).hom ≫ (N.trans φ).hom := by
  rw [← Category.assoc, ← Functor.map_comp]
  simp [pairIso]

/-- **The comparison isomorphism of a cartesian system satisfies the cocycle condition.** -/
theorem isCocycle_pairIso : P.IsCocycle (N.obj ⦋0⦌) N.pairIso := by
  unfold IsCocycle
  have hL := N.glueOfEq_comp_trans (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.δ (1 : Fin 2))
    (SimplexCategory.δ (2 : Fin 3)) (SimplexCategory.δ (1 : Fin 3)) _
    SimplexCategory.delta_one_comp_delta_two SimplexCategory.delta_one_comp_delta_one
  have hM := N.glueOfEq_comp_trans (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.δ (1 : Fin 2))
    (SimplexCategory.δ (2 : Fin 3)) (SimplexCategory.δ (0 : Fin 3)) _
    SimplexCategory.delta_zero_comp_delta_two SimplexCategory.delta_one_comp_delta_zero
  have hR := N.glueOfEq_comp_trans (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.δ (0 : Fin 2))
    (SimplexCategory.δ (0 : Fin 3)) (SimplexCategory.δ (1 : Fin 3)) _
    SimplexCategory.delta_zero_comp_delta_zero SimplexCategory.delta_zero_comp_delta_one
  have h0 := N.map_pairIso_comp_trans (SimplexCategory.δ (0 : Fin 3))
  have h1 := N.map_pairIso_comp_trans (SimplexCategory.δ (1 : Fin 3))
  have h2 := N.map_pairIso_comp_trans (SimplexCategory.δ (2 : Fin 3))
  rw [← cancel_mono ((P.map (SimplexCategory.δ (1 : Fin 3))).map
      (N.trans (SimplexCategory.δ (0 : Fin 2))).hom ≫
        (N.trans (SimplexCategory.δ (1 : Fin 3))).hom), h1]
  simp only [Category.assoc]
  change _ = (P.glueLeft (N.obj ⦋0⦌)).inv ≫ _ ≫ (P.glueMiddle (N.obj ⦋0⦌)).hom ≫ _ ≫
    (P.glueRight (N.obj ⦋0⦌)).hom ≫ _
  unfold glueLeft glueMiddle glueRight
  rw [hR, h0, hM, h2, ← hL, Iso.inv_hom_id_assoc]

/-- **The pair of a cartesian system**: its object in degree zero with its comparison
isomorphism. -/
def toPair : P.Pair where
  obj := N.obj ⦋0⦌
  iso := N.pairIso
  cocycle := N.isCocycle_pairIso

end CartesianSystem

/-- The compatibility of a morphism of the objects in degree zero of a cartesian system and of a
pair with their comparison isomorphisms. -/
def ToPairComm (A : P.Pair) (N : P.CartesianSystem) (f : N.obj ⦋0⦌ ⟶ A.obj) : Prop :=
  (P.map (SimplexCategory.δ (1 : Fin 2))).map f ≫ A.iso.hom =
    N.pairIso.hom ≫ (P.map (SimplexCategory.δ (0 : Fin 2))).map f

/-- The identification of a cartesian system with the system of a pair is compatible with the
comparison isomorphisms. -/
theorem toPairComm_of_iso_pairSystem (A : P.Pair) (N : P.CartesianSystem)
    (e : ∀ n, N.obj n ≅ (P.pairSystem A.obj A.iso A.cocycle).obj n)
    (he : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      (N.trans φ).hom ≫ (e n).hom =
        (P.map φ).map (e m).hom ≫ ((P.pairSystem A.obj A.iso A.cocycle).trans φ).hom) :
    P.ToPairComm A N (e ⦋0⦌ ≪≫ P.pairZeroIso A.obj).hom :=
  P.comm_of_iso_pairSystem_of_eq A.obj A.iso A.cocycle N e he
    (e ⦋0⦌ ≪≫ P.pairZeroIso A.obj) rfl N.pairIso rfl

/-- An isomorphism of the objects in degree zero of a cartesian system and of a pair, compatible
with the comparison isomorphisms, is an isomorphism of pairs. -/
def toPairIsoMk (A : P.Pair) (N : P.CartesianSystem) (E : N.obj ⦋0⦌ ≅ A.obj)
    (h : P.ToPairComm A N E.hom) : N.toPair ≅ A :=
  Pair.isoMk E h

/-- A cartesian system identified, compatibly with the transitions, with the system of a pair
has that pair as its pair. -/
def toPairIsoOfIsoPairSystem (A : P.Pair) (N : P.CartesianSystem)
    (e : ∀ n, N.obj n ≅ (P.pairSystem A.obj A.iso A.cocycle).obj n)
    (he : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      (N.trans φ).hom ≫ (e n).hom =
        (P.map φ).map (e m).hom ≫ ((P.pairSystem A.obj A.iso A.cocycle).trans φ).hom) :
    N.toPair ≅ A :=
  Pair.isoMk (e ⦋0⦌ ≪≫ P.pairZeroIso A.obj)
    (P.comm_of_iso_pairSystem_of_eq A.obj A.iso A.cocycle N e he
      (e ⦋0⦌ ≪≫ P.pairZeroIso A.obj) rfl N.pairIso rfl)

variable {P} in
/-- A family of morphisms between the objects of two cartesian systems compatible with the
transitions gives, in degree zero, a morphism of their pairs. -/
def CartesianSystem.toPairHom {N N' : P.CartesianSystem} (f : ∀ n, N.obj n ⟶ N'.obj n)
    (hf : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      (P.map φ).map (f m) ≫ (N'.trans φ).hom = (N.trans φ).hom ≫ f n) :
    N.toPair ⟶ N'.toPair where
  map := f ⦋0⦌
  comm := by
    simp only [CartesianSystem.toPair, pairIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [reassoc_of% (hf (SimplexCategory.δ (1 : Fin 2)))]
    congr 1
    rw [Iso.comp_inv_eq, Category.assoc, hf, Iso.inv_hom_id_assoc]

/-! ### The cocycle condition in reindexed form -/

section Reindex

variable {P}

/-- The pullback of a morphism `β : f_ψ^* M ⟶ f_ψ'^* M` along `φ`, read through the compositor as
a morphism `f_{ψ ≫ φ}^* M ⟶ f_{ψ' ≫ φ}^* M`. -/
def reindexP {l m n : SimplexCategory} (ψ ψ' : l ⟶ m) (φ : m ⟶ n) {M : P.obj l}
    (β : (P.map ψ).obj M ⟶ (P.map ψ').obj M) :
    (P.map (ψ ≫ φ)).obj M ⟶ (P.map (ψ' ≫ φ)).obj M :=
  (P.paste ψ φ M).inv ≫ (P.map φ).map β ≫ (P.paste ψ' φ M).hom

variable (P) in
/-- **The cocycle condition in reindexed form, at given faces**: for `a₀ a₁ : o₀ ⟶ o₁` and
`b₀ b₁ b₂ : o₁ ⟶ o₂` satisfying the simplicial identities of the faces, the reindexing of `α`
along `b₁` is the composite of its reindexings along `b₂` and `b₀`. -/
def IsReindexCocycleAt {o₀ o₁ o₂ : SimplexCategory} (a₀ a₁ : o₀ ⟶ o₁) (b₀ b₁ b₂ : o₁ ⟶ o₂)
    (e₂₁ : a₁ ≫ b₁ = a₁ ≫ b₂) (e₂₀ : a₀ ≫ b₂ = a₁ ≫ b₀) (e₀₁ : a₀ ≫ b₀ = a₀ ≫ b₁)
    (F : P.obj o₀) (α : (P.map a₁).obj F ⟶ (P.map a₀).obj F) : Prop :=
  reindexP a₁ a₀ b₁ α =
    eqToHom (show (P.map (a₁ ≫ b₁)).obj F = (P.map (a₁ ≫ b₂)).obj F by rw [e₂₁]) ≫
      reindexP a₁ a₀ b₂ α ≫
      eqToHom (show (P.map (a₀ ≫ b₂)).obj F = (P.map (a₁ ≫ b₀)).obj F by rw [e₂₀]) ≫
      reindexP a₁ a₀ b₀ α ≫
      eqToHom (show (P.map (a₀ ≫ b₀)).obj F = (P.map (a₀ ≫ b₁)).obj F by rw [e₀₁])

variable (P) in
/-- **The cocycle condition in reindexed form**: the reindexing of `α` along `δ²₁` is the
composite of its reindexings along `δ²₂` and `δ²₀`, the three being compared through the
simplicial identities. -/
def IsReindexCocycle (F : P.obj ⦋0⦌)
    (α : (P.map (SimplexCategory.δ (1 : Fin 2))).obj F ≅
      (P.map (SimplexCategory.δ (0 : Fin 2))).obj F) : Prop :=
  P.IsReindexCocycleAt (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.δ (1 : Fin 2))
    (@SimplexCategory.δ (0 + 1) (0 : Fin 3)) (@SimplexCategory.δ (0 + 1) (1 : Fin 3))
    (@SimplexCategory.δ (0 + 1) (2 : Fin 3))
    (SimplexCategory.delta_one_comp_delta_one.trans SimplexCategory.delta_one_comp_delta_two.symm)
    (SimplexCategory.delta_zero_comp_delta_two.trans
      SimplexCategory.delta_one_comp_delta_zero.symm)
    (SimplexCategory.delta_zero_comp_delta_zero.trans
      SimplexCategory.delta_zero_comp_delta_one.symm) F α.hom

/-- The pullback of a morphism along `φ`, through the compositors. -/
theorem map_eq_reindexP {l m n : SimplexCategory} (ψ ψ' : l ⟶ m) (φ : m ⟶ n) {M : P.obj l}
    (β : (P.map ψ).obj M ⟶ (P.map ψ').obj M) :
    (P.map φ).map β = (P.paste ψ φ M).hom ≫ reindexP ψ ψ' φ β ≫ (P.paste ψ' φ M).inv := by
  simp [reindexP]

/-- An identification of two factorizations, through the compositors. -/
theorem glueOfEq_hom_eq {l m n : SimplexCategory} (ψ ψ' : l ⟶ m) (φ φ' : m ⟶ n) (v : l ⟶ n)
    (h : ψ ≫ φ = v) (h' : ψ' ≫ φ' = v) (X : P.obj l) :
    (P.glueOfEq ψ ψ' φ φ' v h h' X).hom = (P.paste ψ φ X).hom ≫
      eqToHom (congrArg (fun k => (P.map k).obj X) (h.trans h'.symm)) ≫
        (P.paste ψ' φ' X).inv := by
  subst h
  simp [glueOfEq, pasteOfEq]

variable (P) in
/-- **The cocycle condition is the reindexed cocycle condition.** -/
theorem isCocycle_iff_isReindexCocycle (F : P.obj ⦋0⦌)
    (α : (P.map (SimplexCategory.δ (1 : Fin 2))).obj F ≅
      (P.map (SimplexCategory.δ (0 : Fin 2))).obj F) :
    P.IsCocycle F α ↔ P.IsReindexCocycle F α := by
  unfold IsCocycle IsReindexCocycle IsReindexCocycleAt glueLeft glueMiddle glueRight
  rw [← Iso.symm_hom, glueOfEq_symm, glueOfEq_hom_eq, glueOfEq_hom_eq, glueOfEq_hom_eq,
    map_eq_reindexP _ (SimplexCategory.δ (0 : Fin 2)),
    map_eq_reindexP _ (SimplexCategory.δ (0 : Fin 2)),
    map_eq_reindexP _ (SimplexCategory.δ (0 : Fin 2))]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [cancel_epi]
  simp only [← Category.assoc]
  rw [cancel_mono]

end Reindex

end CategoryTheory.SimplicialPseudoFamily

end
