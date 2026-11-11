module

public import Mathlib.Algebra.Category.AlgCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.CategoryTheory.Monad.Adjunction
public import StacksFrontier.AlgebraicTopology.SimplicialSet.TrivialKanFibration.SimplicialAbelianGroup
public import StacksFrontier.AlgebraicTopology.StandardResolution.Whiskering

@[expose] public section

/-!
# Standard resolutions

Let `V : 𝒜 ⥤ 𝒮` be a functor with a left adjoint `U : 𝒮 ⥤ 𝒜`. Writing `d : U ∘ V ⟶ id_𝒜` for the
counit and `η : id_𝒮 ⟶ V ∘ U` for the unit, the endofunctor `Y = U ∘ V` of `𝒜` carries the two
transformations `d` and `s = 1_U ⋆ η ⋆ 1_V : Y ⟶ Y ∘ Y`, that is, `Y` is a comonad on `𝒜`.
Godement's standard resolution is the system of iterates `X_n = Y^{∘ (n + 1)}` (`n ≥ 0`),
`X_{-1} = id_𝒜`, with `d^n_j = 1_{X_{j-1}} ⋆ d ⋆ 1_{X_{n-j-1}} : X_n ⟶ X_{n-1}` and
`s^n_j = 1_{X_{j-1}} ⋆ s ⋆ 1_{X_{n-j-1}} : X_n ⟶ X_{n+1}` for `0 ≤ j ≤ n`; it is a simplicial
object of the category `Fun(𝒜, 𝒜)` of endofunctors of `𝒜`, and `ε₀ = d : X_0 ⟶ X_{-1}` makes it
an augmented simplicial object over the constant simplicial object `id_𝒜`.

Whiskering the augmentation `ε` with `V` on the outside, resp. with `U` on the inside, gives
morphisms of simplicial objects `1_V ⋆ ε : V ∘ X ⟶ V` of `Fun(𝒜, 𝒮)` and `ε ⋆ 1_U : X ∘ U ⟶ U` of
`Fun(𝒮, 𝒜)`, and both are homotopy equivalences: each admits a morphism in the other direction
whose two composites with it are homotopic to the identities. In degree `n` the two homotopy
inverses are `η ⋆ 1_V`, resp. `1_U ⋆ η`, iterated `n + 1` times.

For the free/forget adjunction between (not necessarily commutative) `A`-algebras and sets, whose
free functor is `FreeAlgebra`, the tower is `X_n(B) = A[A[⋯[B]⋯]]`
with `n + 1` brackets, its faces and degeneracies are substitutions of variables, and the two
homotopy inverses are the iterated inclusions of the variables, `b ↦ [⋯[b]⋯]` and
`∑ a [e₁]⋯[e_p] ↦ ∑ a [⋯[e₁]⋯]⋯[⋯[e_p]⋯]`. For the free/forget adjunction between `R`-modules and
sets the tower is `X_n(M) = R[R[⋯[M]⋯]]`, and its four maps out of `X_1(M) = R[R[M]]` contract or
double the outer, resp. the inner, bracket. In both cases the augmentation is degreewise
surjective, and for such a morphism of simplicial modules — or of simplicial algebras, through the
underlying simplicial modules — being a homotopy equivalence of underlying simplicial sets is
*equivalent* to inducing a quasi-isomorphism of the associated chain complexes; so `M`, resp. `B`,
in degree `0` and through the augmentation, is the only nonzero homology group of the complex of
the resolution.

## Main results

* `CategoryTheory.Comonad.exists_augmented_standardResolution`: the iterates of a comonad `G` on
  `A`, with the faces and degeneracies obtained by whiskering `G.ε` and `G.δ` into the `j`-th
  factor, are the faces and degeneracies of an augmented simplicial object of `A ⥤ A` whose
  augmentation is `G.ε`.
* `CategoryTheory.Adjunction.exists_homotopyInverse_whiskered_standardResolution`: the
  whiskerings `1_V ⋆ ε` and `ε ⋆ 1_U` of the augmentation of the standard resolution are homotopy
  equivalences of simplicial objects of `A ⥤ S`, resp. of `S ⥤ A`.
* `AlgCat.face_eq_lift_and_degeneracy_eq_lift`: the faces and degeneracies of the standard
  resolution of an `A`-algebra by noncommutative free `A`-algebras (the noncommutative analogue of
  Stacks 09CB, whose commutative form is `CommAlgCat.face_eq_aeval_and_degeneracy_eq_rename`), as
  maps out of a free algebra, are four `FreeAlgebra.lift`s: `d^n_0` substitutes for each variable
  `[z]` the element `z`, `s^n_0` replaces `[z]` by `[[z]]`, and `d^{n+1}_{j+1}`, `s^{n+1}_{j+1}`
  send `[z]` to `[d^n_j(z)]`, resp. `[s^n_j(z)]`.
* `AlgCat.exists_homotopyInverse_whiskered_standardResolution`: the same homotopy equivalences for
  the free/forget adjunction of not necessarily commutative `A`-algebras, with their homotopy
  inverses displayed as the iterated inclusions of the variables. The commutative case of Stacks
  08NE, with polynomial algebras, is
  `CommAlgCat.exists_homotopyInverse_whiskered_standardResolution` in
  `StacksFrontier.Cotangent.StandardResolution`, through
  `CategoryTheory.Godement.exists_homotopyInverse_whiskerRight_eq` and
  `CategoryTheory.Godement.exists_homotopyInverse_whiskerLeft_eq`: the homotopy inverses of the
  whiskered augmentations extending a prescribed family compatible with `d⁰₀` and `sⁿ₀`.
* `AlgebraicTopology.homotopyEquivalences_forget_iff_quasiIso_of_surjective`: for a degreewise
  surjective morphism `f` of simplicial `R`-modules, the underlying morphism of simplicial sets is
  a homotopy equivalence if and only if `s(f)` is a quasi-isomorphism.
* `AlgebraicTopology.homotopyEquivalences_forget_iff_quasiIso_forget₂_of_surjective`: the same for
  a degreewise surjective morphism of simplicial `A`-algebras, through the underlying simplicial
  `A`-modules.
* `ModuleCat.free_standardResolution_face_degeneracy_apply`: the two faces and two degeneracies
  out of `X_1(M) = R[R[M]]`, on a typical element `ξ = ∑ᵢ rᵢ[∑ⱼ r_ij[m_ij]]`.

## References

* [Stacks, Tag 08NA](https://stacks.math.columbia.edu/tag/08NA)
* [Stacks, Tag 08NC](https://stacks.math.columbia.edu/tag/08NC)
* [Stacks, Tag 08ND](https://stacks.math.columbia.edu/tag/08ND)
* [Stacks, Tag 08NE](https://stacks.math.columbia.edu/tag/08NE)
* [Stacks, Tag 09CB](https://stacks.math.columbia.edu/tag/09CB)
* [Stacks, Tag 0G5T](https://stacks.math.columbia.edu/tag/0G5T)
* [Stacks, Tag 0G5U](https://stacks.math.columbia.edu/tag/0G5U)
* [Stacks, Tag 08N9](https://stacks.math.columbia.edu/tag/08N9)
* [Stacks, Tag 08NB](https://stacks.math.columbia.edu/tag/08NB)
* [Stacks, Tag 08NS](https://stacks.math.columbia.edu/tag/08NS)
* [Stacks, Tag 08P1](https://stacks.math.columbia.edu/tag/08P1)
* [Stacks, Tag 08P2](https://stacks.math.columbia.edu/tag/08P2)
* [Stacks, Tag 019N](https://stacks.math.columbia.edu/tag/019N)
* [Godement, *Topologie algébrique et théorie des faisceaux*, Appendice 1]
-/

open CategoryTheory Opposite Simplicial

universe v₁ v₂ v₃ u₁ u₂ u₃ v' v'' u' u'' v u

/-! ### Padding, transport and horizontal identities -/

section Shared

/-- A morphism is unchanged by identity morphisms on both ends. -/
private lemma eq_id_comp_comp_id {D : Type u} [Category.{v} D] {P R : D} (f : P ⟶ R) :
    f = 𝟙 P ≫ f ≫ 𝟙 R := by simp

/-- A morphism `f : F ⟶ K ⋙ H` of functors is unchanged by composing it with identities on both
ends and with `Functor.whiskerRight (𝟙 K) H`, which is the identity of `K ⋙ H`. -/
private lemma eq_id_comp_comp_whiskerRight_id {C : Type u} [Category.{v} C] {D : Type u'}
    [Category.{v'} D] {E : Type u''} [Category.{v''} E] {K : C ⥤ D} {F : C ⥤ E} (H : D ⥤ E)
    (f : F ⟶ K ⋙ H) :
    f = 𝟙 F ≫ f ≫ Functor.whiskerRight (𝟙 K) H ≫ 𝟙 (K ⋙ H) := by
  rw [Functor.whiskerRight_id']
  simp

/-- The conjugate of an identity morphism of the model is the identity. -/
private theorem eqToHom_id_eqToHom {D : Type u} [Category.{v} D] {P P' : D} (h : P = P')
    (f : P' ⟶ P') (hf : f = 𝟙 P') : eqToHom h ≫ f ≫ eqToHom h.symm = 𝟙 P := by
  subst h
  rw [hf]
  simp

/-- Morphisms of simplicial objects agreeing in every degree `⦋n⦌` are equal. -/
private theorem hom_ext_of_app {D : Type u} [Category.{v} D] {Q R : SimplicialObject D}
    {f g : Q ⟶ R} (h : ∀ n : ℕ, f.app (op ⦋n⦌) = g.app (op ⦋n⦌)) : f = g :=
  SimplicialObject.hom_ext _ _ fun n => by simpa using h n.unop.len

/-- Horizontally composing with the identity of the identity functor, on the outside. -/
private theorem hcomp_id_left {D : Type u₁} [Category.{v₁} D] {E : Type u₂} [Category.{v₂} E]
    {H I : D ⥤ E} (β : H ⟶ I) : NatTrans.hcomp (𝟙 (𝟭 D)) β = β := by
  ext X; simp

/-- Horizontally composing with the identity of the identity functor, on the inside. -/
private theorem hcomp_id_right {D : Type u₁} [Category.{v₁} D] {E : Type u₂} [Category.{v₂} E]
    {F G : D ⥤ E} (α : F ⟶ G) : NatTrans.hcomp α (𝟙 (𝟭 E)) = α := by
  ext X; simp

/-- The horizontal composite of two identities is the identity. -/
private theorem hcomp_id_id {D : Type u₁} [Category.{v₁} D] {E : Type u₂} [Category.{v₂} E]
    {K : Type u₃} [Category.{v₃} K] (G : D ⥤ E) (F : E ⥤ K) :
    NatTrans.hcomp (𝟙 G) (𝟙 F) = 𝟙 (G ⋙ F) := by
  ext X; simp

end Shared

/-! ### The defining clauses of the faces and degeneracies -/

/-! ### The standard resolution of a comonad -/

section ComonadLaws

variable {A : Type u} [Category.{v} A] (G : Comonad A)

/-- The left counit law of a comonad, at the level of transformations of functors:
`(G.ε ⋆ 1_G) ∘ G.δ = 1_G`, the outer factor listed first. On components this is
`CategoryTheory.Comonad.left_counit`. -/
private lemma δ_comp_whiskerLeft_ε :
    G.δ ≫ Functor.whiskerLeft (G : A ⥤ A) G.ε = 𝟙 (G : A ⥤ A) := by
  ext X; simp

/-- The right counit law of a comonad, at the level of transformations of functors:
`(1_G ⋆ G.ε) ∘ G.δ = 1_G`. On components this is `CategoryTheory.Comonad.right_counit`. -/
private lemma δ_comp_whiskerRight_ε :
    G.δ ≫ Functor.whiskerRight G.ε (G : A ⥤ A) = 𝟙 (G : A ⥤ A) := by
  ext X; simp

/-- Coassociativity of a comonad, at the level of transformations of functors:
`(G.δ ⋆ 1_G) ∘ G.δ = (1_G ⋆ G.δ) ∘ G.δ`. On components this is
`CategoryTheory.Comonad.coassoc`. -/
private lemma δ_comp_whiskerLeft_δ :
    G.δ ≫ Functor.whiskerLeft (G : A ⥤ A) G.δ = G.δ ≫ Functor.whiskerRight G.δ (G : A ⥤ A) := by
  ext X; simp

end ComonadLaws

namespace CategoryTheory.Comonad

/-- **Stacks 08NC**.
Let `G` be a comonad on a category `A`, with counit `G.ε : G ⟶ 𝟭 A` and comultiplication
`G.δ : G ⟶ G ⋙ G`. The iterates `Z (n + 1)` of `G`, with `Z 0 = 𝟭 A`, carry faces
`d n j : Z (n + 1) ⟶ Z n` and degeneracies `s n j : Z (n + 1) ⟶ Z (n + 2)` for `0 ≤ j ≤ n`,
obtained by whiskering `G.ε`, resp. `G.δ`, into the `j`-th factor `G` counted from the left in the
composite `Z (n + 1) = G ∘ ⋯ ∘ G`, and these are the faces and degeneracies of a simplicial object
of the category `A ⥤ A` of endofunctors of `A`, augmented over the constant simplicial object `𝟭 A`
by `ε₀ = d 0 0 = G.ε`. -/
@[stacks 08NC]
public theorem exists_augmented_standardResolution {A : Type u} [Category.{v} A]
    (G : Comonad A) :
    ∃ (Z : ℕ → (A ⥤ A)) (hZ : ∀ n : ℕ, Z (n + 1) = Z n ⋙ (G : A ⥤ A))
      (d : ∀ n : ℕ, Fin (n + 1) → (Z (n + 1) ⟶ Z n))
      (s : ∀ n : ℕ, Fin (n + 1) → (Z (n + 1) ⟶ Z (n + 2))),
      Z 0 = 𝟭 A ∧
      (∀ n : ℕ, d n 0 = eqToHom (hZ n) ≫ Functor.whiskerLeft (Z n) G.ε) ∧
      (∀ (n : ℕ) (j : Fin (n + 1)),
        d (n + 1) j.succ =
          eqToHom (hZ (n + 1)) ≫ Functor.whiskerRight (d n j) (G : A ⥤ A) ≫
            eqToHom (hZ n).symm) ∧
      (∀ n : ℕ,
        s n 0 = eqToHom (hZ n) ≫ Functor.whiskerLeft (Z n) G.δ ≫
          Functor.whiskerRight (eqToHom (hZ n).symm) (G : A ⥤ A) ≫ eqToHom (hZ (n + 1)).symm) ∧
      (∀ (n : ℕ) (j : Fin (n + 1)),
        s (n + 1) j.succ =
          eqToHom (hZ (n + 1)) ≫ Functor.whiskerRight (s n j) (G : A ⥤ A) ≫
            eqToHom (hZ (n + 2)).symm) ∧
      ∃ (X : SimplicialObject.Augmented (A ⥤ A))
        (h : ∀ n : ℕ, X.left.obj (op ⦋n⦌) = Z (n + 1)) (hX : X.right = Z 0),
        (∀ (n : ℕ) (j : Fin (n + 2)),
          X.left.δ j = eqToHom (h (n + 1)) ≫ d (n + 1) j ≫ eqToHom (h n).symm) ∧
        (∀ (n : ℕ) (j : Fin (n + 1)),
          X.left.σ j = eqToHom (h n) ≫ s n j ≫ eqToHom (h (n + 1)).symm) ∧
        X.hom.app (op ⦋0⦌) = eqToHom (h 0) ≫ d 0 0 ≫ eqToHom hX.symm := by
  obtain ⟨X, h, hX, hδ, hσ, hhom⟩ :=
    Godement.exists_augmented_standardResolution G.ε G.δ
      (δ_comp_whiskerLeft_ε G) (δ_comp_whiskerRight_ε G) (δ_comp_whiskerLeft_δ G)
  exact ⟨fun n => (G : A ⥤ A).iterate n, fun _ => rfl, Godement.face G.ε,
    Godement.degeneracy G.δ, rfl,
    fun n => (Godement.Prep.face_zero G.ε n).trans (Category.id_comp _).symm,
    fun n j => (Godement.Prep.face_succ G.ε n j).trans (eq_id_comp_comp_id _),
    fun n => (Godement.Prep.degeneracy_zero G.δ n).trans
      (eq_id_comp_comp_whiskerRight_id (K := (G : A ⥤ A).iterate (n + 1)) (G : A ⥤ A) _),
    fun n j => (Godement.Prep.degeneracy_succ G.δ n j).trans (eq_id_comp_comp_id _),
    X, h, hX, hδ, hσ, hhom⟩

end CategoryTheory.Comonad

/-! ### The whiskered augmentations are homotopy equivalences -/

section Whiskered

/-! #### Reading a morphism of a pinned simplicial object on the model -/

section Pinned

variable {D : Type u} [Category.{v} D]

/-- Let the terms of `Q` be identified with a family `P` by `e`, and let a transition map of `Q` be
pinned to a morphism `x` of the model. Then the components of a morphism `φ : Q ⟶ Q`, read on the
model through `e`, commute with `x`. -/
private theorem conj_comm {Q : SimplicialObject D} {P : ℕ → D}
    (e : ∀ n : ℕ, Q.obj (op ⦋n⦌) = P n) (φ : Q ⟶ Q) {n m : ℕ}
    (g : (op ⦋n⦌ : SimplexCategoryᵒᵖ) ⟶ op ⦋m⦌) {x : P n ⟶ P m}
    (hx : Q.map g = eqToHom (e n) ≫ x ≫ eqToHom (e m).symm) :
    (eqToHom (e n).symm ≫ φ.app (op ⦋n⦌) ≫ eqToHom (e n)) ≫ x =
      x ≫ (eqToHom (e m).symm ≫ φ.app (op ⦋m⦌) ≫ eqToHom (e m)) := by
  have hx' : x = eqToHom (e n).symm ≫ Q.map g ≫ eqToHom (e m) := by
    rw [hx]
    simp
  subst hx'
  simp

/-- If the augmentation of `Q` is pinned to `ε₀` and `φ : Q.left ⟶ Q.left` lies over the identity
of `Q.right`, then the degree-`0` component of `φ`, read on the model, commutes with `ε₀` and the
identity. -/
private theorem conj_comm_aug {Q : SimplicialObject.Augmented D} {P₀ R : D}
    (e : Q.left.obj (op ⦋0⦌) = P₀) (er : Q.right = R) {ε₀ : P₀ ⟶ R}
    (ehom : Q.hom.app (op ⦋0⦌) = eqToHom e ≫ ε₀ ≫ eqToHom er.symm) (φ : Q.left ⟶ Q.left)
    (hφ : φ.app (op ⦋0⦌) ≫ Q.hom.app (op ⦋0⦌) = Q.hom.app (op ⦋0⦌)) :
    (eqToHom e.symm ≫ φ.app (op ⦋0⦌) ≫ eqToHom e) ≫ ε₀ = ε₀ ≫ 𝟙 R := by
  subst e; subst er
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at ehom ⊢
  subst ehom
  exact hφ

/-- If `r` is a section of the augmentation of `Q`, then the endomorphism `Q.hom ≫ r` of `Q.left`
lies over the identity of `Q.right` in degree `0`. -/
private theorem comp_hom_app_zero_eq_hom_app_zero (Q : SimplicialObject.Augmented D)
    (r : (Functor.const SimplexCategoryᵒᵖ).obj Q.right ⟶ Q.left) (hr : r ≫ Q.hom = 𝟙 _) :
    (Q.hom ≫ r).app (op ⦋0⦌) ≫ Q.hom.app (op ⦋0⦌) = Q.hom.app (op ⦋0⦌) := by
  have hz : r.app (op ⦋0⦌) ≫ Q.hom.app (op ⦋0⦌) = 𝟙 _ := by
    simpa using congrArg (fun t => NatTrans.app t (op ⦋0⦌)) hr
  rw [NatTrans.comp_app, Category.assoc, hz, Category.comp_id]

/-- A splitting `h₀` of the augmentation of `Q` in degree `0` makes that augmentation a homotopy
equivalence, given that every endomorphism of `Q.left` lying over the identity of `Q.right` is
homotopic to the identity. -/
private theorem exists_homotopyInverse_of_endo_homotopic_id (Q : SimplicialObject.Augmented D)
    (h₀ : Q.right ⟶ Q.left.obj (op ⦋0⦌)) (hh₀ : h₀ ≫ Q.hom.app (op ⦋0⦌) = 𝟙 Q.right)
    (key : ∀ φ : Q.left ⟶ Q.left,
      φ.app (op ⦋0⦌) ≫ Q.hom.app (op ⦋0⦌) = Q.hom.app (op ⦋0⦌) →
      Relation.EqvGen (fun f g => Nonempty (SimplicialObject.Homotopy f g)) φ (𝟙 Q.left)) :
    ∃ r : (Functor.const SimplexCategoryᵒᵖ).obj Q.right ⟶ Q.left,
      Relation.EqvGen (fun f g => Nonempty (SimplicialObject.Homotopy f g)) (Q.hom ≫ r) (𝟙 _) ∧
      Relation.EqvGen (fun f g => Nonempty (SimplicialObject.Homotopy f g)) (r ≫ Q.hom)
        (𝟙 _) := by
  obtain ⟨r, -, hr⟩ :=
    SimplicialObject.Augmented.exists_section_of_comp_hom_app_zero_eq_id Q h₀ hh₀
  exact ⟨r, key _ (comp_hom_app_zero_eq_hom_app_zero Q r hr), by rw [hr]; exact .refl _⟩

/-- Conjugating a morphism of the model back and forth returns it. -/
private theorem eqToHom_conj_self {P P' : D} (h : P = P') (f : P ⟶ P) :
    eqToHom h ≫ (eqToHom h.symm ≫ f ≫ eqToHom h) ≫ eqToHom h.symm = f := by
  subst h; simp

end Pinned

/-! #### The recursions determine the faces and the degeneracies -/

section Recursion

variable {C : Type u} [Category.{v} C] {Y : C ⥤ C}

/-- Two families `x`, `g` of morphisms `X_n ⟶ P n` which agree in the outermost position `j = 0`
and satisfy the same recursion `x^{n+1}_{j+1} = 1_Y ⋆ x^n_j` in the remaining positions are
equal. -/
private theorem eq_of_rec (P : ℕ → C ⥤ C) (hP : ∀ n : ℕ, P n ⋙ Y = P (n + 1))
    (hZ : ∀ n : ℕ, Y.iterate (n + 1) = Y.iterate n ⋙ Y)
    (x g : ∀ n : ℕ, Fin (n + 1) → (Y.iterate (n + 1) ⟶ P n))
    (h₀ : ∀ n : ℕ, x n 0 = g n 0)
    (hx : ∀ (n : ℕ) (j : Fin (n + 1)), x (n + 1) j.succ =
      eqToHom (hZ (n + 1)) ≫ Functor.whiskerRight (x n j) Y ≫ eqToHom (hP n))
    (hg : ∀ (n : ℕ) (j : Fin (n + 1)), g (n + 1) j.succ =
      eqToHom (hZ (n + 1)) ≫ Functor.whiskerRight (g n j) Y ≫ eqToHom (hP n))
    (n : ℕ) : ∀ j : Fin (n + 1), x n j = g n j := by
  induction n with
  | zero =>
    intro j
    induction j using Fin.cases with
    | zero => exact h₀ 0
    | succ i => exact i.elim0
  | succ n ih =>
    intro j
    induction j using Fin.cases with
    | zero => exact h₀ (n + 1)
    | succ i => rw [hx n i, hg n i, ih i]

/-- A family of faces presented by the recursions `d^n_0 = d ⋆ 1_{X_{n-1}}` and
`d^{n+1}_{j+1} = 1_Y ⋆ d^n_j` is `Godement.face d`. -/
private theorem face_eq_face (dd : Y ⟶ 𝟭 C)
    (hZ : ∀ n : ℕ, Y.iterate (n + 1) = Y.iterate n ⋙ Y)
    (d : ∀ n : ℕ, Fin (n + 1) → (Y.iterate (n + 1) ⟶ Y.iterate n))
    (hd₀ : ∀ n : ℕ, d n 0 = eqToHom (hZ n) ≫ Functor.whiskerLeft (Y.iterate n) dd)
    (hd : ∀ (n : ℕ) (j : Fin (n + 1)), d (n + 1) j.succ =
      eqToHom (hZ (n + 1)) ≫ Functor.whiskerRight (d n j) Y ≫ eqToHom (hZ n).symm)
    (n : ℕ) : ∀ j : Fin (n + 1), d n j = Godement.face dd n j :=
  eq_of_rec Y.iterate (fun n => (hZ n).symm) hZ d (Godement.face dd)
    (fun n => by rw [hd₀ n, Godement.Prep.face_zero]; exact Category.id_comp _) hd
    (fun n j => by rw [Godement.Prep.face_succ dd n j]; exact eq_id_comp_comp_id _) n

/-- A family of degeneracies presented by the recursions `s^n_0 = s ⋆ 1_{X_{n-1}}` and
`s^{n+1}_{j+1} = 1_Y ⋆ s^n_j` is `Godement.degeneracy s`. -/
private theorem degeneracy_eq_degeneracy (ss : Y ⟶ Y ⋙ Y)
    (hZ : ∀ n : ℕ, Y.iterate (n + 1) = Y.iterate n ⋙ Y)
    (s : ∀ n : ℕ, Fin (n + 1) → (Y.iterate (n + 1) ⟶ Y.iterate (n + 2)))
    (hs₀ : ∀ n : ℕ, s n 0 = eqToHom (hZ n) ≫ Functor.whiskerLeft (Y.iterate n) ss ≫
      Functor.whiskerRight (eqToHom (hZ n).symm) Y ≫ eqToHom (hZ (n + 1)).symm)
    (hs : ∀ (n : ℕ) (j : Fin (n + 1)), s (n + 1) j.succ =
      eqToHom (hZ (n + 1)) ≫ Functor.whiskerRight (s n j) Y ≫ eqToHom (hZ (n + 2)).symm)
    (n : ℕ) : ∀ j : Fin (n + 1), s n j = Godement.degeneracy ss n j :=
  eq_of_rec (fun n => Y.iterate (n + 2)) (fun n => (hZ (n + 2)).symm) hZ s
    (Godement.degeneracy ss)
    (fun n => by
      rw [hs₀ n, Godement.Prep.degeneracy_zero]
      exact (eq_id_comp_comp_whiskerRight_id (K := Y.iterate (n + 1)) Y _).symm) hs
    (fun n j => by rw [Godement.Prep.degeneracy_succ ss n j]; exact eq_id_comp_comp_id _) n

end Recursion

/-! #### Transport through a whiskering -/

section Transport

/-- Whiskering on the right transports a morphism written as `eqToHom ≫ x' ≫ eqToHom` to one of
the same shape, the equalities pushed through `· ⋙ H`. -/
private theorem whiskerRight_transport {C : Type u} [Category.{v} C] {D : Type u₂}
    [Category.{v₂} D] {E : Type u₃} [Category.{v₃} E] {P P' R R' : C ⥤ D}
    (eP : P = P') (eR : R = R') {x : P ⟶ R} {x' : P' ⟶ R'}
    (hx : x = eqToHom eP ≫ x' ≫ eqToHom eR.symm) (H : D ⥤ E) :
    Functor.whiskerRight x H = eqToHom (congrArg (fun T => T ⋙ H) eP) ≫
      Functor.whiskerRight x' H ≫ eqToHom (congrArg (fun T => T ⋙ H) eR).symm := by
  subst eP; subst eR; subst hx; simp

/-- Whiskering on the left transports a morphism written as `eqToHom ≫ x' ≫ eqToHom` to one of
the same shape, the equalities pushed through `H ⋙ ·`. -/
private theorem whiskerLeft_transport {C : Type u} [Category.{v} C] {D : Type u₂}
    [Category.{v₂} D] {E : Type u₃} [Category.{v₃} E] {P P' R R' : D ⥤ E}
    (eP : P = P') (eR : R = R') {x : P ⟶ R} {x' : P' ⟶ R'}
    (hx : x = eqToHom eP ≫ x' ≫ eqToHom eR.symm) (H : C ⥤ D) :
    Functor.whiskerLeft H x = eqToHom (congrArg (fun T => H ⋙ T) eP) ≫
      Functor.whiskerLeft H x' ≫ eqToHom (congrArg (fun T => H ⋙ T) eR).symm := by
  subst eP; subst eR; subst hx; simp

/-- Two morphisms of the model composing to the identity have conjugates composing to the
identity. -/
private theorem conj_comp_conj_eq_id {D : Type u} [Category.{v} D] {P P' R R' : D}
    (eP : P = P') (eR : R = R') (u : P' ⟶ R') (w : R' ⟶ P') (huw : u ≫ w = 𝟙 P') :
    (eqToHom eP ≫ u ≫ eqToHom eR.symm) ≫ eqToHom eR ≫ w ≫ eqToHom eP.symm = 𝟙 P := by
  subst eP; subst eR
  simp [huw]

end Transport

/-! #### The triangle identities -/

section Triangles

variable {A : Type u₁} [Category.{v₁} A] {S : Type u₂} [Category.{v₂} S] {U : S ⥤ A} {V : A ⥤ S}

/-- The triangle identity `1_V = (1_V ⋆ d) ∘ (η ⋆ 1_V)`, at the level of transformations of
functors; Mathlib's `Adjunction.right_triangle` reads it in the bicategory of categories, with
the unitors and the associator spelled out. -/
private theorem whiskerLeft_unit_comp_whiskerRight_counit (adj : U ⊣ V) :
    Functor.whiskerLeft V adj.unit ≫ Functor.whiskerRight adj.counit V = 𝟙 V := by
  ext x; simp

/-- The triangle identity `1_U = (d ⋆ 1_U) ∘ (1_U ⋆ η)`, at the level of transformations of
functors; Mathlib's `Adjunction.left_triangle` reads it in the bicategory of categories, with the
unitors and the associator spelled out. -/
private theorem whiskerRight_unit_comp_whiskerLeft_counit (adj : U ⊣ V) :
    Functor.whiskerRight adj.unit U ≫ Functor.whiskerLeft U adj.counit = 𝟙 U := by
  ext x; simp

end Triangles

/-! #### Every endomorphism over the identity augmentation is homotopic to the identity -/

section Homotopic

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B] {Y : A ⥤ A}

/-- An endomorphism of the standard resolution whiskered on the outside by `G`, lying over the
identity of the augmentation, is homotopic to the identity. -/
private theorem homotopic_id_of_whiskerRight (dd : Y ⟶ 𝟭 A) (ss : Y ⟶ Y ⋙ Y) (G : A ⥤ B)
    (Q : SimplicialObject.Augmented (A ⥤ B))
    (e : ∀ n : ℕ, Q.left.obj (op ⦋n⦌) = Y.iterate (n + 1) ⋙ G) (er : Q.right = G)
    (eδ : ∀ (n : ℕ) (j : Fin (n + 2)), Q.left.δ j =
      eqToHom (e (n + 1)) ≫ Functor.whiskerRight (Godement.face dd (n + 1) j) G ≫
        eqToHom (e n).symm)
    (eσ : ∀ (n : ℕ) (j : Fin (n + 1)), Q.left.σ j =
      eqToHom (e n) ≫ Functor.whiskerRight (Godement.degeneracy ss n j) G ≫
        eqToHom (e (n + 1)).symm)
    (ehom : Q.hom.app (op ⦋0⦌) =
      eqToHom (e 0) ≫ Functor.whiskerRight (Godement.face dd 0 0) G ≫ eqToHom er.symm)
    (φ : Q.left ⟶ Q.left)
    (hφ : φ.app (op ⦋0⦌) ≫ Q.hom.app (op ⦋0⦌) = Q.hom.app (op ⦋0⦌)) :
    Relation.EqvGen (fun f g => Nonempty (SimplicialObject.Homotopy f g)) φ (𝟙 Q.left) := by
  obtain ⟨α, β, hα, hβ, -, -, ⟨H⟩⟩ :=
    Godement.exists_homotopy_hcomp_hcomp dd ss (𝟭 A) (𝟭 A) G G (𝟙 G) (𝟙 (𝟭 A))
      (fun n => eqToHom (e n).symm ≫ φ.app (op ⦋n⦌) ≫ eqToHom (e n)) (fun _ => 𝟙 _)
      (fun n j => conj_comm e φ (SimplexCategory.δ j).op (eδ n j))
      (fun n j => conj_comm e φ (SimplexCategory.σ j).op (eσ n j))
      (conj_comm_aug (e 0) er ehom φ hφ)
      (fun _ _ => by simp) (fun _ _ => by simp)
      (by rw [Category.id_comp]; exact (Category.comp_id _).symm)
      Q Q e er eδ eσ ehom e er eδ eσ ehom
  have hα' : α.left = 𝟙 Q.left := hom_ext_of_app fun n => by
    rw [hα n]
    exact eqToHom_id_eqToHom (e n) _ (hcomp_id_id _ _)
  have hβ' : β.left = φ := hom_ext_of_app fun n => by
    rw [hβ n, hcomp_id_left]
    exact eqToHom_conj_self (e n) _
  exact Relation.EqvGen.rel _ _ (by rw [← hβ', ← hα']; exact ⟨H⟩)

/-- An endomorphism of the standard resolution whiskered on the inside by `F`, lying over the
identity of the augmentation, is homotopic to the identity. -/
private theorem homotopic_id_of_whiskerLeft (dd : Y ⟶ 𝟭 A) (ss : Y ⟶ Y ⋙ Y) (F : B ⥤ A)
    (Q : SimplicialObject.Augmented (B ⥤ A))
    (e : ∀ n : ℕ, Q.left.obj (op ⦋n⦌) = F ⋙ Y.iterate (n + 1)) (er : Q.right = F)
    (eδ : ∀ (n : ℕ) (j : Fin (n + 2)), Q.left.δ j =
      eqToHom (e (n + 1)) ≫ Functor.whiskerLeft F (Godement.face dd (n + 1) j) ≫
        eqToHom (e n).symm)
    (eσ : ∀ (n : ℕ) (j : Fin (n + 1)), Q.left.σ j =
      eqToHom (e n) ≫ Functor.whiskerLeft F (Godement.degeneracy ss n j) ≫
        eqToHom (e (n + 1)).symm)
    (ehom : Q.hom.app (op ⦋0⦌) =
      eqToHom (e 0) ≫ Functor.whiskerLeft F (Godement.face dd 0 0) ≫ eqToHom er.symm)
    (φ : Q.left ⟶ Q.left)
    (hφ : φ.app (op ⦋0⦌) ≫ Q.hom.app (op ⦋0⦌) = Q.hom.app (op ⦋0⦌)) :
    Relation.EqvGen (fun f g => Nonempty (SimplicialObject.Homotopy f g)) φ (𝟙 Q.left) := by
  obtain ⟨α, β, hα, hβ, -, -, ⟨H⟩⟩ :=
    Godement.exists_homotopy_hcomp_hcomp dd ss F F (𝟭 A) (𝟭 A) (𝟙 (𝟭 A)) (𝟙 F)
      (fun _ => 𝟙 _) (fun n => eqToHom (e n).symm ≫ φ.app (op ⦋n⦌) ≫ eqToHom (e n))
      (fun _ _ => by simp) (fun _ _ => by simp)
      (by rw [Category.id_comp]; exact (Category.comp_id _).symm)
      (fun n j => conj_comm e φ (SimplexCategory.δ j).op (eδ n j))
      (fun n j => conj_comm e φ (SimplexCategory.σ j).op (eσ n j))
      (conj_comm_aug (e 0) er ehom φ hφ)
      Q Q e er eδ eσ ehom e er eδ eσ ehom
  have hα' : α.left = φ := hom_ext_of_app fun n => by
    rw [hα n, hcomp_id_right]
    exact eqToHom_conj_self (e n) _
  have hβ' : β.left = 𝟙 Q.left := hom_ext_of_app fun n => by
    rw [hβ n]
    exact eqToHom_id_eqToHom (e n) _ (hcomp_id_id _ _)
  exact (Relation.EqvGen.rel _ _ (by rw [← hβ', ← hα']; exact ⟨H⟩)).symm

end Homotopic

end Whiskered

namespace CategoryTheory.Adjunction

/-- **Stacks 08ND**.
Let `V : A ⥤ S` have a left adjoint `U : S ⥤ A`, and let `X` be the standard resolution: the
augmented simplicial object of `A ⥤ A` with terms the iterates `Z (n + 1)` of the comonad
`U ∘ V`, faces and degeneracies `d`, `s` whiskering its counit, resp. its comultiplication,
into the `j`-th factor, point `Z 0 = 𝟭 A` and augmentation `ε₀ = d 0 0`. Then the whiskered
augmentations `1_V ⋆ ε : V ∘ X ⟶ V` and `ε ⋆ 1_U : X ∘ U ⟶ U` are homotopy equivalences: each
admits a morphism `r` in the other direction such that both composites with it are homotopic to
the identities, homotopic meaning related by the equivalence relation generated by the existence
of a simplicial homotopy. -/
@[stacks 08ND]
public theorem exists_homotopyInverse_whiskered_standardResolution
    {A : Type u₁} [Category.{v₁} A] {S : Type u₂} [Category.{v₂} S]
    {U : S ⥤ A} {V : A ⥤ S} (adj : U ⊣ V)
    (Z : ℕ → (A ⥤ A)) (hZ : ∀ n : ℕ, Z (n + 1) = Z n ⋙ (adj.toComonad : A ⥤ A))
    (d : ∀ n : ℕ, Fin (n + 1) → (Z (n + 1) ⟶ Z n))
    (s : ∀ n : ℕ, Fin (n + 1) → (Z (n + 1) ⟶ Z (n + 2)))
    (hZ₀ : Z 0 = 𝟭 A)
    (hd₀ : ∀ n : ℕ, d n 0 = eqToHom (hZ n) ≫ Functor.whiskerLeft (Z n) adj.toComonad.ε)
    (hd : ∀ (n : ℕ) (j : Fin (n + 1)), d (n + 1) j.succ =
      eqToHom (hZ (n + 1)) ≫ Functor.whiskerRight (d n j) (adj.toComonad : A ⥤ A) ≫
        eqToHom (hZ n).symm)
    (hs₀ : ∀ n : ℕ, s n 0 = eqToHom (hZ n) ≫ Functor.whiskerLeft (Z n) adj.toComonad.δ ≫
      Functor.whiskerRight (eqToHom (hZ n).symm) (adj.toComonad : A ⥤ A) ≫
        eqToHom (hZ (n + 1)).symm)
    (hs : ∀ (n : ℕ) (j : Fin (n + 1)), s (n + 1) j.succ =
      eqToHom (hZ (n + 1)) ≫ Functor.whiskerRight (s n j) (adj.toComonad : A ⥤ A) ≫
        eqToHom (hZ (n + 2)).symm)
    (X : SimplicialObject.Augmented (A ⥤ A))
    (h : ∀ n : ℕ, X.left.obj (Opposite.op ⦋n⦌) = Z (n + 1)) (hX : X.right = Z 0)
    (hδ : ∀ (n : ℕ) (j : Fin (n + 2)),
      X.left.δ j = eqToHom (h (n + 1)) ≫ d (n + 1) j ≫ eqToHom (h n).symm)
    (hσ : ∀ (n : ℕ) (j : Fin (n + 1)),
      X.left.σ j = eqToHom (h n) ≫ s n j ≫ eqToHom (h (n + 1)).symm)
    (hε : X.hom.app (Opposite.op ⦋0⦌) = eqToHom (h 0) ≫ d 0 0 ≫ eqToHom hX.symm)
    (a : X.left ⋙ (Functor.whiskeringRight A A S).obj V ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj (X.right ⋙ V))
    (ha : ∀ n : SimplexCategoryᵒᵖ, a.app n = Functor.whiskerRight (X.hom.app n) V)
    (b : X.left ⋙ (Functor.whiskeringLeft S A A).obj U ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj (U ⋙ X.right))
    (hb : ∀ n : SimplexCategoryᵒᵖ, b.app n = Functor.whiskerLeft U (X.hom.app n)) :
    (∃ r : (Functor.const SimplexCategoryᵒᵖ).obj (X.right ⋙ V) ⟶
        X.left ⋙ (Functor.whiskeringRight A A S).obj V,
      Relation.EqvGen (fun f g => Nonempty (SimplicialObject.Homotopy f g)) (a ≫ r) (𝟙 _) ∧
      Relation.EqvGen (fun f g => Nonempty (SimplicialObject.Homotopy f g)) (r ≫ a) (𝟙 _)) ∧
    (∃ r : (Functor.const SimplexCategoryᵒᵖ).obj (U ⋙ X.right) ⟶
        X.left ⋙ (Functor.whiskeringLeft S A A).obj U,
      Relation.EqvGen (fun f g => Nonempty (SimplicialObject.Homotopy f g)) (b ≫ r) (𝟙 _) ∧
      Relation.EqvGen (fun f g => Nonempty (SimplicialObject.Homotopy f g)) (r ≫ b) (𝟙 _)) := by
  have hZeq : Z = Functor.iterate (adj.toComonad : A ⥤ A) := by
    funext n
    induction n with
    | zero => exact hZ₀
    | succ n ih =>
      rw [hZ n, ih]
      rfl
  subst hZeq
  have hdeq : d = Godement.face adj.toComonad.ε :=
    funext fun n => funext (face_eq_face adj.toComonad.ε hZ d hd₀ hd n)
  have hseq : s = Godement.degeneracy adj.toComonad.δ :=
    funext fun n => funext (degeneracy_eq_degeneracy adj.toComonad.δ hZ s hs₀ hs n)
  subst hdeq
  subst hseq
  have ha₀ : (eqToHom (congrArg (fun T => T ⋙ V) hX) ≫ Functor.whiskerLeft V adj.unit ≫
      eqToHom (congrArg (fun T => T ⋙ V) (h 0)).symm) ≫ a.app (Opposite.op ⦋0⦌) =
      𝟙 (X.right ⋙ V) := by
    rw [ha (Opposite.op ⦋0⦌), whiskerRight_transport (h 0) hX hε V]
    exact conj_comp_conj_eq_id _ _ _ _ (whiskerLeft_unit_comp_whiskerRight_counit adj)
  have hb₀ : (eqToHom (congrArg (fun T => U ⋙ T) hX) ≫ Functor.whiskerRight adj.unit U ≫
      eqToHom (congrArg (fun T => U ⋙ T) (h 0)).symm) ≫ b.app (Opposite.op ⦋0⦌) =
      𝟙 (U ⋙ X.right) := by
    rw [hb (Opposite.op ⦋0⦌), whiskerLeft_transport (h 0) hX hε U]
    exact conj_comp_conj_eq_id _ _ _ _ (whiskerRight_unit_comp_whiskerLeft_counit adj)
  exact ⟨exists_homotopyInverse_of_endo_homotopic_id
      ⟨X.left ⋙ (Functor.whiskeringRight A A S).obj V, X.right ⋙ V, a⟩ _ ha₀
      (homotopic_id_of_whiskerRight adj.toComonad.ε adj.toComonad.δ V _
        (fun n => congrArg (fun T => T ⋙ V) (h n)) (congrArg (fun T => T ⋙ V) hX)
        (fun n j => whiskerRight_transport (h (n + 1)) (h n) (hδ n j) V)
        (fun n j => whiskerRight_transport (h n) (h (n + 1)) (hσ n j) V)
        ((ha (Opposite.op ⦋0⦌)).trans (whiskerRight_transport (h 0) hX hε V))),
    exists_homotopyInverse_of_endo_homotopic_id
      ⟨X.left ⋙ (Functor.whiskeringLeft S A A).obj U, U ⋙ X.right, b⟩ _ hb₀
      (homotopic_id_of_whiskerLeft adj.toComonad.ε adj.toComonad.δ U _
        (fun n => congrArg (fun T => U ⋙ T) (h n)) (congrArg (fun T => U ⋙ T) hX)
        (fun n j => whiskerLeft_transport (h (n + 1)) (h n) (hδ n j) U)
        (fun n j => whiskerLeft_transport (h n) (h (n + 1)) (hσ n j) U)
        ((hb (Opposite.op ⦋0⦌)).trans (whiskerLeft_transport (h 0) hX hε U)))⟩

end CategoryTheory.Adjunction

/-! ### The standard resolution of an algebra by free algebras -/

section FreeAlgebras

open AlgCat

/-- The inverse of the universal property of a free algebra, at the identity map, is the
inclusion of the variables: `(FreeAlgebra.lift A).symm (AlgHom.id A (FreeAlgebra A E)) x = [x]`. -/
private lemma lift_symm_id_apply {A : Type u} [CommRing A] (E : Type u) (x : E) :
    ((FreeAlgebra.lift A).symm (AlgHom.id A (FreeAlgebra A E))) x = FreeAlgebra.ι A x := by
  rw [FreeAlgebra.lift_symm_apply]
  rfl

/-- The unit of the free/forget adjunction for `A`-algebras is the inclusion of the variables:
`AlgCat.adj.unit.app E x = [x]`. -/
private lemma unit_app_apply {A : Type u} [CommRing A] (E : Type u) (x : E) :
    (adj (R := A)).unit.app E x = FreeAlgebra.ι A x :=
  lift_symm_id_apply E x

end FreeAlgebras

namespace AlgCat

/-- The noncommutative analogue of Stacks Example 09CB. Let `A` be a ring and let `X` be an
object of `AlgCat A`, the category of all, not necessarily commutative, `A`-algebras. In the tower
`Xₙ = A⟨A⟨⋯⟨X⟩⋯⟩⟩` (`n + 1` brackets) of the standard resolution of `X` for the free/forget
adjunction `AlgCat.adj`, each stage being the noncommutative free algebra `FreeAlgebra` on the
previous one, the faces `dⁿⱼ` and degeneracies `sⁿⱼ` are described on the variables by:
`dⁿ₀` substitutes for the variable `[z]` the element `z`, so it is `FreeAlgebra.lift A id` and
`d⁰₀ : A⟨X⟩ ⟶ X` is the augmentation; `sⁿ₀` sends `[z]` to `[[z]]`; and `dⁿ⁺¹ⱼ₊₁`, `sⁿ⁺¹ⱼ₊₁` send
`[z]` to `[dⁿⱼ(z)]`, resp. `[sⁿⱼ(z)]`. Stacks works instead with commutative `A`-algebras and
polynomial algebras; that statement is `CommAlgCat.face_eq_aeval_and_degeneracy_eq_rename`. -/
public theorem face_eq_lift_and_degeneracy_eq_lift {A : Type u} [CommRing A] (X : AlgCat.{u} A)
    (n : ℕ) :
    ((Godement.face (adj (R := A)).toComonad.ε n 0).app X).hom = FreeAlgebra.lift A id ∧
      (∀ j : Fin (n + 1), ((Godement.face (adj (R := A)).toComonad.ε (n + 1) j.succ).app X).hom =
        FreeAlgebra.lift A (FreeAlgebra.ι A ∘
          ((Godement.face (adj (R := A)).toComonad.ε n j).app X).hom)) ∧
      ((Godement.degeneracy (adj (R := A)).toComonad.δ n 0).app X).hom =
        FreeAlgebra.lift A (fun z => FreeAlgebra.ι A (FreeAlgebra.ι A z)) ∧
      (∀ j : Fin (n + 1),
        ((Godement.degeneracy (adj (R := A)).toComonad.δ (n + 1) j.succ).app X).hom =
          FreeAlgebra.lift A (FreeAlgebra.ι A ∘
            ((Godement.degeneracy (adj (R := A)).toComonad.δ n j).app X).hom)) := by
  refine ⟨?_, fun j => rfl, ?_, fun j => rfl⟩
  · cases n <;> rfl
  · have h : ((Godement.degeneracy (adj (R := A)).toComonad.δ n 0).app X).hom
        = FreeAlgebra.lift A (fun z =>
            FreeAlgebra.ι A ((adj (R := A)).unit.app
              (ToType (((adj (R := A)).toComonad.toFunctor.iterate n).obj X)) z)) := by
      cases n <;> rfl
    rw [h]
    exact congrArg _ (funext fun z => congrArg (FreeAlgebra.ι A) (unit_app_apply _ z))

/-- The variable `[b]` of `Y(B) = A[B]`, the free `A`-algebra on the underlying set of `B`, where
`Y` is the comonad of the free/forget adjunction. -/
public def comonadι {A : Type u} [CommRing A] (B : AlgCat.{u} A) (b : B) :
    ((adj (R := A)).toComonad.obj B : Type u) :=
  FreeAlgebra.ι A b

/-- The variable `[e]` of the free `A`-algebra `A[E]` on a set `E`. -/
public def freeι {A : Type u} [CommRing A] (E : Type u) (e : E) : ((free A).obj E : Type u) :=
  FreeAlgebra.ι A e

end AlgCat

/-! ### The homotopy inverses for free algebras are the iterated variables -/

section Variables

open AlgCat

/-! #### Generic transport lemmas for `eqToHom`-conjugated pinnings -/

/-- If `x` is presented as `eqToHom ≫ x' ≫ eqToHom` and `f`, `g` intertwine `x`, then their
conjugates intertwine `x'`. -/
private theorem comm_of_eqToHom_conj {D : Type u} [Category.{v} D] {P P' R R' : D}
    (eP : P = P') (eR : R = R') {x : P ⟶ R} {x' : P' ⟶ R'}
    (hx : x = eqToHom eP ≫ x' ≫ eqToHom eR.symm) (f : P ⟶ P) (g : R ⟶ R)
    (hfg : f ≫ x = x ≫ g) :
    (eqToHom eP.symm ≫ f ≫ eqToHom eP) ≫ x' = x' ≫ (eqToHom eR.symm ≫ g ≫ eqToHom eR) := by
  subst eP; subst eR
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hx ⊢
  subst hx
  exact hfg

/-- If `x` is presented as `eqToHom ≫ x' ≫ eqToHom` and `f` fixes `x`, then the conjugate of `f`
fixes `x'`. -/
private theorem comm_of_eqToHom_conj_id {D : Type u} [Category.{v} D] {P P' R R' : D}
    (eP : P = P') (eR : R = R') {x : P ⟶ R} {x' : P' ⟶ R'}
    (hx : x = eqToHom eP ≫ x' ≫ eqToHom eR.symm) (f : P ⟶ P) (hfx : f ≫ x = x) :
    (eqToHom eP.symm ≫ f ≫ eqToHom eP) ≫ x' = x' := by
  subst eP; subst eR
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hx ⊢
  subst hx
  exact hfx

/-- A functor carries an `eqToHom`-conjugated presentation of a morphism to one of its image. -/
private theorem map_conj {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (W : C ⥤ D) {P P' R R' : C} (eP : P = P') (eR : R = R') {x : P ⟶ R} {x' : P' ⟶ R'}
    (hx : x = eqToHom eP ≫ x' ≫ eqToHom eR.symm) :
    W.map x = eqToHom (congrArg W.obj eP) ≫ W.map x' ≫ eqToHom (congrArg W.obj eR).symm := by
  subst eP; subst eR
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hx ⊢
  rw [hx]

/-- A right inverse in an `eqToHom`-conjugated presentation is a right inverse. -/
private theorem conj_comp_eq_id {D : Type u} [Category.{v} D] {P P' R R' : D}
    (eP : P = P') (eR : R = R') {w : P ⟶ R} {w' : P' ⟶ R'} {t : R' ⟶ P'}
    (hw : w = eqToHom eP ≫ w' ≫ eqToHom eR.symm) (ht : t ≫ w' = 𝟙 R') :
    (eqToHom eR ≫ t ≫ eqToHom eP.symm) ≫ w = 𝟙 R := by
  subst eP; subst eR
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hw ht ⊢
  rw [hw]
  exact ht

/-- A morphism out of a constant simplicial object satisfies `r_{n+1} = r_n ∘ s^n_j`. -/
private theorem app_succ_eq_comp_sigma {D : Type u} [Category.{v} D] {W : D}
    {K : SimplicialObject D} (r : (Functor.const SimplexCategoryᵒᵖ).obj W ⟶ K)
    (n : ℕ) (j : Fin (n + 1)) : r.app (op ⦋n + 1⦌) = r.app (op ⦋n⦌) ≫ K.σ j := by
  simpa [SimplicialObject.σ] using r.naturality (SimplexCategory.σ j).op

/-- A functor transports a pinning. If the terms, faces, degeneracies and augmentation of an
augmented simplicial object `X` of endofunctors of `C` are pinned to the powers of `Y`, the faces
`Godement.face dd` and the degeneracies `Godement.degeneracy ss`, and `c` is the whiskering of the
augmentation of `X` by `W`, then `X ⋙ W` is pinned to the image of that Godement system under
`W`. -/
private theorem exists_map_pinning {C : Type u} [Category.{v} C] {D : Type u₂} [Category.{v₂} D]
    {Y : C ⥤ C} (dd : Y ⟶ 𝟭 C) (ss : Y ⟶ Y ⋙ Y) (W : (C ⥤ C) ⥤ D)
    (X : SimplicialObject.Augmented (C ⥤ C))
    (h : ∀ n : ℕ, X.left.obj (op ⦋n⦌) = Y.iterate (n + 1)) (hX : X.right = 𝟭 C)
    (hδ : ∀ (n : ℕ) (j : Fin (n + 2)), X.left.δ j =
      eqToHom (h (n + 1)) ≫ Godement.face dd (n + 1) j ≫ eqToHom (h n).symm)
    (hσ : ∀ (n : ℕ) (j : Fin (n + 1)), X.left.σ j =
      eqToHom (h n) ≫ Godement.degeneracy ss n j ≫ eqToHom (h (n + 1)).symm)
    (hε : X.hom.app (op ⦋0⦌) = eqToHom (h 0) ≫ Godement.face dd 0 0 ≫ eqToHom hX.symm)
    (c : X.left ⋙ W ⟶ (Functor.const SimplexCategoryᵒᵖ).obj (W.obj X.right))
    (hc : c.app (op ⦋0⦌) = W.map (X.hom.app (op ⦋0⦌))) :
    ∃ (e : ∀ n : ℕ, (X.left ⋙ W).obj (op ⦋n⦌) = W.obj (Y.iterate (n + 1)))
      (er : W.obj X.right = W.obj (𝟭 C)),
      (∀ (n : ℕ) (j : Fin (n + 2)), SimplicialObject.δ (X.left ⋙ W) j =
        eqToHom (e (n + 1)) ≫ W.map (Godement.face dd (n + 1) j) ≫ eqToHom (e n).symm) ∧
      (∀ (n : ℕ) (j : Fin (n + 1)), SimplicialObject.σ (X.left ⋙ W) j =
        eqToHom (e n) ≫ W.map (Godement.degeneracy ss n j) ≫ eqToHom (e (n + 1)).symm) ∧
      c.app (op ⦋0⦌) = eqToHom (e 0) ≫ W.map (Godement.face dd 0 0) ≫ eqToHom er.symm :=
  ⟨fun n => congrArg W.obj (h n), congrArg W.obj hX,
    fun n j => map_conj W (h (n + 1)) (h n) (hδ n j),
    fun n j => map_conj W (h n) (h (n + 1)) (hσ n j),
    hc.trans (map_conj W (h 0) hX hε)⟩

/-! #### Sections of a conjugated Godement resolution -/

/-- Let `Q` be an augmented simplicial object of `D` whose terms, faces, degeneracies and
augmentation are pinned to the image under `W` of the powers of `Y`, the faces `Godement.face dd`
and the degeneracies `Godement.degeneracy ss`, and let `h₀` split its augmentation in degree `0`.
Then `h₀` extends to a section `r` of `Q.hom`, and the endomorphism `Q.hom ≫ r` of `Q.left` is,
degreewise and after transport, a family `ψ` commuting with the faces and the degeneracies and
lying over the identity. -/
private theorem exists_section_conj_comm
    {C : Type u} [Category.{v} C] {D : Type u₂} [Category.{v₂} D] {Y : C ⥤ C}
    (dd : Y ⟶ 𝟭 C) (ss : Y ⟶ Y ⋙ Y) (W : (C ⥤ C) ⥤ D) (Q : SimplicialObject.Augmented D)
    (e : ∀ n : ℕ, Q.left.obj (op ⦋n⦌) = W.obj (Y.iterate (n + 1)))
    (er : Q.right = W.obj (Y.iterate 0))
    (eδ : ∀ (n : ℕ) (j : Fin (n + 2)), Q.left.δ j =
      eqToHom (e (n + 1)) ≫ W.map (Godement.face dd (n + 1) j) ≫ eqToHom (e n).symm)
    (eσ : ∀ (n : ℕ) (j : Fin (n + 1)), Q.left.σ j =
      eqToHom (e n) ≫ W.map (Godement.degeneracy ss n j) ≫ eqToHom (e (n + 1)).symm)
    (ehom : Q.hom.app (op ⦋0⦌) =
      eqToHom (e 0) ≫ W.map (Godement.face dd 0 0) ≫ eqToHom er.symm)
    (h₀ : Q.right ⟶ Q.left.obj (op ⦋0⦌)) (hh₀ : h₀ ≫ Q.hom.app (op ⦋0⦌) = 𝟙 Q.right) :
    ∃ (r : (Functor.const SimplexCategoryᵒᵖ).obj Q.right ⟶ Q.left)
      (ψ : (n : ℕ) → (W.obj (Y.iterate (n + 1)) ⟶ W.obj (Y.iterate (n + 1)))),
      r.app (op ⦋0⦌) = h₀ ∧ r ≫ Q.hom = 𝟙 _ ∧
      (∀ n : ℕ, eqToHom (e n) ≫ ψ n ≫ eqToHom (e n).symm = (Q.hom ≫ r).app (op ⦋n⦌)) ∧
      (∀ (n : ℕ) (j : Fin (n + 2)), ψ (n + 1) ≫ W.map (Godement.face dd (n + 1) j) =
        W.map (Godement.face dd (n + 1) j) ≫ ψ n) ∧
      (∀ (n : ℕ) (j : Fin (n + 1)), ψ n ≫ W.map (Godement.degeneracy ss n j) =
        W.map (Godement.degeneracy ss n j) ≫ ψ (n + 1)) ∧
      ψ 0 ≫ W.map (Godement.face dd 0 0) = W.map (Godement.face dd 0 0) := by
  obtain ⟨r, hr0, hr⟩ :=
    SimplicialObject.Augmented.exists_section_of_comp_hom_app_zero_eq_id Q h₀ hh₀
  have hnat : ∀ {n m : ℕ} (g : (op ⦋n⦌ : SimplexCategoryᵒᵖ) ⟶ op ⦋m⦌),
      (Q.hom ≫ r).app (op ⦋n⦌) ≫ Q.left.map g = Q.left.map g ≫ (Q.hom ≫ r).app (op ⦋m⦌) :=
    fun g => ((Q.hom ≫ r).naturality g).symm
  exact ⟨r, fun n => eqToHom (e n).symm ≫ (Q.hom ≫ r).app (op ⦋n⦌) ≫ eqToHom (e n),
    hr0, hr, fun n => by simp,
    fun n j => comm_of_eqToHom_conj (e (n + 1)) (e n) (eδ n j) _ _ (hnat _),
    fun n j => comm_of_eqToHom_conj (e n) (e (n + 1)) (eσ n j) _ _ (hnat _),
    comm_of_eqToHom_conj_id (e 0) er ehom _
      (comp_hom_app_zero_eq_hom_app_zero Q r hr)⟩

/-- A morphism `r` out of a constant simplicial object satisfies `r_{n+1} = r_n ≫ s^n_0`, so if its
degree-`0` component is `p 0` and the family `p` satisfies the same recursion
`p n ≫ s^n_0 = p (n + 1)`, then `r_n` is `p n` in every degree. -/
private theorem const_app_eq_of_degeneracy_step
    {C : Type u} [Category.{v} C] {D : Type u₂} [Category.{v₂} D] {Y : C ⥤ C}
    (ss : Y ⟶ Y ⋙ Y) (W : (C ⥤ C) ⥤ D) {K : SimplicialObject D} {S T : D}
    (r : (Functor.const SimplexCategoryᵒᵖ).obj S ⟶ K)
    (e : ∀ n : ℕ, K.obj (op ⦋n⦌) = W.obj (Y.iterate (n + 1)))
    (eσ : ∀ (n : ℕ) (j : Fin (n + 1)), K.σ j =
      eqToHom (e n) ≫ W.map (Godement.degeneracy ss n j) ≫ eqToHom (e (n + 1)).symm)
    (er : S = T) (p : ∀ n : ℕ, T ⟶ W.obj (Y.iterate (n + 1)))
    (hp0 : r.app (op ⦋0⦌) = eqToHom er ≫ p 0 ≫ eqToHom (e 0).symm)
    (hp : ∀ n : ℕ, p n ≫ W.map (Godement.degeneracy ss n 0) = p (n + 1)) (n : ℕ) :
    r.app (op ⦋n⦌) = eqToHom er ≫ p n ≫ eqToHom (e n).symm := by
  induction n with
  | zero => exact hp0
  | succ m ih =>
    rw [app_succ_eq_comp_sigma r m 0, ih, eσ m 0, ← hp m]
    simp

/-! #### The two halves of the homotopy equivalence, for a general Godement system -/

/-- Godement's standard resolution whiskered on the outside by a functor `G` is a homotopy
equivalence over its augmentation, with the section extending any prescribed splitting `h₀` in
degree `0`. -/
private theorem key_whiskerRight
    {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    {Y : A ⥤ A} (dd : Y ⟶ 𝟭 A) (ss : Y ⟶ Y ⋙ Y) (G : A ⥤ B)
    (Q : SimplicialObject.Augmented (A ⥤ B))
    (e : ∀ n : ℕ, Q.left.obj (op ⦋n⦌) = Y.iterate (n + 1) ⋙ G)
    (er : Q.right = G)
    (eδ : ∀ (n : ℕ) (j : Fin (n + 2)), Q.left.δ j =
      eqToHom (e (n + 1)) ≫ Functor.whiskerRight (Godement.face dd (n + 1) j) G ≫
        eqToHom (e n).symm)
    (eσ : ∀ (n : ℕ) (j : Fin (n + 1)), Q.left.σ j =
      eqToHom (e n) ≫ Functor.whiskerRight (Godement.degeneracy ss n j) G ≫
        eqToHom (e (n + 1)).symm)
    (ehom : Q.hom.app (op ⦋0⦌) =
      eqToHom (e 0) ≫ Functor.whiskerRight (Godement.face dd 0 0) G ≫ eqToHom er.symm)
    (h₀ : Q.right ⟶ Q.left.obj (op ⦋0⦌)) (hh₀ : h₀ ≫ Q.hom.app (op ⦋0⦌) = 𝟙 Q.right) :
    ∃ r : (Functor.const SimplexCategoryᵒᵖ).obj Q.right ⟶ Q.left,
      r.app (op ⦋0⦌) = h₀ ∧
      Relation.EqvGen (fun f g => Nonempty (SimplicialObject.Homotopy f g)) (Q.hom ≫ r) (𝟙 _) ∧
      Relation.EqvGen (fun f g => Nonempty (SimplicialObject.Homotopy f g)) (r ≫ Q.hom)
        (𝟙 _) := by
  obtain ⟨r, -, hr0, hr, -, -, -, -⟩ :=
    exists_section_conj_comm dd ss ((Functor.whiskeringRight A A B).obj G) Q e er eδ eσ ehom
      h₀ hh₀
  refine ⟨r, hr0, homotopic_id_of_whiskerRight dd ss G Q e er eδ eσ ehom _ ?_,
    by rw [hr]; exact Relation.EqvGen.refl _⟩
  exact comp_hom_app_zero_eq_hom_app_zero Q r hr

/-- Godement's standard resolution whiskered on the inside by a functor `F` is a homotopy
equivalence over its augmentation, with the section extending any prescribed splitting `h₀` in
degree `0`. -/
private theorem key_whiskerLeft
    {A : Type u₁} [Category.{v₁} A] {C : Type u} [Category.{v} C]
    {Y : C ⥤ C} (dd : Y ⟶ 𝟭 C) (ss : Y ⟶ Y ⋙ Y) (F : A ⥤ C)
    (Q : SimplicialObject.Augmented (A ⥤ C))
    (e : ∀ n : ℕ, Q.left.obj (op ⦋n⦌) = F ⋙ Y.iterate (n + 1))
    (er : Q.right = F)
    (eδ : ∀ (n : ℕ) (j : Fin (n + 2)), Q.left.δ j =
      eqToHom (e (n + 1)) ≫ Functor.whiskerLeft F (Godement.face dd (n + 1) j) ≫
        eqToHom (e n).symm)
    (eσ : ∀ (n : ℕ) (j : Fin (n + 1)), Q.left.σ j =
      eqToHom (e n) ≫ Functor.whiskerLeft F (Godement.degeneracy ss n j) ≫
        eqToHom (e (n + 1)).symm)
    (ehom : Q.hom.app (op ⦋0⦌) =
      eqToHom (e 0) ≫ Functor.whiskerLeft F (Godement.face dd 0 0) ≫ eqToHom er.symm)
    (h₀ : Q.right ⟶ Q.left.obj (op ⦋0⦌)) (hh₀ : h₀ ≫ Q.hom.app (op ⦋0⦌) = 𝟙 Q.right) :
    ∃ r : (Functor.const SimplexCategoryᵒᵖ).obj Q.right ⟶ Q.left,
      r.app (op ⦋0⦌) = h₀ ∧
      Relation.EqvGen (fun f g => Nonempty (SimplicialObject.Homotopy f g)) (Q.hom ≫ r) (𝟙 _) ∧
      Relation.EqvGen (fun f g => Nonempty (SimplicialObject.Homotopy f g)) (r ≫ Q.hom)
        (𝟙 _) := by
  obtain ⟨r, -, hr0, hr, -, -, -, -⟩ :=
    exists_section_conj_comm dd ss ((Functor.whiskeringLeft A C C).obj F) Q e er eδ eσ ehom h₀ hh₀
  refine ⟨r, hr0, homotopic_id_of_whiskerLeft dd ss F Q e er eδ eσ ehom _ ?_,
    by rw [hr]; exact Relation.EqvGen.refl _⟩
  exact comp_hom_app_zero_eq_hom_app_zero Q r hr

/-! #### The free/forget adjunction: the variables -/

/-- The lift of `z ↦ [[z]]` sends a variable `[y]` to `[[y]]`. -/
private theorem lift_ι_ι {A : Type u} [CommRing A] (E : Type u) (y : E) :
    FreeAlgebra.lift A (fun z : E => FreeAlgebra.ι A (FreeAlgebra.ι A z)) (FreeAlgebra.ι A y)
      = FreeAlgebra.ι A (FreeAlgebra.ι A y) :=
  FreeAlgebra.lift_ι_apply _ _

/-- The zeroth face of the standard resolution of an `A`-algebra by free algebras deletes the
outer bracket of a variable: `d^n_0 [y] = y`. -/
private theorem face_zero_hom_comonadι {A : Type u} [CommRing A] (B : AlgCat.{u} A) (n : ℕ)
    (y : ((AlgCat.adj A).toComonad.toFunctor.iterate n).obj B) :
    ((Godement.face (AlgCat.adj A).toComonad.ε n 0).app B).hom (comonadι _ y) = y :=
  (DFunLike.congr_fun (AlgCat.face_eq_lift_and_degeneracy_eq_lift B n).1 _).trans
    (FreeAlgebra.lift_ι_apply _ _)

/-- The zeroth degeneracy of the standard resolution of an `A`-algebra by free algebras doubles
the bracket of a variable: `s^n_0 [y] = [[y]]`. -/
private theorem degeneracy_zero_hom_comonadι {A : Type u} [CommRing A] (B : AlgCat.{u} A) (n : ℕ)
    (y : ((AlgCat.adj A).toComonad.toFunctor.iterate n).obj B) :
    ((Godement.degeneracy (AlgCat.adj A).toComonad.δ n 0).app B).hom (comonadι _ y) =
      comonadι _ (comonadι _ y) := by
  obtain ⟨-, -, hs₀, -⟩ := AlgCat.face_eq_lift_and_degeneracy_eq_lift B n
  exact (DFunLike.congr_fun hs₀ _).trans (lift_ι_ι _ y)

/-- The iterated variables `b ↦ [⋯[b]⋯]` of an `A`-algebra split the augmentation of the standard
resolution: deleting the outer bracket of `ρ 0` recovers the identity of the forgetful functor. -/
private theorem iteratedι_comp_face_zero {A : Type u} [CommRing A]
    (ρ : ∀ n : ℕ, forget (AlgCat.{u} A) ⟶
      (AlgCat.adj A).toComonad.toFunctor.iterate (n + 1) ⋙ forget (AlgCat.{u} A))
    (hρ₀ : ∀ (B : AlgCat.{u} A) (x : B), (ρ 0).app B x = comonadι B x) :
    ρ 0 ≫ Functor.whiskerRight
        (Godement.face (AlgCat.adj A).toComonad.ε 0 0) (forget (AlgCat.{u} A)) =
      𝟙 (forget (AlgCat.{u} A)) := by
  ext B x
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, TypeCat.Fun.toFun_apply,
    CategoryTheory.comp_apply, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, NatTrans.id_app,
    CategoryTheory.id_apply]
  rw [hρ₀]
  exact face_zero_hom_comonadι B 0 x

/-- The iterated variables of an `A`-algebra are compatible with the zeroth degeneracy: doubling
the innermost bracket of `ρ n` gives `ρ (n + 1)`. -/
private theorem iteratedι_comp_degeneracy_zero {A : Type u} [CommRing A]
    (ρ : ∀ n : ℕ, forget (AlgCat.{u} A) ⟶
      (AlgCat.adj A).toComonad.toFunctor.iterate (n + 1) ⋙ forget (AlgCat.{u} A))
    (hρ₀ : ∀ (B : AlgCat.{u} A) (x : B), (ρ 0).app B x = comonadι B x)
    (hρ : ∀ (n : ℕ) (B : AlgCat.{u} A) (x : B),
      (ρ (n + 1)).app B x = comonadι _ ((ρ n).app B x)) (n : ℕ) :
    ρ n ≫ Functor.whiskerRight
        (Godement.degeneracy (AlgCat.adj A).toComonad.δ n 0) (forget (AlgCat.{u} A)) =
      ρ (n + 1) := by
  ext B x
  obtain ⟨y, hy⟩ : ∃ y, (ρ n).app B x = comonadι _ y := by
    cases n with
    | zero => exact ⟨x, hρ₀ B x⟩
    | succ m => exact ⟨(ρ m).app B x, hρ m B x⟩
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, TypeCat.Fun.toFun_apply,
    CategoryTheory.comp_apply, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk]
  rw [hρ n B x, hy]
  exact degeneracy_zero_hom_comonadι B n y

/-- Two morphisms out of a free `A`-algebra agree as soon as they agree on the variables. -/
private theorem free_hom_ext {A : Type u} [CommRing A] {E : Type u} {B : AlgCat.{u} A}
    {f g : (AlgCat.free A).obj E ⟶ B} (h : ∀ e, f.hom (freeι E e) = g.hom (freeι E e)) :
    f = g :=
  AlgCat.hom_ext A (FreeAlgebra.hom_ext (funext h))

/-- The iterated variables `[e] ↦ [⋯[e]⋯]` of a free `A`-algebra split the augmentation of the
standard resolution: deleting the outer bracket of `τ 0` recovers the identity of the free
algebra functor. -/
private theorem freeIteratedι_comp_face_zero {A : Type u} [CommRing A]
    (τ : ∀ n : ℕ, AlgCat.free A ⟶
      AlgCat.free A ⋙ (AlgCat.adj A).toComonad.toFunctor.iterate (n + 1))
    (hτ₀ : ∀ (E : Type u) (e : E), ((τ 0).app E).hom (freeι E e) = comonadι _ (freeι E e)) :
    τ 0 ≫ Functor.whiskerLeft (AlgCat.free A)
      (Godement.face (AlgCat.adj A).toComonad.ε 0 0) = 𝟙 (AlgCat.free A) := by
  refine NatTrans.ext (funext fun E => free_hom_ext fun e => ?_)
  rw [NatTrans.comp_app, NatTrans.id_app, AlgCat.hom_comp, AlgHom.comp_apply, AlgCat.hom_id,
    AlgHom.id_apply, Functor.whiskerLeft_app, hτ₀]
  exact face_zero_hom_comonadι _ 0 (freeι E e)

/-- The iterated variables of a free `A`-algebra are compatible with the zeroth degeneracy:
doubling the innermost bracket of `τ n` gives `τ (n + 1)`. -/
private theorem freeIteratedι_comp_degeneracy_zero {A : Type u} [CommRing A]
    (τ : ∀ n : ℕ, AlgCat.free A ⟶
      AlgCat.free A ⋙ (AlgCat.adj A).toComonad.toFunctor.iterate (n + 1))
    (hτ₀ : ∀ (E : Type u) (e : E), ((τ 0).app E).hom (freeι E e) = comonadι _ (freeι E e))
    (hτ : ∀ (n : ℕ) (E : Type u) (e : E), ((τ (n + 1)).app E).hom (freeι E e) =
      comonadι _ (((τ n).app E).hom (freeι E e))) (n : ℕ) :
    τ n ≫ Functor.whiskerLeft (AlgCat.free A)
      (Godement.degeneracy (AlgCat.adj A).toComonad.δ n 0) = τ (n + 1) := by
  refine NatTrans.ext (funext fun E => free_hom_ext fun e => ?_)
  obtain ⟨y, hy⟩ : ∃ y, ((τ n).app E).hom (freeι E e) = comonadι _ y := by
    cases n with
    | zero => exact ⟨freeι E e, hτ₀ E e⟩
    | succ m => exact ⟨((τ m).app E).hom (freeι E e), hτ m E e⟩
  rw [NatTrans.comp_app, AlgCat.hom_comp, AlgHom.comp_apply, Functor.whiskerLeft_app, hτ n E e,
    hy]
  exact degeneracy_zero_hom_comonadι _ n y

end Variables

namespace CategoryTheory.Godement

/-- Let `X` be an augmented simplicial object of `C ⥤ C` whose terms, faces, degeneracies and
augmentation are pinned to the powers of `Y`, `Godement.face dd`, `Godement.degeneracy ss` and
`d⁰₀`, and let `a = 1_G ⋆ ε : G ∘ X ⟶ G` be its augmentation whiskered on the outside by a functor
`G`. Let `p n : G ⟶ G ∘ Y^{n+1}` be a family with `(1_G ⋆ d⁰₀) ∘ p 0 = 1_G` and
`(1_G ⋆ sⁿ₀) ∘ p n = p (n + 1)`. Then `a` is a homotopy equivalence whose homotopy inverse is
`p n` in degree `n`: both composites with it are related to the identity by the equivalence
relation generated by the existence of a simplicial homotopy. -/
public theorem exists_homotopyInverse_whiskerRight_eq
    {C : Type u₁} [Category.{v₁} C] {B : Type u₂} [Category.{v₂} B]
    {Y : C ⥤ C} (dd : Y ⟶ 𝟭 C) (ss : Y ⟶ Y ⋙ Y) (G : C ⥤ B)
    (X : SimplicialObject.Augmented (C ⥤ C))
    (h : ∀ n : ℕ, X.left.obj (op ⦋n⦌) = Y.iterate (n + 1)) (hX : X.right = 𝟭 C)
    (hδ : ∀ (n : ℕ) (j : Fin (n + 2)), X.left.δ j =
      eqToHom (h (n + 1)) ≫ Godement.face dd (n + 1) j ≫ eqToHom (h n).symm)
    (hσ : ∀ (n : ℕ) (j : Fin (n + 1)), X.left.σ j =
      eqToHom (h n) ≫ Godement.degeneracy ss n j ≫ eqToHom (h (n + 1)).symm)
    (hε : X.hom.app (op ⦋0⦌) = eqToHom (h 0) ≫ Godement.face dd 0 0 ≫ eqToHom hX.symm)
    (a : X.left ⋙ (Functor.whiskeringRight C C B).obj G ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj (X.right ⋙ G))
    (ha : ∀ n : SimplexCategoryᵒᵖ, a.app n = Functor.whiskerRight (X.hom.app n) G)
    (p : ∀ n : ℕ, G ⟶ Y.iterate (n + 1) ⋙ G)
    (hp₀ : p 0 ≫ Functor.whiskerRight (Godement.face dd 0 0) G = 𝟙 G)
    (hp : ∀ n : ℕ, p n ≫ Functor.whiskerRight (Godement.degeneracy ss n 0) G = p (n + 1)) :
    ∃ r : (Functor.const SimplexCategoryᵒᵖ).obj (X.right ⋙ G) ⟶
        X.left ⋙ (Functor.whiskeringRight C C B).obj G,
      (∀ n : ℕ, r.app (op ⦋n⦌) =
        eqToHom (congrArg (fun F => F ⋙ G) hX) ≫ p n ≫
          eqToHom (congrArg (fun F => F ⋙ G) (h n)).symm) ∧
      Relation.EqvGen (fun f g => Nonempty (SimplicialObject.Homotopy f g)) (a ≫ r) (𝟙 _) ∧
      Relation.EqvGen (fun f g => Nonempty (SimplicialObject.Homotopy f g)) (r ≫ a) (𝟙 _) := by
  obtain ⟨e₁, er₁, eδ₁, eσ₁, ehom₁⟩ := exists_map_pinning dd ss
    ((Functor.whiskeringRight C C B).obj G) X h hX hδ hσ hε a (ha (op ⦋0⦌))
  obtain ⟨r, hr0, hh₁, hh₂⟩ := key_whiskerRight dd ss G
    ⟨X.left ⋙ (Functor.whiskeringRight C C B).obj G, X.right ⋙ G, a⟩
    e₁ er₁ eδ₁ eσ₁ ehom₁ _ (conj_comp_eq_id (e₁ 0) er₁ ehom₁ hp₀)
  exact ⟨r, fun n => const_app_eq_of_degeneracy_step ss
    ((Functor.whiskeringRight C C B).obj G) r e₁ eσ₁ er₁ p hr0 hp n, hh₁, hh₂⟩

/-- Let `X` be an augmented simplicial object of `C ⥤ C` whose terms, faces, degeneracies and
augmentation are pinned to the powers of `Y`, `Godement.face dd`, `Godement.degeneracy ss` and
`d⁰₀`, and let `b = ε ⋆ 1_F : X ∘ F ⟶ F` be its augmentation whiskered on the inside by a functor
`F`. Let `p n : F ⟶ Y^{n+1} ∘ F` be a family with `(d⁰₀ ⋆ 1_F) ∘ p 0 = 1_F` and
`(sⁿ₀ ⋆ 1_F) ∘ p n = p (n + 1)`. Then `b` is a homotopy equivalence whose homotopy inverse is
`p n` in degree `n`: both composites with it are related to the identity by the equivalence
relation generated by the existence of a simplicial homotopy. -/
public theorem exists_homotopyInverse_whiskerLeft_eq
    {A : Type u₁} [Category.{v₁} A] {C : Type u} [Category.{v} C]
    {Y : C ⥤ C} (dd : Y ⟶ 𝟭 C) (ss : Y ⟶ Y ⋙ Y) (F : A ⥤ C)
    (X : SimplicialObject.Augmented (C ⥤ C))
    (h : ∀ n : ℕ, X.left.obj (op ⦋n⦌) = Y.iterate (n + 1)) (hX : X.right = 𝟭 C)
    (hδ : ∀ (n : ℕ) (j : Fin (n + 2)), X.left.δ j =
      eqToHom (h (n + 1)) ≫ Godement.face dd (n + 1) j ≫ eqToHom (h n).symm)
    (hσ : ∀ (n : ℕ) (j : Fin (n + 1)), X.left.σ j =
      eqToHom (h n) ≫ Godement.degeneracy ss n j ≫ eqToHom (h (n + 1)).symm)
    (hε : X.hom.app (op ⦋0⦌) = eqToHom (h 0) ≫ Godement.face dd 0 0 ≫ eqToHom hX.symm)
    (b : X.left ⋙ (Functor.whiskeringLeft A C C).obj F ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj (F ⋙ X.right))
    (hb : ∀ n : SimplexCategoryᵒᵖ, b.app n = Functor.whiskerLeft F (X.hom.app n))
    (p : ∀ n : ℕ, F ⟶ F ⋙ Y.iterate (n + 1))
    (hp₀ : p 0 ≫ Functor.whiskerLeft F (Godement.face dd 0 0) = 𝟙 F)
    (hp : ∀ n : ℕ, p n ≫ Functor.whiskerLeft F (Godement.degeneracy ss n 0) = p (n + 1)) :
    ∃ r : (Functor.const SimplexCategoryᵒᵖ).obj (F ⋙ X.right) ⟶
        X.left ⋙ (Functor.whiskeringLeft A C C).obj F,
      (∀ n : ℕ, r.app (op ⦋n⦌) =
        eqToHom (congrArg (fun T => F ⋙ T) hX) ≫ p n ≫
          eqToHom (congrArg (fun T => F ⋙ T) (h n)).symm) ∧
      Relation.EqvGen (fun f g => Nonempty (SimplicialObject.Homotopy f g)) (b ≫ r) (𝟙 _) ∧
      Relation.EqvGen (fun f g => Nonempty (SimplicialObject.Homotopy f g)) (r ≫ b) (𝟙 _) := by
  obtain ⟨e₂, er₂, eδ₂, eσ₂, ehom₂⟩ := exists_map_pinning dd ss
    ((Functor.whiskeringLeft A C C).obj F) X h hX hδ hσ hε b (hb (op ⦋0⦌))
  obtain ⟨r, hr0, hh₁, hh₂⟩ := key_whiskerLeft dd ss F
    ⟨X.left ⋙ (Functor.whiskeringLeft A C C).obj F, F ⋙ X.right, b⟩
    e₂ er₂ eδ₂ eσ₂ ehom₂ _ (conj_comp_eq_id (e₂ 0) er₂ ehom₂ hp₀)
  exact ⟨r, fun n => const_app_eq_of_degeneracy_step ss
    ((Functor.whiskeringLeft A C C).obj F) r e₂ eσ₂ er₂ p hr0 hp n, hh₁, hh₂⟩

end CategoryTheory.Godement

namespace AlgCat

/-- The analogue of Stacks 08NE for the free/forget adjunction of *not necessarily commutative*
`A`-algebras (`AlgCat`, whose free functor is `FreeAlgebra`, the non-commutative free algebra);
Stacks 08NE itself concerns commutative `A`-algebras and polynomial algebras `A[E]`, and is
`CommAlgCat.exists_homotopyInverse_whiskered_standardResolution`.
Let `A` be a ring, let `U : Sets → Alg_A` be the free associative algebra functor and `V` the
forgetful functor, and let `X` be the standard resolution of the comonad `Y = U ∘ V`: the augmented
simplicial object of `Fun(Alg_A, Alg_A)` with terms the iterates `Xₙ = Y^{n+1}`, so that
`Xₙ(B) = A[A[⋯[B]⋯]]` with `n + 1` brackets, faces `Godement.face`, degeneracies
`Godement.degeneracy`, point `𝟭` and augmentation `d⁰₀`. Then the whiskered augmentations
`1_V ⋆ ε : V ∘ X ⟶ V` and `ε ⋆ 1_U : X ∘ U ⟶ U` are homotopy equivalences with their homotopy
inverses displayed: in degree `n` the first is the map of sets `b ↦ [⋯[b]⋯]` (`n + 1` brackets)
and the second is the `A`-algebra map `∑ a [e₁]⋯[e_p] ↦ ∑ a [⋯[e₁]⋯]⋯[⋯[e_p]⋯]` sending a
variable `[e]` to `[⋯[e]⋯]` (`n + 2` brackets), and both composites of each with the augmentation
are homotopic to the identity, homotopic meaning related by the equivalence relation generated by
the existence of a simplicial homotopy. Evaluating the first clause at an `A`-algebra `B` gives
the homotopy equivalence of the underlying simplicial sets of `X(B) ⟶ B`, and the second at a set
`E` the homotopy equivalence of simplicial `A`-algebras `X(A⟨E⟩) ⟶ A⟨E⟩`, where `A⟨E⟩` is the free
non-commutative algebra. -/
public theorem exists_homotopyInverse_whiskered_standardResolution {A : Type u} [CommRing A]
    (X : SimplicialObject.Augmented (AlgCat.{u} A ⥤ AlgCat.{u} A))
    (h : ∀ n : ℕ, X.left.obj (op ⦋n⦌) =
      (AlgCat.adj A).toComonad.toFunctor.iterate (n + 1))
    (hX : X.right = 𝟭 (AlgCat.{u} A))
    (hδ : ∀ (n : ℕ) (j : Fin (n + 2)), X.left.δ j =
      eqToHom (h (n + 1)) ≫ Godement.face (AlgCat.adj A).toComonad.ε (n + 1) j ≫
        eqToHom (h n).symm)
    (hσ : ∀ (n : ℕ) (j : Fin (n + 1)), X.left.σ j =
      eqToHom (h n) ≫ Godement.degeneracy (AlgCat.adj A).toComonad.δ n j ≫
        eqToHom (h (n + 1)).symm)
    (hε : X.hom.app (op ⦋0⦌) =
      eqToHom (h 0) ≫ Godement.face (AlgCat.adj A).toComonad.ε 0 0 ≫ eqToHom hX.symm)
    (a : X.left ⋙ (Functor.whiskeringRight (AlgCat.{u} A) (AlgCat.{u} A) (Type u)).obj
        (forget (AlgCat.{u} A)) ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj (X.right ⋙ forget (AlgCat.{u} A)))
    (ha : ∀ n : SimplexCategoryᵒᵖ,
      a.app n = Functor.whiskerRight (X.hom.app n) (forget (AlgCat.{u} A)))
    (b : X.left ⋙ (Functor.whiskeringLeft (Type u) (AlgCat.{u} A) (AlgCat.{u} A)).obj
        (AlgCat.free A) ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj (AlgCat.free A ⋙ X.right))
    (hb : ∀ n : SimplexCategoryᵒᵖ,
      b.app n = Functor.whiskerLeft (AlgCat.free A) (X.hom.app n))
    (ρ : ∀ n : ℕ, forget (AlgCat.{u} A) ⟶
      (AlgCat.adj A).toComonad.toFunctor.iterate (n + 1) ⋙ forget (AlgCat.{u} A))
    (hρ₀ : ∀ (B : AlgCat.{u} A) (x : B), (ρ 0).app B x = comonadι B x)
    (hρ : ∀ (n : ℕ) (B : AlgCat.{u} A) (x : B),
      (ρ (n + 1)).app B x = comonadι _ ((ρ n).app B x))
    (τ : ∀ n : ℕ, AlgCat.free A ⟶
      AlgCat.free A ⋙ (AlgCat.adj A).toComonad.toFunctor.iterate (n + 1))
    (hτ₀ : ∀ (E : Type u) (e : E), ((τ 0).app E).hom (freeι E e) = comonadι _ (freeι E e))
    (hτ : ∀ (n : ℕ) (E : Type u) (e : E), ((τ (n + 1)).app E).hom (freeι E e) =
      comonadι _ (((τ n).app E).hom (freeι E e))) :
    (∃ r : (Functor.const SimplexCategoryᵒᵖ).obj (X.right ⋙ forget (AlgCat.{u} A)) ⟶
        X.left ⋙ (Functor.whiskeringRight (AlgCat.{u} A) (AlgCat.{u} A) (Type u)).obj
          (forget (AlgCat.{u} A)),
      (∀ n : ℕ, r.app (op ⦋n⦌) =
        eqToHom (congrArg (fun F => F ⋙ forget (AlgCat.{u} A)) hX) ≫ ρ n ≫
          eqToHom (congrArg (fun F => F ⋙ forget (AlgCat.{u} A)) (h n)).symm) ∧
      Relation.EqvGen (fun f g => Nonempty (SimplicialObject.Homotopy f g)) (a ≫ r) (𝟙 _) ∧
      Relation.EqvGen (fun f g => Nonempty (SimplicialObject.Homotopy f g)) (r ≫ a) (𝟙 _)) ∧
    (∃ r : (Functor.const SimplexCategoryᵒᵖ).obj (AlgCat.free A ⋙ X.right) ⟶
        X.left ⋙ (Functor.whiskeringLeft (Type u) (AlgCat.{u} A) (AlgCat.{u} A)).obj
          (AlgCat.free A),
      (∀ n : ℕ, r.app (op ⦋n⦌) =
        eqToHom (congrArg (fun F => AlgCat.free A ⋙ F) hX) ≫ τ n ≫
          eqToHom (congrArg (fun F => AlgCat.free A ⋙ F) (h n)).symm) ∧
      Relation.EqvGen (fun f g => Nonempty (SimplicialObject.Homotopy f g)) (b ≫ r) (𝟙 _) ∧
      Relation.EqvGen (fun f g => Nonempty (SimplicialObject.Homotopy f g)) (r ≫ b) (𝟙 _)) := by
  constructor
  · obtain ⟨e₁, er₁, eδ₁, eσ₁, ehom₁⟩ := exists_map_pinning (AlgCat.adj A).toComonad.ε
      (AlgCat.adj A).toComonad.δ
      ((Functor.whiskeringRight (AlgCat.{u} A) (AlgCat.{u} A) (Type u)).obj
        (forget (AlgCat.{u} A))) X h hX hδ hσ hε a (ha (op ⦋0⦌))
    obtain ⟨r, hr0, hh₁, hh₂⟩ := key_whiskerRight (AlgCat.adj A).toComonad.ε
      (AlgCat.adj A).toComonad.δ (forget (AlgCat.{u} A))
      ⟨X.left ⋙ (Functor.whiskeringRight (AlgCat.{u} A) (AlgCat.{u} A) (Type u)).obj
          (forget (AlgCat.{u} A)), X.right ⋙ forget (AlgCat.{u} A), a⟩
      e₁ er₁ eδ₁ eσ₁ ehom₁ _
      (conj_comp_eq_id (e₁ 0) er₁ ehom₁ (iteratedι_comp_face_zero ρ hρ₀))
    exact ⟨r, fun n => const_app_eq_of_degeneracy_step (AlgCat.adj A).toComonad.δ
      ((Functor.whiskeringRight (AlgCat.{u} A) (AlgCat.{u} A) (Type u)).obj
        (forget (AlgCat.{u} A))) r e₁ eσ₁ er₁ ρ hr0
        (iteratedι_comp_degeneracy_zero ρ hρ₀ hρ) n, hh₁, hh₂⟩
  · obtain ⟨e₂, er₂, eδ₂, eσ₂, ehom₂⟩ := exists_map_pinning (AlgCat.adj A).toComonad.ε
      (AlgCat.adj A).toComonad.δ
      ((Functor.whiskeringLeft (Type u) (AlgCat.{u} A) (AlgCat.{u} A)).obj (AlgCat.free A))
      X h hX hδ hσ hε b (hb (op ⦋0⦌))
    obtain ⟨r, hr0, hh₁, hh₂⟩ := key_whiskerLeft (AlgCat.adj A).toComonad.ε
      (AlgCat.adj A).toComonad.δ (AlgCat.free A)
      ⟨X.left ⋙ (Functor.whiskeringLeft (Type u) (AlgCat.{u} A) (AlgCat.{u} A)).obj
          (AlgCat.free A), AlgCat.free A ⋙ X.right, b⟩
      e₂ er₂ eδ₂ eσ₂ ehom₂ _
      (conj_comp_eq_id (e₂ 0) er₂ ehom₂ (freeIteratedι_comp_face_zero τ hτ₀))
    exact ⟨r, fun n => const_app_eq_of_degeneracy_step (AlgCat.adj A).toComonad.δ
      ((Functor.whiskeringLeft (Type u) (AlgCat.{u} A) (AlgCat.{u} A)).obj (AlgCat.free A))
      r e₂ eσ₂ er₂ τ hr0 (freeIteratedι_comp_degeneracy_zero τ hτ₀ hτ) n, hh₁, hh₂⟩

end AlgCat

/-! ### Homotopy equivalence versus quasi-isomorphism -/

section QuasiIso

open MonoidalCategory SSet MorphismProperty CartesianMonoidalCategory AlgebraicTopology

/-! #### A trivial Kan fibration is a homotopy equivalence -/

/-- A trivial Kan fibration of simplicial sets is a homotopy equivalence. -/
private lemma homotopyEquivalences_of_trivialKanFibrations {X Y : SSet.{v}} (f : X ⟶ Y)
    (hf : SSet.trivialKanFibrations f) :
    SimplicialObject.homotopyEquivalences (Type v) f := by
  obtain ⟨g, ⟨H₁⟩, ⟨H₂⟩⟩ := SSet.trivialKanFibrations_isHomotopyEquiv f hf
  exact ⟨g, Relation.EqvGen.rel _ _ ⟨H₁.toSimplicialObjectHomotopy⟩,
    Relation.EqvGen.rel _ _ ⟨H₂.toSimplicialObjectHomotopy⟩⟩

/-! #### From simplicial modules to simplicial abelian groups -/

/-- The functor `forget₂ (ModuleCat R) AddCommGrpCat` detects quasi-isomorphisms of the
associated chain complexes. -/
private lemma quasiIso_map_whiskerRight_forget₂_iff {R : Type u} [Ring R]
    {X Y : SimplicialObject (ModuleCat.{v} R)} (f : X ⟶ Y) :
    QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{v}).map
        (Functor.whiskerRight f (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}))) ↔
      QuasiIso ((alternatingFaceMapComplex (ModuleCat.{v} R)).map f) := by
  have e := alternatingFaceMapComplexCompMapHomologicalComplexIso (C := ModuleCat.{v} R)
    (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v})
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    ((alternatingFaceMapComplex (ModuleCat.{v} R)).map f)
    (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v})]
  exact quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (e.app X).symm (e.app Y).symm (e.inv.naturality f).symm)

end QuasiIso

namespace AlgebraicTopology

/-- **Stacks 0G5T**.
Let `R` be a ring and let `f : X ⟶ Y` be a morphism of simplicial `R`-modules which is surjective
in each degree. Then the underlying morphism of simplicial sets `X ⋙ forget ⟶ Y ⋙ forget` is a
homotopy equivalence — it admits a morphism of simplicial sets back whose two composites with it
are homotopic to the identities — if and only if the induced morphism `s(X) ⟶ s(Y)` of associated
chain complexes of `R`-modules is a quasi-isomorphism. Applied to the augmentation `X(M) ⟶ M` of
the standard resolution of an `R`-module `M` by free modules, whose underlying augmentation of
simplicial sets is a homotopy equivalence, this says that `M` is the only nonzero homology group of
the complex associated to `X(M)`. -/
@[stacks 0G5T]
public theorem homotopyEquivalences_forget_iff_quasiIso_of_surjective {R : Type u} [Ring R]
    {X Y : SimplicialObject (ModuleCat.{v} R)} (f : X ⟶ Y)
    (hf : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (f.app n).hom) :
    SimplicialObject.homotopyEquivalences (Type v)
        (Functor.whiskerRight f (forget (ModuleCat.{v} R))) ↔
      QuasiIso ((alternatingFaceMapComplex (ModuleCat.{v} R)).map f) := by
  rw [← quasiIso_map_whiskerRight_forget₂_iff]
  exact ⟨fun h => quasiIso_alternatingFaceMapComplex_map_of_homotopyEquivalences_forget _ h,
    fun h => homotopyEquivalences_of_trivialKanFibrations _
      (SimplicialObject.trivialKanFibrations_whiskerRight_forget_of_surjective_of_quasiIso
        (Functor.whiskerRight f (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v})) hf)⟩

/-- **Stacks 08NA**.
Let `A` be a ring and let `f : X ⟶ Y` be a morphism of simplicial `A`-algebras which is surjective
in each degree. Then the underlying morphism of simplicial sets is a homotopy equivalence if and
only if the induced morphism `s(X) ⟶ s(Y)` of the chain complexes associated to the underlying
simplicial `A`-modules is a quasi-isomorphism. Applied to the augmentation `X(B) ⟶ B` of the
standard resolution of a commutative `A`-algebra `B` by the polynomial algebras `A[A[⋯[B]⋯]]`,
whose underlying augmentation of simplicial sets is a homotopy equivalence, this says that `B` is
the only nonzero homology group of the complex of `A`-modules associated to `X(B)`. -/
@[stacks 08NA]
public theorem homotopyEquivalences_forget_iff_quasiIso_forget₂_of_surjective {A : Type u}
    [CommRing A] {X Y : SimplicialObject (AlgCat.{v} A)} (f : X ⟶ Y)
    (hf : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (f.app n).hom) :
    SimplicialObject.homotopyEquivalences (Type v)
        (Functor.whiskerRight f (forget (AlgCat.{v} A))) ↔
      QuasiIso ((alternatingFaceMapComplex (ModuleCat.{v} A)).map
        (Functor.whiskerRight f (forget₂ (AlgCat.{v} A) (ModuleCat.{v} A)))) :=
  homotopyEquivalences_forget_iff_quasiIso_of_surjective
    (Functor.whiskerRight f (forget₂ (AlgCat.{v} A) (ModuleCat.{v} A))) hf

end AlgebraicTopology

/-! ### The standard resolution of a module by free modules -/

section FreeModules

open ModuleCat

/-- The basis element `[n]` of `Y(N) = R[N]`, the free `R`-module on the underlying set of `N`,
where `Y` is the comonad of the free/forget adjunction. -/
public noncomputable def ModuleCat.comonadMk {R : Type u} [Ring R] {N : ModuleCat.{u} R} (n : N) :
    ((adj R).toComonad.obj N : Type u) :=
  freeMk n

/-- The sum `∑ᵢ f nᵢ rᵢ` attached to an element `ξ = ∑ᵢ rᵢ[nᵢ]` of `Y(N) = R[N]`, the free
`R`-module on the underlying set of `N`, and a function `f : N → R → M`. -/
public def ModuleCat.comonadSum {R : Type u} [Ring R] {N : ModuleCat.{u} R} {M : Type*}
    [AddCommMonoid M] (ξ : ((adj R).toComonad.obj N : Type u)) (f : N → R → M) : M :=
  Finsupp.sum ξ f

/-- The free comonad on a general element, against a pointwise description `g` of the morphism
it is applied to: `Y(f) (∑ᵢ rᵢ[nᵢ]) = ∑ᵢ rᵢ[g nᵢ]` whenever `f n = g n` for all `n`. -/
private lemma toComonad_map_apply {R : Type u} [Ring R] {N N' : ModuleCat.{u} R} (f : N ⟶ N')
    {g : N → N'} (hg : ∀ n, f n = g n) (ξ : ((adj R).toComonad.obj N : Type u)) :
    (adj R).toComonad.map f ξ = comonadSum ξ (fun n r => r • comonadMk (g n)) :=
  Finsupp.sum_congr fun n _ =>
    (congrArg (Finsupp.single · _) (hg n)).trans (Finsupp.smul_single_one _ _).symm

/-- The counit of the free comonad evaluates a formal sum: `∑ᵢ rᵢ[nᵢ] ↦ ∑ᵢ rᵢnᵢ`. -/
private lemma toComonad_ε_app_apply {R : Type u} [Ring R] (N : ModuleCat.{u} R)
    (ξ : ((adj R).toComonad.obj N : Type u)) :
    (adj R).toComonad.ε.app N ξ = comonadSum ξ (fun n r => r • n) := rfl

/-- The comultiplication of the free comonad doubles the bracket: `∑ᵢ rᵢ[nᵢ] ↦ ∑ᵢ rᵢ[[nᵢ]]`. -/
private lemma toComonad_δ_app_apply {R : Type u} [Ring R] (N : ModuleCat.{u} R)
    (ξ : ((adj R).toComonad.obj N : Type u)) :
    (adj R).toComonad.δ.app N ξ = comonadSum ξ (fun n r => r • comonadMk (comonadMk n)) :=
  Finsupp.sum_congr fun _ _ => (Finsupp.smul_single_one _ _).symm

end FreeModules

namespace ModuleCat

/-- **Stacks 0G5U**.
Let `R` be a ring, `M` an `R`-module and `R[N]` the free `R`-module on the underlying set of an
`R`-module `N`, with `[n] = ModuleCat.comonadMk n` and `∑ᵢ f nᵢ rᵢ = ModuleCat.comonadSum ξ f` for
`ξ = ∑ᵢ rᵢ[nᵢ]`. For the simplicial `R`-module `X(M)` with `X₁(M) = R[R[M]]` and
`X₂(M) = R[R[R[M]]]`, and a typical element `ξ = ∑ᵢ rᵢ[∑ⱼ r_ij[m_ij]]` of `X₁(M)`, the two faces
`d₀, d₁ : R[R[M]] → R[M]` — the counit of the free-forgetful adjunction contracting the outer,
resp. the inner, bracket — are given by `d₀(ξ) = ∑_{i,j} rᵢr_ij[m_ij]` and
`d₁(ξ) = ∑ᵢ rᵢ[∑ⱼ r_ij m_ij]`, and the two degeneracies `s₀, s₁ : R[R[M]] → R[R[R[M]]]` — its
comultiplication doubling the outer, resp. the inner, bracket — by `s₀(ξ) = ∑ᵢ rᵢ[[∑ⱼ r_ij[m_ij]]]`
and `s₁(ξ) = ∑ᵢ rᵢ[∑ⱼ r_ij[[m_ij]]]`. -/
@[stacks 0G5U]
public theorem free_standardResolution_face_degeneracy_apply {R : Type u} [Ring R]
    (M : ModuleCat.{u} R)
    (ξ : ((adj R).toComonad.obj ((adj R).toComonad.obj M) : Type u)) :
    (adj R).toComonad.ε.app ((adj R).toComonad.obj M) ξ = comonadSum ξ (fun x r => r • x) ∧
      (adj R).toComonad.map ((adj R).toComonad.ε.app M) ξ =
        comonadSum ξ (fun x r => r • comonadMk (comonadSum x (fun m c => c • m))) ∧
      (adj R).toComonad.δ.app ((adj R).toComonad.obj M) ξ =
        comonadSum ξ (fun x r => r • comonadMk (comonadMk x)) ∧
      (adj R).toComonad.map ((adj R).toComonad.δ.app M) ξ =
        comonadSum ξ (fun x r =>
          r • comonadMk (comonadSum x (fun m c => c • comonadMk (comonadMk m)))) :=
  ⟨toComonad_ε_app_apply _ ξ,
    toComonad_map_apply _ (toComonad_ε_app_apply M) ξ,
    toComonad_δ_app_apply _ ξ,
    toComonad_map_apply _ (toComonad_δ_app_apply M) ξ⟩

end ModuleCat

end
