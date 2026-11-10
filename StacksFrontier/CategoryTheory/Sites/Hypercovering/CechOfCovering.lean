module

public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Cech
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Coskeletal
public import StacksFrontier.CategoryTheory.Sites.CoveringPermanence
import StacksFrontier.CategoryTheory.Sites.Hypercovering.MorphismPropertySelfProduct

/-!
# The Čech hypercovering of a covering morphism

Let `C` be a site with fibre products given by a pretopology `J`. A covering morphism `U ⟶ X`,
that is one whose one-member family is a covering family of `X`, gives a simplicial
semi-representable object over `X` whose term in degree `n` is the `(n + 1)`-fold fibre product of
`U` over `X`. This file proves that this object is a hypercovering of `X`.

## Main results

* `isHypercovering_cech`: the Čech object of a one-member covering family is a hypercovering.
* `powerUniqueIso`, with `powerUniqueIso_hom` and `isIso_powerπ`: the `α`-fold power of a formal
  coproduct for a one-element index type `α` is that formal coproduct, the isomorphism being the
  projection `FormalCoproduct.powerπ`.
* `cech_isCoskeletal`: the Čech object of any formal coproduct of objects over `X` is
  `0`-coskeletal, which is what makes all of its matching morphisms isomorphisms.

## Implementation notes

The source's `SR(C, X)` is `FormalCoproduct (Over X)`. The simplicial object is Mathlib's
`FormalCoproduct.cech` applied to the one-summand formal coproduct
`(FormalCoproduct.incl (Over X)).obj (Over.mk f)`. Its degree-`n` term is, by the definition of
`cech`, the `power (Fin (n + 1))` of that one-summand object, whose sole component is the
`(n + 1)`-fold fibre product over `X`; `FormalCoproduct.cech_obj` records this.

Both clauses of `IsHypercovering` reduce to statements about one-member families, because every
object occurring has a one-element index type. The degree-zero clause is the hypothesis `hf`
transported along the canonical isomorphisms identifying the degree-zero term with `U` and the
terminal object of `SR(C, X)` with `{X → X}`; the matching clauses hold because the Čech object is
`0`-coskeletal, so every matching morphism is an isomorphism.

## References

* [Stacks Project, Tag 0GMA](https://stacks.math.columbia.edu/tag/0GMA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe w v u

namespace Stacks.CategoryTheory.Hypercovering

add_to_stacks 0GMA "the Čech simplicial construction" FormalCoproduct.cech
add_to_stacks 0GMA "the terms" FormalCoproduct.cech_obj

section Truncated

private alias trunc0_eq := CategoryTheory.SimplicialObject.Augmented.truncZero_eq

private instance : Subsingleton (SimplexCategory.Truncated 0) := ⟨trunc0_eq⟩

/-- The unique object of the zero-truncated simplex category. -/
private def zeroObj : SimplexCategory.Truncated 0 := ⟨SimplexCategory.mk 0, by simp⟩

private instance (x y : SimplexCategory.Truncated 0) : Subsingleton (x.1 ⟶ y.1) := ⟨by
  intro f g
  apply SimplexCategory.Hom.ext
  ext k
  have hy : y.1.len = 0 := by have := y.2; omega
  have hf := (f.toOrderHom k).isLt
  have hg := (g.toOrderHom k).isLt
  omega⟩

private instance (x y : SimplexCategory.Truncated 0) : Subsingleton (x ⟶ y) :=
  ⟨fun _ _ ↦ ObjectProperty.hom_ext _ (Subsingleton.elim _ _)⟩

end Truncated

section Power

variable {D : Type u} [Category.{v} D]

/-- The `α`-fold power of a formal coproduct, for a one-element index type `α`, is the formal
coproduct itself: its index type `α → A.I` is `A.I`, and its component at `i` is a product of
one copy of `A.obj (i default)`. -/
noncomputable def powerUniqueIso (A : FormalCoproduct.{w} D) (α : Type) [Unique α]
    [HasProductsOfShape α D] : A.power α ≅ A :=
  FormalCoproduct.isoOfComponents (Equiv.funUnique α A.I) fun i ↦ productUniqueIso (A.obj ∘ i)

/-- The isomorphism `powerUniqueIso` is the projection `FormalCoproduct.powerπ` of the unique
index. -/
theorem powerUniqueIso_hom (A : FormalCoproduct.{w} D) (α : Type) [Unique α]
    [HasProductsOfShape α D] :
    (powerUniqueIso A α).hom = A.powerπ (default : α) := by
  apply FormalCoproduct.hom_ext rfl
  intro i
  simp [powerUniqueIso]

/-- The projection of the `α`-fold power of a formal coproduct onto the unique index of a
one-element index type `α` is an isomorphism. -/
instance isIso_powerπ (A : FormalCoproduct.{w} D) (α : Type) [Unique α]
    [HasProductsOfShape α D] (a : α) : IsIso (A.powerπ a) := by
  obtain rfl : a = default := Subsingleton.elim _ _
  rw [← powerUniqueIso_hom A α]
  infer_instance

end Power

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

section Singleton

/-- A natural transformation whose postcomposition is bijective on morphisms out of every functor
exhibits its source as a right Kan extension. -/
private lemma isRightKanExtension_of_bijective {A B D : Type*}
    [Category A] [Category B] [Category D] (L : A ⥤ B) (F : A ⥤ D)
    (F' : B ⥤ D) (α : L ⋙ F' ⟶ F)
    (hα : ∀ G : B ⥤ D,
      Function.Bijective (fun φ : G ⟶ F' ↦ Functor.whiskerLeft L φ ≫ α)) :
    F'.IsRightKanExtension α where
  nonempty_isUniversal := ⟨IsTerminal.ofUniqueHom
    (fun E ↦ CostructuredArrow.homMk ((Equiv.ofBijective _ (hα E.left)).symm E.hom)
      ((Equiv.ofBijective _ (hα E.left)).apply_symm_apply E.hom))
    fun E φ ↦ CostructuredArrow.hom_ext _ _ <| (hα E.left).injective <|
      (CostructuredArrow.w φ).trans
        ((Equiv.ofBijective _ (hα E.left)).apply_symm_apply E.hom).symm⟩

/-- The Čech object of a formal coproduct of objects over `X` is `0`-coskeletal: a morphism into
it is the same datum as a morphism of its degree-zero term, because its degree-`n` term is the
`(n + 1)`-fold power of the formal coproduct. -/
theorem cech_isCoskeletal {X : C}
    (A : FormalCoproduct.{w} (Over X))
    [HasFiniteProducts (Over X)] :
    A.cech.IsCoskeletal 0 := by
  let : HasFiniteLimits (FormalCoproduct.{w} (Over X)) :=
    hasFiniteLimits_of_hasTerminal_and_pullbacks
  let K := A.cech
  let π : ∀ n : ℕ, Fin (n + 1) → (K.obj (op ⦋n⦌) ⟶ A) :=
    fun _ i ↦ A.powerπ i
  have hU : ∀ n : ℕ, IsLimit (Fan.mk (K.obj (op ⦋n⦌)) (π n)) := by
    intro n
    simpa [K, π, FormalCoproduct.cech, FormalCoproduct.powerFan] using
      (A.isLimitPowerFan (Fin (n + 1)))
  have hπ : ∀ {n m : ℕ} (φ : ⦋n⦌ ⟶ ⦋m⦌) (i : Fin (n + 1)),
      K.map φ.op ≫ π n i = π m (φ.toOrderHom i) := by
    intro n m φ i
    dsimp [π, K]
    simp
  have hbij (V : SimplicialObject (FormalCoproduct.{w} (Over X))) :
      Function.Bijective (fun g : V ⟶ K ↦ g.app (op ⦋0⦌) ≫ π 0 0) :=
    SimplicialObject.bijective_app_zero_comp_π π hU hπ V
  change K.IsCoskeletal 0
  rw [SimplicialObject.isCoskeletal_iff]
  let L := (SimplexCategory.Truncated.inclusion 0).op
  let α : L ⋙ K ⟶ L ⋙ K := 𝟙 _
  have : IsIso (π 0 0) := by
    dsimp [π]
    exact isIso_powerπ A (Fin 1) 0
  have hα (V : SimplicialObject (FormalCoproduct.{w} (Over X))) :
      Function.Bijective (fun g : V ⟶ K ↦ Functor.whiskerLeft L g ≫ α) := by
    constructor
    · intro g h hEq
      apply (hbij V).injective
      have h0 := congrArg (fun η ↦ η.app (op zeroObj)) hEq
      simpa [L, α, zeroObj] using congrArg (fun q ↦ q ≫ π 0 0) h0
    · intro η
      obtain ⟨g, hg⟩ := (hbij V).surjective (η.app (op zeroObj) ≫ π 0 0)
      have hg0 : g.app (op ⦋0⦌) = η.app (op zeroObj) := (cancel_mono (π 0 0)).1 hg
      refine ⟨g, ?_⟩
      apply NatTrans.ext
      funext z
      have hz : z = op zeroObj := Subsingleton.elim _ _
      subst z
      simpa [L, α, zeroObj] using hg0
  exact isRightKanExtension_of_bijective L (L ⋙ K) K α hα

/-- Composing two one-member covering families gives a one-member covering family. -/
private lemma singleton_comp_mem (J : Pretopology C) {A B X : C}
    (f : A ⟶ B) (e : B ⟶ X)
    (hf : Presieve.singleton f ∈ J.coverings B)
    (he : Presieve.singleton e ∈ J.coverings X) :
    Presieve.singleton (f ≫ e) ∈ J.coverings X := by
  let T : ∀ ⦃Y : C⦄ ⦃g : Y ⟶ X⦄, Presieve.singleton e g → Presieve Y :=
    fun {_} _ h ↦ by
      cases h
      exact Presieve.singleton f
  have ht : ∀ ⦃Y : C⦄ (g : Y ⟶ X) (h : Presieve.singleton e g), T h ∈ J.coverings Y := by
    intro Y g h
    cases h
    exact hf
  have hbind : Presieve.bind (Presieve.singleton e) T = Presieve.singleton (f ≫ e) := by
    funext Y g
    apply propext
    constructor
    · rintro ⟨Z, a, b, hb, ha, rfl⟩
      cases hb
      cases ha
      exact Presieve.singleton.mk
    · intro h
      cases h
      exact ⟨B, f, e, Presieve.singleton.mk, Presieve.singleton.mk, rfl⟩
  rw [← hbind]
  exact J.transitive (Presieve.singleton e) T he ht

end Singleton

/-- **Stacks Project, Tag 0GMA.** The Čech object of a covering morphism is a hypercovering of
its target. -/
@[stacks 0GMA "the hypercovering property"]
theorem isHypercovering_cech (J : Pretopology C) {U X : C} (f : U ⟶ X)
    (hf : Presieve.singleton f ∈ J.coverings X) :
    let : HasTerminal (Over X) := Over.over_hasTerminal X
    let : HasBinaryProducts (Over X) :=
      Over.ConstructProducts.over_binaryProduct_of_pullback
    let : HasFiniteProducts (Over X) := hasFiniteProducts_of_has_binary_and_terminal
    IsHypercovering J ((FormalCoproduct.incl (Over X)).obj (Over.mk f)).cech := by
  let : HasTerminal (Over X) := Over.over_hasTerminal X
  let : HasBinaryProducts (Over X) :=
    Over.ConstructProducts.over_binaryProduct_of_pullback
  let : HasFiniteProducts (Over X) := hasFiniteProducts_of_has_binary_and_terminal
  let A := (FormalCoproduct.incl (Over X)).obj (Over.mk f)
  let K := A.cech
  change
    IsCoveringOver J (terminal.from (K.obj (op ⦋0⦌))) ∧
      ∀ n : ℕ, IsCoveringOver J
        (((SimplicialObject.coskAdj n).unit.app K).app (op ⦋n + 1⦌))
  constructor
  · let q₀ : K.obj (op ⦋0⦌) ≅ A := powerUniqueIso A (Fin 1)
    let : ∀ Y : Over X, Unique ((FormalCoproduct.incl (Over X)).obj Y).I := fun _ ↦ by
      dsimp [FormalCoproduct.incl]
      infer_instance
    let T : FormalCoproduct (Over X) := { I := A.I, obj := fun _ ↦ Over.mk (𝟙 X) }
    let q : A ⟶ T :=
      { f := id
        φ := fun _ ↦ Over.homMk f (by simp [A, T, FormalCoproduct.incl]) }
    let e : (FormalCoproduct.incl (Over X)).obj (Over.mk (𝟙 X)) ≅ T :=
      FormalCoproduct.isoOfComponents
        (Equiv.ofBijective (fun _ : PUnit ↦ (default : A.I))
          ⟨by intro x y _; exact Subsingleton.elim _ _,
            by intro i; exact ⟨PUnit.unit, Subsingleton.elim _ _⟩⟩)
        (fun _ ↦ Iso.refl (Over.mk (𝟙 X)))
    let hT : IsTerminal T :=
      IsTerminal.ofIso (FormalCoproduct.isTerminalIncl _ Over.mkIdTerminal) e
    let eT := hT.uniqueUpToIso terminalIsTerminal
    let : Unique (K.obj (op ⦋0⦌)).I := by
      change Unique (ToType (SimplexCategory.mk 0) → A.I)
      infer_instance
    have hq : Presieve.singleton ((q.φ default).left) ∈ J X := hf
    have hiso : ∀ {P Q : FormalCoproduct (Over X)} (e : P ≅ Q) (i : P.I), IsIso (e.hom.φ i).left :=
      fun e i ↦ inferInstanceAs (IsIso ((Over.forget X).map (e.hom.φ i)))
    have := hiso q₀ default
    have hcomp : Presieve.singleton
        ((q₀.hom.φ default).left ≫ (q.φ default).left) ∈
        J (T.obj default).left := singleton_comp_mem J _ _ (J.has_isos _) hq
    have := hiso eT ((q₀.hom ≫ q).f default)
    let : Unique (⊤_ FormalCoproduct (Over X)).I := by
      refine ⟨⟨eT.hom.f default⟩, ?_⟩
      intro i
      calc
        i = eT.hom.f (eT.inv.f i) :=
          (congrArg (fun g : (⊤_ FormalCoproduct (Over X)) ⟶ _ ↦ g.f i) eT.inv_hom_id).symm
        _ = eT.hom.f default := congrArg eT.hom.f (Subsingleton.elim _ _)
    have hfinal : Presieve.singleton
        (((q₀.hom ≫ q).φ default).left ≫
          (eT.hom.φ ((q₀.hom ≫ q).f default)).left) ∈
        J ((⊤_ FormalCoproduct (Over X)).obj
          (eT.hom.f ((q₀.hom ≫ q).f default))).left := by
      convert singleton_comp_mem J
        (((q₀.hom ≫ q).φ default).left)
        (eT.hom.φ ((q₀.hom ≫ q).f default)).left hcomp (J.has_isos _) using 1
    have hfinalCover : IsCoveringOver J (q₀.hom ≫ q ≫ eT.hom) := by
      apply (isCoveringOver_unique_iff_singleton J (q₀.hom ≫ q ≫ eT.hom) default).2
      have hj : eT.hom.f ((q₀.hom ≫ q).f default) = default := Subsingleton.elim _ _
      have hfinal' := singleton_comp_mem J
        (((q₀.hom ≫ q).φ default).left ≫
          (eT.hom.φ ((q₀.hom ≫ q).f default)).left)
        (eqToHom (congrArg (fun i ↦ ((⊤_ FormalCoproduct (Over X)).obj i).left) hj))
        hfinal (J.has_isos _)
      simpa [FormalCoproduct.category, q] using hfinal'
    rwa [terminal.hom_ext (terminal.from _) (q₀.hom ≫ q ≫ eT.hom)]
  · intro n
    have hzero : IsIso ((SimplicialObject.coskAdj 0).unit.app K) :=
      (SimplicialObject.isCoskeletal_iff_isIso K 0).mp (cech_isCoskeletal A)
    have : IsIso ((SimplicialObject.coskAdj n).unit.app K) :=
      (SimplicialObject.nonempty_truncCoskAdj_and_isIso_coskAdj_unit_app
        (Nat.zero_le n)).2.2 K hzero
    exact IsCoveringOver.of_isIso J _

end Stacks.CategoryTheory.Hypercovering

end
