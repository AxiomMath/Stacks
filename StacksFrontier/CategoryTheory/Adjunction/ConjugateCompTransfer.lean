module

public import StacksFrontier.CategoryTheory.Adjunction.ConjugateOfNatIsoLeft

/-!
# Two systems of adjunctions with the same left adjoints, and their composition comparisons

Let `L₁ : C₀ ⥤ C₁` and `L₂ : C₁ ⥤ C₂` be two composable functors and let `L : C₀ ⥤ C₂` be a
third one together with an isomorphism `ι : L₁ ⋙ L₂ ≅ L`.  Suppose each of the three has *two*
right adjoints — `P₁, Q₁` for `L₁`, `P₂, Q₂` for `L₂` and `P, Q` for `L` — and suppose each of
the two systems has a composition comparison of its right adjoints, `cP : P₂ ⋙ P₁ ≅ P` and
`cQ : Q₂ ⋙ Q₁ ≅ Q`.

The two systems are compared by uniqueness of a right adjoint:
`CategoryTheory.Adjunction.rightAdjointUniq` gives `P₁ ≅ Q₁`, `P₂ ≅ Q₂` and `P ≅ Q`.  This file
proves that **the adjunction of the `Q`-system at `L` is the composite of its two factors read
through `cQ` if and only if the square of those three comparisons against `cP` and `cQ`
commutes**, provided the same is true of the `P`-system.

The point of the equivalence is that it holds in *both* directions, so it tells a consumer two
things at once.  Read forwards it transfers a composition law: if the square commutes, the
`Q`-system composes as the `P`-system does.  Read backwards it says that the square is not an
independent statement — it is the composition law itself, rewritten.  A development that owns a
concrete composition law for one system and wants it for another must therefore identify the
comparisons of right adjoints by some means *other* than uniqueness of a right adjoint; using
`CategoryTheory.Adjunction.rightAdjointUniq` for them reduces the square to the very law it was
meant to supply.

## Main results

* `Stacks.CategoryTheory.conjugateEquiv_ofNatIsoRight_hom`,
  `Stacks.CategoryTheory.conjugateEquiv_ofNatIsoRight_right` and
  `Stacks.CategoryTheory.conjugateEquiv_ofNatIsoRight_left`: the three missing entries of the
  conjugate calculus for `CategoryTheory.Adjunction.ofNatIsoRight`, companions of the
  `ofNatIsoLeft` ones in
  `StacksFrontier/CategoryTheory/Adjunction/ConjugateOfNatIsoLeft.lean`.
* `Stacks.CategoryTheory.conjugateEquiv_comp_id`: the conjugate of the identity of a composite
  left adjoint is the horizontal composite of the two conjugates of identities.
* `Stacks.CategoryTheory.eq_of_conjugateEquiv_id_eq`: two adjunctions with the same left and the
  same right adjoint are equal as soon as their conjugates against a third adjunction agree —
  the conjugate against a fixed adjunction determines the unit.
* `Stacks.CategoryTheory.conjugateEquiv_id_transport`: the conjugate of the identity of `L`
  between the two transported composite adjunctions, computed.
* `Stacks.CategoryTheory.eq_comp_ofNatIsoRight_ofNatIsoLeft_iff`: **the equivalence**.

## Implementation notes

Everything is the conjugate calculus — `CategoryTheory.conjugateEquiv_comp`,
`CategoryTheory.conjugateEquiv_whiskerLeft`, `CategoryTheory.conjugateEquiv_whiskerRight` and
the transport lemmas — together with the one observation that makes the equivalence an
equivalence rather than an implication: for a fixed `a : L ⊣ P`, the assignment
`b ↦ CategoryTheory.conjugateEquiv a b (𝟙 L)` is injective on adjunctions `L ⊣ Q`, because
`CategoryTheory.unit_conjugateEquiv` recovers the unit of `b` from it.

No composition comparison is assumed to be canonical in any sense: `cP` and `cQ` are arbitrary
isomorphisms, and the hypothesis on the `P`-system is an equation between adjunctions, not a
property of `cP`.
-/

@[expose] public section

open CategoryTheory

universe v₀ v₁ v₂ u₀ u₁ u₂

namespace Stacks.CategoryTheory

variable {C₀ : Type u₀} {C₁ : Type u₁} {C₂ : Type u₂}
  [Category.{v₀} C₀] [Category.{v₁} C₁] [Category.{v₂} C₂]

/-! ### The conjugate calculus for a change of the right adjoint -/

section OfNatIsoRight

variable {L L' : C₀ ⥤ C₁} {R R' : C₁ ⥤ C₀} {T T' : C₁ ⥤ C₀}

/-- **Changing the right adjoint of an adjunction along an isomorphism `e : R ≅ R'` has `e.hom`
as the conjugate of the identity of the left adjoint**, the original adjunction being taken
first.  This is the companion of `Stacks.CategoryTheory.conjugateEquiv_ofNatIsoRight_id`, where
the transported adjunction is taken first and the conjugate is `e.inv`. -/
theorem conjugateEquiv_ofNatIsoRight_hom (adj : L ⊣ R) (e : R ≅ R') :
    conjugateEquiv adj (adj.ofNatIsoRight e) (𝟙 L) = e.hom := by
  have h := conjugateEquiv_comm adj (adj.ofNatIsoRight e) (α := 𝟙 L) (β := 𝟙 L)
    (Category.comp_id _)
  rw [conjugateEquiv_ofNatIsoRight_id] at h
  exact ((Iso.comp_inv_eq e).mp h).trans (Category.id_comp _)

/-- Changing the right adjoint of the *second* adjunction of a conjugate composes the conjugate
with `e.hom`. -/
theorem conjugateEquiv_ofNatIsoRight_right (adj₁ : L ⊣ R) (adj₂ : L' ⊣ T) (e : T ≅ T')
    (α : L' ⟶ L) :
    conjugateEquiv adj₁ (adj₂.ofNatIsoRight e) α = conjugateEquiv adj₁ adj₂ α ≫ e.hom := by
  have h := conjugateEquiv_comp adj₁ adj₂ (adj₂.ofNatIsoRight e) α (𝟙 L')
  rw [conjugateEquiv_ofNatIsoRight_hom, Category.id_comp] at h
  exact h.symm

/-- Changing the right adjoint of the *first* adjunction of a conjugate precomposes the
conjugate with `e.inv`. -/
theorem conjugateEquiv_ofNatIsoRight_left (adj₁ : L ⊣ R) (e : R ≅ R') (adj₂ : L' ⊣ T)
    (α : L' ⟶ L) :
    conjugateEquiv (adj₁.ofNatIsoRight e) adj₂ α = e.inv ≫ conjugateEquiv adj₁ adj₂ α := by
  have h := conjugateEquiv_comp (adj₁.ofNatIsoRight e) adj₁ adj₂ (𝟙 L) α
  rw [conjugateEquiv_ofNatIsoRight_id, Category.comp_id] at h
  exact h.symm

/-- The comparison of two right adjoints of one functor is the conjugate of the identity of that
functor, by definition of `CategoryTheory.Adjunction.rightAdjointUniq`. -/
theorem rightAdjointUniq_hom_eq {D₀ : Type*} {D₁ : Type*} [Category D₀] [Category D₁]
    {F : D₀ ⥤ D₁} {G G' : D₁ ⥤ D₀} (adj : F ⊣ G) (adj' : F ⊣ G') :
    (Adjunction.rightAdjointUniq adj adj').hom = conjugateEquiv adj adj' (𝟙 F) := rfl

/-- **An adjunction is any other adjunction with the same left adjoint, read through the
comparison of the two right adjoints.**  This is `CategoryTheory.Adjunction.unit_rightAdjointUniq`
packaged as an equality of adjunctions. -/
theorem eq_ofNatIsoRight_rightAdjointUniq {D₀ : Type*} {D₁ : Type*} [Category D₀] [Category D₁]
    {F : D₀ ⥤ D₁} {G G' : D₁ ⥤ D₀} (adj : F ⊣ G) (adj' : F ⊣ G') :
    adj' = adj.ofNatIsoRight (Adjunction.rightAdjointUniq adj adj') :=
  Adjunction.ext (Adjunction.unit_rightAdjointUniq_hom adj adj').symm

/-- The two transports of an adjunction — of its left adjoint along an isomorphism and of its
right adjoint along another — commute. -/
theorem ofNatIsoLeft_ofNatIsoRight {D₀ : Type*} {D₁ : Type*} [Category D₀] [Category D₁]
    {F F' : D₀ ⥤ D₁} {G G' : D₁ ⥤ D₀} (adj : F ⊣ G) (ι : F ≅ F') (e : G ≅ G') :
    (adj.ofNatIsoLeft ι).ofNatIsoRight e = (adj.ofNatIsoRight e).ofNatIsoLeft ι := by
  refine Adjunction.ext (NatTrans.ext (funext fun c ↦ ?_))
  simp only [Adjunction.ofNatIsoLeft_unit, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc]
  exact congrArg (fun t ↦ adj.unit.app c ≫ t) (e.hom.naturality (ι.hom.app c))

end OfNatIsoRight

/-! ### The conjugate of the identity of a composite -/

variable {L₁ : C₀ ⥤ C₁} {L₂ : C₁ ⥤ C₂} {P₁ Q₁ : C₁ ⥤ C₀} {P₂ Q₂ : C₂ ⥤ C₁}

/-- **The conjugate of the identity of a composite left adjoint is the horizontal composite of
the two conjugates of identities.**  Two composable functors with two right adjoints each give
two adjunctions for the composite, and the comparison of their right adjoints is the whiskered
composite of the two comparisons.

This is the mate form of `CategoryTheory.Adjunction.leftAdjointUniq_comp`; it is
`CategoryTheory.conjugateEquiv_whiskerRight` and
`CategoryTheory.conjugateEquiv_whiskerLeft` composed through the mixed adjunction
`b₁.comp a₂`. -/
theorem conjugateEquiv_comp_id (a₁ : L₁ ⊣ P₁) (a₂ : L₂ ⊣ P₂) (b₁ : L₁ ⊣ Q₁) (b₂ : L₂ ⊣ Q₂) :
    conjugateEquiv (a₁.comp a₂) (b₁.comp b₂) (𝟙 (L₁ ⋙ L₂)) =
      Functor.whiskerLeft P₂ (conjugateEquiv a₁ b₁ (𝟙 L₁)) ≫
        Functor.whiskerRight (conjugateEquiv a₂ b₂ (𝟙 L₂)) Q₁ := by
  have h := conjugateEquiv_comp (a₁.comp a₂) (b₁.comp a₂) (b₁.comp b₂)
    (Functor.whiskerRight (𝟙 L₁) L₂) (Functor.whiskerLeft L₁ (𝟙 L₂))
  rw [conjugateEquiv_whiskerRight a₁ b₁ a₂ (𝟙 L₁),
    conjugateEquiv_whiskerLeft a₂ b₂ b₁ (𝟙 L₂)] at h
  simp only [Functor.whiskerLeft_id', Functor.whiskerRight_id', Category.comp_id] at h
  exact h.symm

/-! ### The two systems -/

variable {L : C₀ ⥤ C₂} {P Q : C₂ ⥤ C₀}

/-- **An adjunction with a given left and right adjoint is determined by its conjugate against
any fixed adjunction with the same left adjoint.**  The conjugate recovers the unit, by
`CategoryTheory.unit_conjugateEquiv` at the identity. -/
theorem eq_of_conjugateEquiv_id_eq (a : L ⊣ P) (b b' : L ⊣ Q)
    (h : conjugateEquiv a b (𝟙 L) = conjugateEquiv a b' (𝟙 L)) : b = b' := by
  refine Adjunction.ext (NatTrans.ext (funext fun c ↦ ?_))
  have hb := unit_conjugateEquiv a b (𝟙 L) c
  have hb' := unit_conjugateEquiv a b' (𝟙 L) c
  rw [h] at hb
  simpa using hb.symm.trans hb'

/-- **The conjugate of the identity of `L` between the two transported composite adjunctions.**
Both composite adjunctions are read through the same isomorphism `ι` of left adjoints and
through their own comparison of right adjoints, so the conjugate is the horizontal composite of
the two comparisons of right adjoints, conjugated by `cP` and `cQ`. -/
theorem conjugateEquiv_id_transport (a₁ : L₁ ⊣ P₁) (a₂ : L₂ ⊣ P₂) (b₁ : L₁ ⊣ Q₁) (b₂ : L₂ ⊣ Q₂)
    (ι : L₁ ⋙ L₂ ≅ L) (cP : P₂ ⋙ P₁ ≅ P) (cQ : Q₂ ⋙ Q₁ ≅ Q) :
    conjugateEquiv (((a₁.comp a₂).ofNatIsoRight cP).ofNatIsoLeft ι)
        (((b₁.comp b₂).ofNatIsoRight cQ).ofNatIsoLeft ι) (𝟙 L) =
      cP.inv ≫ (Functor.whiskerLeft P₂ (conjugateEquiv a₁ b₁ (𝟙 L₁)) ≫
          Functor.whiskerRight (conjugateEquiv a₂ b₂ (𝟙 L₂)) Q₁) ≫ cQ.hom := by
  rw [conjugateEquiv_ofNatIsoLeft_left, Category.id_comp, conjugateEquiv_ofNatIsoLeft_right,
    Iso.hom_inv_id, conjugateEquiv_ofNatIsoRight_left, conjugateEquiv_ofNatIsoRight_right,
    conjugateEquiv_comp_id, Category.assoc]

/-- **Two systems of adjunctions with the same left adjoints: the composition law of the second
system is the commuting of the square of the comparisons of right adjoints.**

`L₁`, `L₂` and `L` have right adjoints `P₁, P₂, P` on one side and `Q₁, Q₂, Q` on the other,
`ι : L₁ ⋙ L₂ ≅ L` identifies the composite left adjoint, and `cP`, `cQ` are composition
comparisons of the right adjoints of the two systems.  Assume the first system's adjunction at
`L` *is* the composite of its two factors, read through `cP` and `ι` — the hypothesis `ha`.

Then the same holds of the second system if and only if `cP` followed by the comparison `P ≅ Q`
is the horizontal composite of the comparisons `P₁ ≅ Q₁` and `P₂ ≅ Q₂` followed by `cQ`, all
three comparisons being the ones uniqueness of a right adjoint supplies.

Both directions are used: forwards to transfer a composition law from a system that has one,
backwards to see that the square is that same law and not an independent statement. -/
theorem eq_comp_ofNatIsoRight_ofNatIsoLeft_iff (a₁ : L₁ ⊣ P₁) (a₂ : L₂ ⊣ P₂) (a : L ⊣ P)
    (b₁ : L₁ ⊣ Q₁) (b₂ : L₂ ⊣ Q₂) (b : L ⊣ Q) (ι : L₁ ⋙ L₂ ≅ L) (cP : P₂ ⋙ P₁ ≅ P)
    (cQ : Q₂ ⋙ Q₁ ≅ Q)
    (ha : a = ((a₁.comp a₂).ofNatIsoRight cP).ofNatIsoLeft ι) :
    b = ((b₁.comp b₂).ofNatIsoRight cQ).ofNatIsoLeft ι ↔
      cP.hom ≫ (Adjunction.rightAdjointUniq a b).hom =
        (Functor.whiskerLeft P₂ (Adjunction.rightAdjointUniq a₁ b₁).hom ≫
            Functor.whiskerRight (Adjunction.rightAdjointUniq a₂ b₂).hom Q₁) ≫ cQ.hom := by
  have key := ha ▸ conjugateEquiv_id_transport a₁ a₂ b₁ b₂ ι cP cQ
  rw [rightAdjointUniq_hom_eq a b, rightAdjointUniq_hom_eq a₁ b₁, rightAdjointUniq_hom_eq a₂ b₂,
    ← Iso.eq_inv_comp cP]
  exact ⟨fun hb ↦ hb ▸ key, fun hsq ↦ eq_of_conjugateEquiv_id_eq a b _ (hsq.trans key.symm)⟩

/-- **The same equivalence with the first system's composition comparison taken to be the
canonical one.**  No hypothesis is left: the comparison of right adjoints of the first system is
`CategoryTheory.Adjunction.rightAdjointUniq` of its own composite adjunction against its
adjunction at `L`, and then the first system's composition law holds by construction.

So the second system's composition law is *exactly* the commuting of the square of the three
comparisons of right adjoints — in particular a proof of the square that computes two of those
three comparisons by uniqueness of a right adjoint cannot be a proof of the composition law: it
is the composition law. -/
theorem eq_comp_ofNatIsoRight_ofNatIsoLeft_iff_rightAdjointUniq (a₁ : L₁ ⊣ P₁) (a₂ : L₂ ⊣ P₂)
    (a : L ⊣ P) (b₁ : L₁ ⊣ Q₁) (b₂ : L₂ ⊣ Q₂) (b : L ⊣ Q) (ι : L₁ ⋙ L₂ ≅ L)
    (cQ : Q₂ ⋙ Q₁ ≅ Q) :
    b = ((b₁.comp b₂).ofNatIsoRight cQ).ofNatIsoLeft ι ↔
      (Adjunction.rightAdjointUniq ((a₁.comp a₂).ofNatIsoLeft ι) a).hom ≫
          (Adjunction.rightAdjointUniq a b).hom =
        (Functor.whiskerLeft P₂ (Adjunction.rightAdjointUniq a₁ b₁).hom ≫
            Functor.whiskerRight (Adjunction.rightAdjointUniq a₂ b₂).hom Q₁) ≫ cQ.hom :=
  eq_comp_ofNatIsoRight_ofNatIsoLeft_iff a₁ a₂ a b₁ b₂ b ι
    (Adjunction.rightAdjointUniq ((a₁.comp a₂).ofNatIsoLeft ι) a) cQ
    ((eq_ofNatIsoRight_rightAdjointUniq ((a₁.comp a₂).ofNatIsoLeft ι) a).trans
      (ofNatIsoLeft_ofNatIsoRight (a₁.comp a₂) ι _))

end Stacks.CategoryTheory

end
