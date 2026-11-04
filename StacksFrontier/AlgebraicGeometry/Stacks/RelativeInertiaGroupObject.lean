module

public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeInertiaGroupAxioms
public import StacksFrontier.AlgebraicGeometry.Stacks.SpacesOverStackCategory

/-!
# The relative inertia is a group object (Stacks 050R)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks. Stacks 050R asserts that the relative
inertia `I_{𝒳/𝒴}` is a **group object** in the category of 1-morphisms to `𝒳` representable by
algebraic spaces (Stacks 04ZQ), with multiplication the composition law

`c : I_{𝒳/𝒴} ×_𝒳 I_{𝒳/𝒴} ⟶ I_{𝒳/𝒴}`, `((x, α), (x', α'), β) ↦ (x, α ∘ β⁻¹ ∘ α' ∘ β)`,

and unit the neutral element `e : 𝒳 ⟶ I_{𝒳/𝒴}`, `x ↦ (x, id_x)`. The source omits the
verification of the group-object axioms; they are supplied here.

The category in question is `CategoryTheory.Bicategory.IsoClassCategory` of the 2-category
`AlgebraicGeometry.Stack.SpacesOverStack`, with the finite products of
`AlgebraicGeometry.Stack.SpacesOverStack.instCartesianMonoidalCategory`: the terminal object is
`𝟙 𝒳` and the binary product is the 2-fibre product over `𝒳`. The group-object
structure is `AlgebraicGeometry.Stack.relativeInertiaGrpObj`; its multiplication, unit and
inverse are *by construction* the isomorphism classes of `c`, of `e` and of
`i : (x, α) ↦ (x, α⁻¹)`, which is what the three identification theorems below record.

## Main definitions

* `AlgebraicGeometry.Stack.relativeInertiaOneHom`,
  `AlgebraicGeometry.Stack.relativeInertiaMulHom` and
  `AlgebraicGeometry.Stack.relativeInertiaInvHom`: the neutral element, the composition law and
  the inverse, as 1-morphisms of the 2-category `Spaces/𝒳` out of the terminal object, out of
  the binary product, and out of the relative inertia itself.
* `AlgebraicGeometry.Stack.relativeInertiaPairIdNeutralHom`, `…PairNeutralIdHom`,
  `…PairIdInverseHom`, `…PairInverseIdHom`, `…CompFstPairHom`, `…MidPairHom`,
  `…IdCompPairHom`: the 1-morphisms of `Spaces/𝒳` into the twofold product on which the
  group-object axioms are read, built from the functors of
  `StacksFrontier/AlgebraicGeometry/Stacks/RelativeInertiaGroupLaw.lean`.

## Main results

* `AlgebraicGeometry.Stack.relativeInertiaGrpObj`: **Stacks 050R**, the group-object structure.
* `AlgebraicGeometry.Stack.relativeInertiaGrpObj_mul`,
  `AlgebraicGeometry.Stack.relativeInertiaGrpObj_one` and
  `AlgebraicGeometry.Stack.relativeInertiaGrpObj_inv`: its multiplication, unit and inverse are
  the isomorphism classes of `c`, `e` and `i`.
* `CategoryTheory.CartesianMonoidalCategory.one_mul_of_lift`,
  `CategoryTheory.CartesianMonoidalCategory.mul_one_of_lift` and
  `CategoryTheory.CartesianMonoidalCategory.mul_assoc_of_lift`: the monoid-object axioms in the
  form in which the strict identities of Stacks 050R deliver them.

## Implementation notes

Each axiom is obtained from the corresponding *strict* identity of functors proved in
`StacksFrontier/AlgebraicGeometry/Stacks/RelativeInertiaGroupLaw.lean` in three steps: the
1-morphism of `Spaces/𝒳` built from the relevant functor is shown to have the two projections
the monoidal structure prescribes, hence to be the corresponding `lift`
(`AlgebraicGeometry.Stack.SpacesOverStack.prod_hom_ext`); the strict identity is transported to
the isomorphism classes; and the resulting `lift`-form of the axiom is converted to Mathlib's
form by the three lemmas of the first section.

Comparing two 1-morphisms of `Spaces/𝒳` means comparing their comparison 2-morphisms. All of
them here are identities or the filler of a 2-fibre product square, and the structural
2-isomorphisms of the 2-category of algebraic stacks are identities
(`AlgebraicGeometry.Stack.stackAssociator_inv_eq_id` and its companions), so the comparisons are
short. They are written in term mode rather than with `rw`/`simp`: a hom-category of the
2-category of algebraic stacks carries two definitionally equal but syntactically distinct
`CategoryTheory.Category` instances, and a tactic that has to match an instance argument makes
no progress there, while a proof term is checked up to definitional equality.

## References

* [Stacks Project, Tag 04ZQ](https://stacks.math.columbia.edu/tag/04ZQ)
* [Stacks Project, Tag 050R](https://stacks.math.columbia.edu/tag/050R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits

namespace CategoryTheory.CartesianMonoidalCategory

open scoped MonoidalCategory

universe vC uC

variable {C : Type uC} [Category.{vC} C] [CartesianMonoidalCategory C] {X : C}

/-- The left unit axiom of a monoid object, from its form as an identity between morphisms out
of the object itself. -/
theorem one_mul_of_lift (one : 𝟙_ C ⟶ X) (mul : X ⊗ X ⟶ X)
    (h : lift (toUnit X ≫ one) (𝟙 X) ≫ mul = 𝟙 X) : one ▷ X ≫ mul = (λ_ X).hom := by
  have hl : (λ_ X).inv = lift (toUnit X) (𝟙 X) := by refine hom_ext _ _ ?_ ?_ <;> simp
  refine (cancel_epi (λ_ X).inv).1 ?_
  rw [← Category.assoc, hl, lift_whiskerRight, h]
  simp

/-- The right unit axiom of a monoid object, from its form as an identity between morphisms out
of the object itself. -/
theorem mul_one_of_lift (one : 𝟙_ C ⟶ X) (mul : X ⊗ X ⟶ X)
    (h : lift (𝟙 X) (toUnit X ≫ one) ≫ mul = 𝟙 X) : X ◁ one ≫ mul = (ρ_ X).hom := by
  have hl : (ρ_ X).inv = lift (𝟙 X) (toUnit X) := by refine hom_ext _ _ ?_ ?_ <;> simp
  refine (cancel_epi (ρ_ X).inv).1 ?_
  rw [← Category.assoc, hl, lift_whiskerLeft, h]
  simp

/-- Whiskering on the right is a lift. -/
theorem whiskerRight_eq_lift (mul : X ⊗ X ⟶ X) :
    mul ▷ X = lift (fst (X ⊗ X) X ≫ mul) (snd (X ⊗ X) X) := by
  refine hom_ext _ _ ?_ ?_ <;> simp

/-- The second projection out of the associator is a lift. -/
theorem associator_hom_comp_snd (X : C) :
    (α_ X X X).hom ≫ snd X (X ⊗ X) = lift (fst (X ⊗ X) X ≫ snd X X) (snd (X ⊗ X) X) := by
  refine hom_ext _ _ ?_ ?_ <;> simp

/-- The associator followed by whiskering on the left is a lift. -/
theorem associator_hom_comp_whiskerLeft_eq_lift (mul : X ⊗ X ⟶ X) :
    (α_ X X X).hom ≫ X ◁ mul =
      lift (fst (X ⊗ X) X ≫ fst X X)
        (lift (fst (X ⊗ X) X ≫ snd X X) (snd (X ⊗ X) X) ≫ mul) := by
  refine hom_ext _ _ ?_ ?_
  · rw [Category.assoc, whiskerLeft_fst, associator_hom_fst, lift_fst]
  · rw [Category.assoc, whiskerLeft_snd, ← Category.assoc, associator_hom_comp_snd, lift_snd]

/-- The associativity axiom of a monoid object, from its form as an identity between lifts. -/
theorem mul_assoc_of_lift (mul : X ⊗ X ⟶ X)
    (h : lift (fst (X ⊗ X) X ≫ mul) (snd (X ⊗ X) X) ≫ mul =
      lift (fst (X ⊗ X) X ≫ fst X X)
        (lift (fst (X ⊗ X) X ≫ snd X X) (snd (X ⊗ X) X) ≫ mul) ≫ mul) :
    mul ▷ X ≫ mul = (α_ X X X).hom ≫ X ◁ mul ≫ mul := by
  rw [whiskerRight_eq_lift, ← Category.assoc, associator_hom_comp_whiskerLeft_eq_lift]
  exact h

end CategoryTheory.CartesianMonoidalCategory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A 1-morphism of algebraic stacks is determined by its underlying functor. -/
theorem algebraicStacksHom_ext {X Y : AlgebraicStacks.{u, w} B S hS} {a b : X ⟶ Y}
    (h : a.hom.hom.toFunctor = b.hom.hom.toFunctor) : a = b :=
  Bicategory.InducedBicategory.hom_ext (Bicategory.InducedBicategory.hom_ext
    (BasedCategory.BasedFunctor.ext' h))

/-- The associator of the 2-category of algebraic stacks is an identity 2-morphism. -/
theorem stackAssociator_inv_eq_id {X Y Z W : AlgebraicStacks.{u, w} B S hS} (a : X ⟶ Y)
    (b : Y ⟶ Z) (c : Z ⟶ W) : (Bicategory.associator a b c).inv = 𝟙 ((a ≫ b) ≫ c) := rfl

/-- The left unitor of the 2-category of algebraic stacks is an identity 2-morphism. -/
theorem stackLeftUnitor_inv_eq_id {X Y : AlgebraicStacks.{u, w} B S hS} (a : X ⟶ Y) :
    (Bicategory.leftUnitor a).inv = 𝟙 (𝟙 X ≫ a) := rfl

/-- The right unitor of the 2-category of algebraic stacks is an identity 2-morphism. -/
theorem stackRightUnitor_inv_eq_id {X Y : AlgebraicStacks.{u, w} B S hS} (a : X ⟶ Y) :
    (Bicategory.rightUnitor a).inv = 𝟙 (a ≫ 𝟙 Y) := rfl

namespace SpacesOverStack

variable {𝒳 : AlgebraicStacks.{u, w} B S hS}

/-- The comparison 2-morphism of a composite of 1-morphisms of `Spaces/𝒳`. -/
theorem comp_comm_eq {F G H : SpacesOverStack B S hS 𝒳} (k : F ⟶ G) (l : G ⟶ H) :
    (k ≫ l).comm = k.comm ≫ (k.map ◁ l.comm) :=
  (rfl : (k ≫ l).comm =
      k.comm ≫ (k.map ◁ l.comm) ≫ (Bicategory.associator k.map l.map H.map).inv).trans
    ((congrArg (fun t => k.comm ≫ (k.map ◁ l.comm) ≫ t)
        (stackAssociator_inv_eq_id B S hS k.map l.map H.map)).trans
      (congrArg (fun t => k.comm ≫ t) (Category.comp_id _)))

/-- The comparison 2-morphism of a composite of 1-morphisms of `Spaces/𝒳` whose first factor has
an identity comparison 2-morphism. -/
theorem comp_comm_eq_whisker {F G H : SpacesOverStack B S hS 𝒳} (k : F ⟶ G) (l : G ⟶ H)
    (hk' : F.map = k.map ≫ G.map) (hk : k.comm = eqToHom hk') :
    (k ≫ l).comm = eqToHom hk' ≫ (k.map ◁ l.comm) :=
  (comp_comm_eq B S hS k l).trans (congrArg (fun t => t ≫ (k.map ◁ l.comm)) hk)

/-- The comparison 2-morphism of a composite of two 1-morphisms of `Spaces/𝒳` whose comparison
2-morphisms are both induced by equalities of 1-morphisms. -/
theorem comp_comm_eq_eqToHom {F G H : SpacesOverStack B S hS 𝒳} (k : F ⟶ G) (l : G ⟶ H)
    (hk' : F.map = k.map ≫ G.map) (hl' : G.map = l.map ≫ H.map)
    (hk : k.comm = eqToHom hk') (hl : l.comm = eqToHom hl')
    (h : F.map = (k.map ≫ l.map) ≫ H.map) : (k ≫ l).comm = eqToHom h :=
  (comp_comm_eq_whisker B S hS k l hk' hk).trans
    ((congrArg (fun t => eqToHom hk' ≫ (k.map ◁ t)) hl).trans
      ((congrArg (fun t => eqToHom hk' ≫ t) (Bicategory.whiskerLeft_eqToHom k.map hl')).trans
        (eqToHom_trans _ _)))

/-- The comparison 2-morphism of an identity 1-morphism of `Spaces/𝒳` is an identity. -/
theorem id_comm_eq_eqToHom (F : SpacesOverStack B S hS 𝒳) (h : F.map = 𝟙 F.source ≫ F.map) :
    (𝟙 F : F ⟶ F).comm = eqToHom h :=
  stackLeftUnitor_inv_eq_id B S hS F.map

/-- Two 1-morphisms of `Spaces/𝒳` with the same underlying 1-morphism of algebraic stacks and
equal comparison 2-morphisms have the same isomorphism class. -/
theorem homMk_eq_of_comm_eq {F G : SpacesOverStack B S hS 𝒳} (f g : F ⟶ G) (hm : f.map = g.map)
    (h : f.comm ≫ eqToHom (congrArg (fun t => t ≫ G.map) hm) = g.comm) :
    IsoClassCategory.homMk f = IsoClassCategory.homMk g :=
  IsoClassCategory.homMk_eq_of_iso
    { hom := ⟨eqToHom hm,
        (congrArg (fun t => f.comm ≫ t) (Bicategory.eqToHom_whiskerRight hm G.map)).trans h⟩
      inv := ⟨eqToHom hm.symm,
        (congrArg (fun t => g.comm ≫ t) (Bicategory.eqToHom_whiskerRight hm.symm G.map)).trans
          (((congrArg (fun t => t ≫ eqToHom (congrArg (fun r => r ≫ G.map) hm.symm))
                h.symm).trans (Category.assoc _ _ _)).trans
            ((congrArg (fun t => f.comm ≫ t)
              ((eqToHom_trans (congrArg (fun r => r ≫ G.map) hm)
                  (congrArg (fun r => r ≫ G.map) hm.symm)).trans
                (eqToHom_refl (f.map ≫ G.map) _))).trans (Category.comp_id _)))⟩
      hom_inv_id := Hom₂.ext ((eqToHom_trans hm hm.symm).trans (eqToHom_refl f.map _))
      inv_hom_id := Hom₂.ext ((eqToHom_trans hm.symm hm).trans (eqToHom_refl g.map _)) }

/-- **Two 1-morphisms of `Spaces/𝒳` whose underlying 1-morphisms of algebraic stacks are equal
and whose comparison 2-morphisms are both induced by equalities of 1-morphisms have the same
isomorphism class.** -/
theorem homMk_eq_of_comm_eqToHom {F G : SpacesOverStack B S hS 𝒳} {f g : F ⟶ G}
    (hm : f.map = g.map) (hf' : F.map = f.map ≫ G.map) (hg' : F.map = g.map ≫ G.map)
    (hf : f.comm = eqToHom hf') (hg : g.comm = eqToHom hg') :
    IsoClassCategory.homMk f = IsoClassCategory.homMk g :=
  homMk_eq_of_map_eq B S hS f g hm
    ((congrArg (fun t => t ≫ (eqToIso hm).hom ▷ G.map) hf).trans
      ((congrArg (fun t => eqToHom hf' ≫ t) (Bicategory.eqToHom_whiskerRight hm G.map)).trans
        ((eqToHom_trans _ _).trans hg.symm)))

end SpacesOverStack

open SpacesOverStack

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- The neutral element as a 1-morphism of `Spaces/𝒳` from the terminal object. -/
noncomputable def relativeInertiaOneHom (f : 𝒳 ⟶ 𝒴) :
    terminalObj B S hS 𝒳 ⟶ relativeInertiaOverStack B S hS f where
  map := relativeInertiaNeutralHom B S hS f
  comm := 𝟙 _

/-- The composition law as a 1-morphism of `Spaces/𝒳` out of the binary product. -/
noncomputable def relativeInertiaMulHom (f : 𝒳 ⟶ 𝒴) :
    prodObj B S hS (relativeInertiaOverStack B S hS f) (relativeInertiaOverStack B S hS f) ⟶
      relativeInertiaOverStack B S hS f :=
  relativeInertiaCompositionHom B S hS f

/-- The inverse as a 1-morphism of `Spaces/𝒳`. -/
noncomputable def relativeInertiaInvHom (f : 𝒳 ⟶ 𝒴) :
    relativeInertiaOverStack B S hS f ⟶ relativeInertiaOverStack B S hS f :=
  relativeInertiaInverseHom B S hS f

/-- `⟨id, e ∘ π⟩ : I ⟶ I ×_𝒳 I` as a 1-morphism of `Spaces/𝒳`. -/
noncomputable def relativeInertiaPairIdNeutralHom (f : 𝒳 ⟶ 𝒴) :
    relativeInertiaOverStack B S hS f ⟶
      prodObj B S hS (relativeInertiaOverStack B S hS f)
        (relativeInertiaOverStack B S hS f) where
  map := Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    { toFunctor := RelativeInertia.pairIdNeutral f.hom.hom.toFunctor 𝒳.val.val.p
      w := TwoFibreProductOver.lift_comp_structureFunctor .. })
  comm := 𝟙 _

/-- `⟨e ∘ π, id⟩ : I ⟶ I ×_𝒳 I` as a 1-morphism of `Spaces/𝒳`. -/
noncomputable def relativeInertiaPairNeutralIdHom (f : 𝒳 ⟶ 𝒴) :
    relativeInertiaOverStack B S hS f ⟶
      prodObj B S hS (relativeInertiaOverStack B S hS f)
        (relativeInertiaOverStack B S hS f) where
  map := Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    { toFunctor := RelativeInertia.pairNeutralId f.hom.hom.toFunctor 𝒳.val.val.p
      w := TwoFibreProductOver.lift_comp_structureFunctor .. })
  comm := 𝟙 _

/-- `⟨id, i⟩ : I ⟶ I ×_𝒳 I` as a 1-morphism of `Spaces/𝒳`. -/
noncomputable def relativeInertiaPairIdInverseHom (f : 𝒳 ⟶ 𝒴) :
    relativeInertiaOverStack B S hS f ⟶
      prodObj B S hS (relativeInertiaOverStack B S hS f)
        (relativeInertiaOverStack B S hS f) where
  map := Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    { toFunctor := RelativeInertia.pairIdInverse f.hom.hom.toFunctor 𝒳.val.val.p
      w := TwoFibreProductOver.lift_comp_structureFunctor .. })
  comm := 𝟙 _

/-- `⟨i, id⟩ : I ⟶ I ×_𝒳 I` as a 1-morphism of `Spaces/𝒳`. -/
noncomputable def relativeInertiaPairInverseIdHom (f : 𝒳 ⟶ 𝒴) :
    relativeInertiaOverStack B S hS f ⟶
      prodObj B S hS (relativeInertiaOverStack B S hS f)
        (relativeInertiaOverStack B S hS f) where
  map := Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    { toFunctor := RelativeInertia.pairInverseId f.hom.hom.toFunctor 𝒳.val.val.p
      w := TwoFibreProductOver.lift_comp_structureFunctor .. })
  comm := 𝟙 _

/-- `c × id : (I ×_𝒳 I) ×_𝒳 I ⟶ I ×_𝒳 I` as a 1-morphism of `Spaces/𝒳`. -/
noncomputable def relativeInertiaCompFstPairHom (f : 𝒳 ⟶ 𝒴) :
    prodObj B S hS (prodObj B S hS (relativeInertiaOverStack B S hS f)
          (relativeInertiaOverStack B S hS f)) (relativeInertiaOverStack B S hS f) ⟶
      prodObj B S hS (relativeInertiaOverStack B S hS f)
        (relativeInertiaOverStack B S hS f) where
  map := Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    { toFunctor := RelativeInertia.compFstPair f.hom.hom.toFunctor 𝒳.val.val.p
      w := TwoFibreProductOver.lift_comp_structureFunctor .. })
  comm := 𝟙 _

/-- `(id × c) ∘ assoc : (I ×_𝒳 I) ×_𝒳 I ⟶ I ×_𝒳 I` as a 1-morphism of `Spaces/𝒳`. -/
noncomputable def relativeInertiaIdCompPairHom (f : 𝒳 ⟶ 𝒴) :
    prodObj B S hS (prodObj B S hS (relativeInertiaOverStack B S hS f)
          (relativeInertiaOverStack B S hS f)) (relativeInertiaOverStack B S hS f) ⟶
      prodObj B S hS (relativeInertiaOverStack B S hS f)
        (relativeInertiaOverStack B S hS f) where
  map := Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    { toFunctor := RelativeInertia.idCompPair f.hom.hom.toFunctor 𝒳.val.val.p
      w := TwoFibreProductOver.lift_comp_structureFunctor .. })
  comm := 𝟙 _

/-- `(pr₂, pr₃) : (I ×_𝒳 I) ×_𝒳 I ⟶ I ×_𝒳 I` as a 1-morphism of `Spaces/𝒳`. Its comparison
2-morphism is the filler of the inner 2-fibre product square, whiskered with the projection to
the first two factors. -/
noncomputable def relativeInertiaMidPairHom (f : 𝒳 ⟶ 𝒴) :
    prodObj B S hS (prodObj B S hS (relativeInertiaOverStack B S hS f)
          (relativeInertiaOverStack B S hS f)) (relativeInertiaOverStack B S hS f) ⟶
      prodObj B S hS (relativeInertiaOverStack B S hS f)
        (relativeInertiaOverStack B S hS f) where
  map := Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    { toFunctor := RelativeInertia.midPair f.hom.hom.toFunctor 𝒳.val.val.p
      w := TwoFibreProductOver.lift_comp_structureFunctor .. })
  comm := (prodFst B S hS (prodObj B S hS (relativeInertiaOverStack B S hS f)
      (relativeInertiaOverStack B S hS f)) (relativeInertiaOverStack B S hS f)).map ◁
    (prodSnd B S hS (relativeInertiaOverStack B S hS f)
      (relativeInertiaOverStack B S hS f)).comm



/-- The comparison 2-morphism of `k ≫ prodSnd` when `k` has an identity comparison 2-morphism
and the whiskered filler of the 2-fibre product square is an identity. -/
theorem comp_prodSnd_comm_eq_eqToHom {F A D : SpacesOverStack B S hS 𝒳}
    (k : F ⟶ SpacesOverStack.prodObj B S hS A D)
    (hk' : F.map = k.map ≫ (SpacesOverStack.prodObj B S hS A D).map)
    (hk : k.comm = eqToHom hk')
    (hw' : k.map ≫ (SpacesOverStack.prodObj B S hS A D).map =
      k.map ≫ ((SpacesOverStack.prodSnd B S hS A D).map ≫ D.map))
    (hw : k.map ◁ (SpacesOverStack.prodSnd B S hS A D).comm = eqToHom hw')
    (h : F.map = (k.map ≫ (SpacesOverStack.prodSnd B S hS A D).map) ≫ D.map) :
    (k ≫ SpacesOverStack.prodSnd B S hS A D).comm = eqToHom h :=
  (SpacesOverStack.comp_comm_eq_whisker B S hS k _ hk' hk).trans
    ((congrArg (fun t => eqToHom hk' ≫ t) hw).trans (eqToHom_trans _ _))

/-! ### The projections of the four 1-morphisms into the twofold product -/

/-- Two 2-morphisms of algebraic stacks are equal if their components are. -/
private theorem hom₂_ext_of_app {X Y : AlgebraicStacks.{u, w} B S hS} {a b : X ⟶ Y}
    {α β : a ⟶ b} (h : ∀ x, α.hom.hom.app x = β.hom.hom.app x) : α = β :=
  Bicategory.InducedBicategory.hom₂_ext (Bicategory.InducedBicategory.hom₂_ext
    (BasedNatTrans.ext _ _ (NatTrans.ext (funext h))))

/-- The whiskered filler of the 2-fibre product square along `⟨id, e ∘ π⟩` is an identity: the
comparison isomorphism of `⟨id, e ∘ π⟩` is the identity. -/
theorem pairIdNeutral_whiskerLeft_prodSnd_comm (f : 𝒳 ⟶ 𝒴) :
    (relativeInertiaPairIdNeutralHom B S hS f).map ◁
        (prodSnd B S hS (relativeInertiaOverStack B S hS f)
          (relativeInertiaOverStack B S hS f)).comm =
      𝟙 ((relativeInertiaPairIdNeutralHom B S hS f).map ≫
        (prodObj B S hS (relativeInertiaOverStack B S hS f)
          (relativeInertiaOverStack B S hS f)).map) :=
  hom₂_ext_of_app B S hS fun _ => rfl

/-- The whiskered filler of the 2-fibre product square along `⟨e ∘ π, id⟩` is an identity. -/
theorem pairNeutralId_whiskerLeft_prodSnd_comm (f : 𝒳 ⟶ 𝒴) :
    (relativeInertiaPairNeutralIdHom B S hS f).map ◁
        (prodSnd B S hS (relativeInertiaOverStack B S hS f)
          (relativeInertiaOverStack B S hS f)).comm =
      𝟙 ((relativeInertiaPairNeutralIdHom B S hS f).map ≫
        (prodObj B S hS (relativeInertiaOverStack B S hS f)
          (relativeInertiaOverStack B S hS f)).map) :=
  hom₂_ext_of_app B S hS fun _ => rfl

/-- The whiskered filler of the 2-fibre product square along `⟨id, i⟩` is an identity. -/
theorem pairIdInverse_whiskerLeft_prodSnd_comm (f : 𝒳 ⟶ 𝒴) :
    (relativeInertiaPairIdInverseHom B S hS f).map ◁
        (prodSnd B S hS (relativeInertiaOverStack B S hS f)
          (relativeInertiaOverStack B S hS f)).comm =
      𝟙 ((relativeInertiaPairIdInverseHom B S hS f).map ≫
        (prodObj B S hS (relativeInertiaOverStack B S hS f)
          (relativeInertiaOverStack B S hS f)).map) :=
  hom₂_ext_of_app B S hS fun _ => rfl

/-- The whiskered filler of the 2-fibre product square along `⟨i, id⟩` is an identity. -/
theorem pairInverseId_whiskerLeft_prodSnd_comm (f : 𝒳 ⟶ 𝒴) :
    (relativeInertiaPairInverseIdHom B S hS f).map ◁
        (prodSnd B S hS (relativeInertiaOverStack B S hS f)
          (relativeInertiaOverStack B S hS f)).comm =
      𝟙 ((relativeInertiaPairInverseIdHom B S hS f).map ≫
        (prodObj B S hS (relativeInertiaOverStack B S hS f)
          (relativeInertiaOverStack B S hS f)).map) :=
  hom₂_ext_of_app B S hS fun _ => rfl

/-! ### Identification of the group-law data with morphisms of the product -/

/-- `⟨e ∘ π, id⟩` has first projection `e ∘ π`. -/
theorem homMk_pairNeutralId_comp_prodFst (f : 𝒳 ⟶ 𝒴) :
    IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (relativeInertiaPairNeutralIdHom B S hS f
      ≫ prodFst B S hS (relativeInertiaOverStack B S hS f) (relativeInertiaOverStack B S hS f)) =
      IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (toTerminalObj B S hS
        (relativeInertiaOverStack B S hS f) ≫ relativeInertiaOneHom B S hS f) :=
  SpacesOverStack.homMk_eq_of_comm_eqToHom B S hS rfl rfl rfl (SpacesOverStack.comp_comm_eq_eqToHom
    B S hS _ _ rfl rfl rfl rfl _) (SpacesOverStack.comp_comm_eq_eqToHom B S hS _ _ rfl rfl rfl rfl
    _)

/-- `⟨e ∘ π, id⟩` has second projection the identity. -/
theorem homMk_pairNeutralId_comp_prodSnd (f : 𝒳 ⟶ 𝒴) :
    IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (relativeInertiaPairNeutralIdHom B S hS f
      ≫ prodSnd B S hS (relativeInertiaOverStack B S hS f) (relativeInertiaOverStack B S hS f)) =
      IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (𝟙 (relativeInertiaOverStack B S hS f))
        :=
  SpacesOverStack.homMk_eq_of_comm_eqToHom B S hS rfl rfl rfl (comp_prodSnd_comm_eq_eqToHom B S hS
    _ rfl rfl rfl (pairNeutralId_whiskerLeft_prodSnd_comm B S hS f) _)
    (SpacesOverStack.id_comm_eq_eqToHom B S hS _ _)

/-- **The left unit law for the composition law**, as an equality of isomorphism classes. -/
theorem homMk_pairNeutralId_comp_mul (f : 𝒳 ⟶ 𝒴) :
    IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (relativeInertiaPairNeutralIdHom B S hS f
      ≫ relativeInertiaMulHom B S hS f) =
      IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (𝟙 (relativeInertiaOverStack B S hS f))
        :=
  SpacesOverStack.homMk_eq_of_comm_eqToHom B S hS (algebraicStacksHom_ext B S hS
      (RelativeInertia.composition_pairNeutralId f.hom.hom.toFunctor 𝒳.val.val.p)) rfl rfl
        (SpacesOverStack.comp_comm_eq_eqToHom B S hS _ _ rfl rfl rfl rfl _)
        (SpacesOverStack.id_comm_eq_eqToHom B S hS _ _)

/-- `⟨id, e ∘ π⟩` has first projection the identity. -/
theorem homMk_pairIdNeutral_comp_prodFst (f : 𝒳 ⟶ 𝒴) :
    IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (relativeInertiaPairIdNeutralHom B S hS f
      ≫ prodFst B S hS (relativeInertiaOverStack B S hS f) (relativeInertiaOverStack B S hS f)) =
      IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (𝟙 (relativeInertiaOverStack B S hS f))
        :=
  SpacesOverStack.homMk_eq_of_comm_eqToHom B S hS rfl rfl rfl (SpacesOverStack.comp_comm_eq_eqToHom
    B S hS _ _ rfl rfl rfl rfl _) (SpacesOverStack.id_comm_eq_eqToHom B S hS _ _)

/-- `⟨id, e ∘ π⟩` has second projection `e ∘ π`. -/
theorem homMk_pairIdNeutral_comp_prodSnd (f : 𝒳 ⟶ 𝒴) :
    IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (relativeInertiaPairIdNeutralHom B S hS f
      ≫ prodSnd B S hS (relativeInertiaOverStack B S hS f) (relativeInertiaOverStack B S hS f)) =
      IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (toTerminalObj B S hS
        (relativeInertiaOverStack B S hS f) ≫ relativeInertiaOneHom B S hS f) :=
  SpacesOverStack.homMk_eq_of_comm_eqToHom B S hS rfl rfl rfl (comp_prodSnd_comm_eq_eqToHom B S hS
    _ rfl rfl rfl (pairIdNeutral_whiskerLeft_prodSnd_comm B S hS f) _)
    (SpacesOverStack.comp_comm_eq_eqToHom B S hS _ _ rfl rfl rfl rfl _)

/-- **The right unit law for the composition law**, as an equality of isomorphism classes. -/
theorem homMk_pairIdNeutral_comp_mul (f : 𝒳 ⟶ 𝒴) :
    IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (relativeInertiaPairIdNeutralHom B S hS f
      ≫ relativeInertiaMulHom B S hS f) =
      IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (𝟙 (relativeInertiaOverStack B S hS f))
        :=
  SpacesOverStack.homMk_eq_of_comm_eqToHom B S hS (algebraicStacksHom_ext B S hS
      (RelativeInertia.composition_pairIdNeutral f.hom.hom.toFunctor 𝒳.val.val.p)) rfl rfl
        (SpacesOverStack.comp_comm_eq_eqToHom B S hS _ _ rfl rfl rfl rfl _)
        (SpacesOverStack.id_comm_eq_eqToHom B S hS _ _)

/-- `⟨i, id⟩` has first projection the inverse. -/
theorem homMk_pairInverseId_comp_prodFst (f : 𝒳 ⟶ 𝒴) :
    IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (relativeInertiaPairInverseIdHom B S hS f
      ≫ prodFst B S hS (relativeInertiaOverStack B S hS f) (relativeInertiaOverStack B S hS f)) =
      IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (relativeInertiaInvHom B S hS f) :=
  SpacesOverStack.homMk_eq_of_comm_eqToHom B S hS rfl rfl rfl (SpacesOverStack.comp_comm_eq_eqToHom
    B S hS _ _ rfl rfl rfl rfl _) rfl

/-- `⟨i, id⟩` has second projection the identity. -/
theorem homMk_pairInverseId_comp_prodSnd (f : 𝒳 ⟶ 𝒴) :
    IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (relativeInertiaPairInverseIdHom B S hS f
      ≫ prodSnd B S hS (relativeInertiaOverStack B S hS f) (relativeInertiaOverStack B S hS f)) =
      IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (𝟙 (relativeInertiaOverStack B S hS f))
        :=
  SpacesOverStack.homMk_eq_of_comm_eqToHom B S hS rfl rfl rfl (comp_prodSnd_comm_eq_eqToHom B S hS
    _ rfl rfl rfl (pairInverseId_whiskerLeft_prodSnd_comm B S hS f) _)
    (SpacesOverStack.id_comm_eq_eqToHom B S hS _ _)

/-- **The left inverse law for the composition law**, as an equality of isomorphism classes. -/
theorem homMk_pairInverseId_comp_mul (f : 𝒳 ⟶ 𝒴) :
    IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (relativeInertiaPairInverseIdHom B S hS f
      ≫ relativeInertiaMulHom B S hS f) =
      IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (toTerminalObj B S hS
        (relativeInertiaOverStack B S hS f) ≫ relativeInertiaOneHom B S hS f) :=
  SpacesOverStack.homMk_eq_of_comm_eqToHom B S hS (algebraicStacksHom_ext B S hS
      (RelativeInertia.composition_pairInverseId f.hom.hom.toFunctor 𝒳.val.val.p)) rfl rfl
        (SpacesOverStack.comp_comm_eq_eqToHom B S hS _ _ rfl rfl rfl rfl _)
        (SpacesOverStack.comp_comm_eq_eqToHom B S hS _ _ rfl rfl rfl rfl _)

/-- `⟨id, i⟩` has first projection the identity. -/
theorem homMk_pairIdInverse_comp_prodFst (f : 𝒳 ⟶ 𝒴) :
    IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (relativeInertiaPairIdInverseHom B S hS f
      ≫ prodFst B S hS (relativeInertiaOverStack B S hS f) (relativeInertiaOverStack B S hS f)) =
      IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (𝟙 (relativeInertiaOverStack B S hS f))
        :=
  SpacesOverStack.homMk_eq_of_comm_eqToHom B S hS rfl rfl rfl (SpacesOverStack.comp_comm_eq_eqToHom
    B S hS _ _ rfl rfl rfl rfl _) (SpacesOverStack.id_comm_eq_eqToHom B S hS _ _)

/-- `⟨id, i⟩` has second projection the inverse. -/
theorem homMk_pairIdInverse_comp_prodSnd (f : 𝒳 ⟶ 𝒴) :
    IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (relativeInertiaPairIdInverseHom B S hS f
      ≫ prodSnd B S hS (relativeInertiaOverStack B S hS f) (relativeInertiaOverStack B S hS f)) =
      IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (relativeInertiaInvHom B S hS f) :=
  SpacesOverStack.homMk_eq_of_comm_eqToHom B S hS rfl rfl rfl (comp_prodSnd_comm_eq_eqToHom B S hS
    _ rfl rfl rfl (pairIdInverse_whiskerLeft_prodSnd_comm B S hS f) _) rfl

/-- **The right inverse law for the composition law**, as an equality of isomorphism classes. -/
theorem homMk_pairIdInverse_comp_mul (f : 𝒳 ⟶ 𝒴) :
    IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (relativeInertiaPairIdInverseHom B S hS f
      ≫ relativeInertiaMulHom B S hS f) =
      IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (toTerminalObj B S hS
        (relativeInertiaOverStack B S hS f) ≫ relativeInertiaOneHom B S hS f) :=
  SpacesOverStack.homMk_eq_of_comm_eqToHom B S hS (algebraicStacksHom_ext B S hS
      (RelativeInertia.composition_pairIdInverse f.hom.hom.toFunctor 𝒳.val.val.p)) rfl rfl
        (SpacesOverStack.comp_comm_eq_eqToHom B S hS _ _ rfl rfl rfl rfl _)
        (SpacesOverStack.comp_comm_eq_eqToHom B S hS _ _ rfl rfl rfl rfl _)

/-- `c × id` has first projection `c` on the first two factors. -/
theorem homMk_compFstPair_comp_prodFst (f : 𝒳 ⟶ 𝒴) :
    IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (relativeInertiaCompFstPairHom B S hS f
      ≫ prodFst B S hS (relativeInertiaOverStack B S hS f) (relativeInertiaOverStack B S hS f)) =
      IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (prodFst B S hS (prodObj B S hS
        (relativeInertiaOverStack B S hS f) (relativeInertiaOverStack B S hS f))
        (relativeInertiaOverStack B S hS f) ≫ relativeInertiaMulHom B S hS f) :=
  SpacesOverStack.homMk_eq_of_comm_eqToHom B S hS rfl rfl rfl (SpacesOverStack.comp_comm_eq_eqToHom
    B S hS _ _ rfl rfl rfl rfl _) (SpacesOverStack.comp_comm_eq_eqToHom B S hS _ _ rfl rfl rfl rfl
    _)

/-- `(id × c) ∘ assoc` has first projection the first factor. -/
theorem homMk_idCompPair_comp_prodFst (f : 𝒳 ⟶ 𝒴) :
    IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (relativeInertiaIdCompPairHom B S hS f ≫
      prodFst B S hS (relativeInertiaOverStack B S hS f) (relativeInertiaOverStack B S hS f)) =
      IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (prodFst B S hS (prodObj B S hS
        (relativeInertiaOverStack B S hS f) (relativeInertiaOverStack B S hS f))
        (relativeInertiaOverStack B S hS f) ≫ prodFst B S hS (relativeInertiaOverStack B S hS f)
        (relativeInertiaOverStack B S hS f)) :=
  SpacesOverStack.homMk_eq_of_comm_eqToHom B S hS rfl rfl rfl (SpacesOverStack.comp_comm_eq_eqToHom
    B S hS _ _ rfl rfl rfl rfl _) (SpacesOverStack.comp_comm_eq_eqToHom B S hS _ _ rfl rfl rfl rfl
    _)

/-- **The associativity law for the composition law**, as an equality of isomorphism classes. -/
theorem homMk_compFstPair_comp_mul (f : 𝒳 ⟶ 𝒴) :
    IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (relativeInertiaCompFstPairHom B S hS f
      ≫ relativeInertiaMulHom B S hS f) =
      IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (relativeInertiaIdCompPairHom B S hS f
        ≫ relativeInertiaMulHom B S hS f) :=
  SpacesOverStack.homMk_eq_of_comm_eqToHom B S hS (algebraicStacksHom_ext B S hS
      (RelativeInertia.composition_assoc f.hom.hom.toFunctor 𝒳.val.val.p)) rfl rfl
        (SpacesOverStack.comp_comm_eq_eqToHom B S hS _ _ rfl rfl rfl rfl _)
        (SpacesOverStack.comp_comm_eq_eqToHom B S hS _ _ rfl rfl rfl rfl _)

/-- The whiskered filler along `c × id` is the filler of the outer 2-fibre product square. -/
theorem compFstPair_whiskerLeft_prodSnd_comm (f : 𝒳 ⟶ 𝒴) :
    (relativeInertiaCompFstPairHom B S hS f).map ◁ (prodSnd B S hS (relativeInertiaOverStack
      B S hS f) (relativeInertiaOverStack B S hS f)).comm = (prodSnd B S hS (prodObj B S hS
      (relativeInertiaOverStack B S hS f) (relativeInertiaOverStack B S hS f))
      (relativeInertiaOverStack B S hS f)).comm :=
  hom₂_ext_of_app B S hS fun _ => rfl

/-- The whiskered filler along `(id × c) ∘ assoc` is the comparison 2-morphism of
`(pr₂, pr₃)`. -/
theorem idCompPair_whiskerLeft_prodSnd_comm (f : 𝒳 ⟶ 𝒴) :
    (relativeInertiaIdCompPairHom B S hS f).map ◁ (prodSnd B S hS (relativeInertiaOverStack
      B S hS f) (relativeInertiaOverStack B S hS f)).comm =
      (relativeInertiaMidPairHom B S hS f).comm :=
  hom₂_ext_of_app B S hS fun _ => rfl

/-- The comparison 2-morphism of `(pr₂, pr₃)`, composed with the whiskered filler, is the filler
of the outer 2-fibre product square. -/
theorem midPair_comm_comp_whiskerLeft_prodSnd_comm (f : 𝒳 ⟶ 𝒴) :
    (relativeInertiaMidPairHom B S hS f).comm ≫
        ((relativeInertiaMidPairHom B S hS f).map ◁ (prodSnd B S hS (relativeInertiaOverStack
          B S hS f) (relativeInertiaOverStack B S hS f)).comm) = (prodSnd B S hS (prodObj B S hS
          (relativeInertiaOverStack B S hS f) (relativeInertiaOverStack B S hS f))
          (relativeInertiaOverStack B S hS f)).comm :=
  hom₂_ext_of_app B S hS fun _ => Iso.hom_inv_id_assoc _ _

/-- The comparison 2-morphism of `c × id` followed by the second projection. -/
theorem compFstPair_comp_prodSnd_comm (f : 𝒳 ⟶ 𝒴) :
    (relativeInertiaCompFstPairHom B S hS f ≫ prodSnd B S hS (relativeInertiaOverStack B S hS f)
      (relativeInertiaOverStack B S hS f)).comm = (prodSnd B S hS (prodObj B S hS
      (relativeInertiaOverStack B S hS f) (relativeInertiaOverStack B S hS f))
      (relativeInertiaOverStack B S hS f)).comm :=
  (SpacesOverStack.comp_comm_eq_whisker B S hS (relativeInertiaCompFstPairHom B S hS f)
      (prodSnd B S hS (relativeInertiaOverStack B S hS f) (relativeInertiaOverStack B S hS f)) rfl
        rfl).trans
    ((Category.id_comp _).trans (compFstPair_whiskerLeft_prodSnd_comm B S hS f))

/-- `c × id` has second projection the third factor. -/
theorem homMk_compFstPair_comp_prodSnd (f : 𝒳 ⟶ 𝒴) :
    IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳)
        (relativeInertiaCompFstPairHom B S hS f ≫ prodSnd B S hS (relativeInertiaOverStack B S hS f)
          (relativeInertiaOverStack B S hS f)) =
      IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (prodSnd B S hS (prodObj B S hS
        (relativeInertiaOverStack B S hS f) (relativeInertiaOverStack B S hS f))
        (relativeInertiaOverStack B S hS f)) :=
  SpacesOverStack.homMk_eq_of_comm_eq B S hS
    (relativeInertiaCompFstPairHom B S hS f ≫ prodSnd B S hS (relativeInertiaOverStack B S hS f)
      (relativeInertiaOverStack B S hS f)) (prodSnd B S hS (prodObj B S hS
      (relativeInertiaOverStack B S hS f) (relativeInertiaOverStack B S hS f))
      (relativeInertiaOverStack B S hS f))
    (algebraicStacksHom_ext B S hS (RelativeInertia.compFstPair_comp_snd f.hom.hom.toFunctor
      𝒳.val.val.p))
    ((Category.comp_id _).trans (compFstPair_comp_prodSnd_comm B S hS f))

/-- The comparison 2-morphism of `(pr₂, pr₃)` followed by the first projection. -/
theorem midPair_comp_prodFst_comm (f : 𝒳 ⟶ 𝒴) :
    (relativeInertiaMidPairHom B S hS f ≫ prodFst B S hS (relativeInertiaOverStack B S hS f)
      (relativeInertiaOverStack B S hS f)).comm = (prodFst B S hS (prodObj B S hS
      (relativeInertiaOverStack B S hS f) (relativeInertiaOverStack B S hS f))
      (relativeInertiaOverStack B S hS f) ≫ prodSnd B S hS (relativeInertiaOverStack B S hS f)
      (relativeInertiaOverStack B S hS f)).comm :=
  ((SpacesOverStack.comp_comm_eq B S hS (relativeInertiaMidPairHom B S hS f) (prodFst B S hS
    (relativeInertiaOverStack B S hS f) (relativeInertiaOverStack B S hS f))).trans
      ((congrArg (fun t => (relativeInertiaMidPairHom B S hS f).comm ≫ t)
          (whiskerLeft_id (relativeInertiaMidPairHom B S hS f).map
            (prodObj B S hS (relativeInertiaOverStack B S hS f) (relativeInertiaOverStack
              B S hS f)).map)).trans (Category.comp_id _))).trans
    ((SpacesOverStack.comp_comm_eq_whisker B S hS (prodFst B S hS (prodObj B S hS
      (relativeInertiaOverStack B S hS f) (relativeInertiaOverStack B S hS f))
      (relativeInertiaOverStack B S hS f)) (prodSnd B S hS (relativeInertiaOverStack B S hS f)
      (relativeInertiaOverStack B S hS f)) rfl rfl).trans
      (Category.id_comp _)).symm

/-- The comparison 2-morphism of `(pr₂, pr₃)` followed by the second projection. -/
theorem midPair_comp_prodSnd_comm (f : 𝒳 ⟶ 𝒴) :
    (relativeInertiaMidPairHom B S hS f ≫ prodSnd B S hS (relativeInertiaOverStack B S hS f)
      (relativeInertiaOverStack B S hS f)).comm = (prodSnd B S hS (prodObj B S hS
      (relativeInertiaOverStack B S hS f) (relativeInertiaOverStack B S hS f))
      (relativeInertiaOverStack B S hS f)).comm :=
  (SpacesOverStack.comp_comm_eq B S hS (relativeInertiaMidPairHom B S hS f) (prodSnd B S hS
    (relativeInertiaOverStack B S hS f) (relativeInertiaOverStack B S hS f))).trans
    (midPair_comm_comp_whiskerLeft_prodSnd_comm B S hS f)

/-- `(pr₂, pr₃)` has first projection the second factor. -/
theorem homMk_midPair_comp_prodFst (f : 𝒳 ⟶ 𝒴) :
    IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (relativeInertiaMidPairHom B S hS f ≫
      prodFst B S hS (relativeInertiaOverStack B S hS f) (relativeInertiaOverStack B S hS f)) =
      IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (prodFst B S hS (prodObj B S hS
      (relativeInertiaOverStack B S hS f) (relativeInertiaOverStack B S hS f))
      (relativeInertiaOverStack B S hS f) ≫ prodSnd B S hS (relativeInertiaOverStack B S hS f)
      (relativeInertiaOverStack B S hS f)) :=
  SpacesOverStack.homMk_eq_of_comm_eq B S hS
    (relativeInertiaMidPairHom B S hS f ≫ prodFst B S hS (relativeInertiaOverStack B S hS f)
      (relativeInertiaOverStack B S hS f)) (prodFst B S hS (prodObj B S hS
      (relativeInertiaOverStack B S hS f) (relativeInertiaOverStack B S hS f))
      (relativeInertiaOverStack B S hS f) ≫ prodSnd B S hS (relativeInertiaOverStack B S hS f)
      (relativeInertiaOverStack B S hS f))
    (algebraicStacksHom_ext B S hS (RelativeInertia.midPair_comp_fst f.hom.hom.toFunctor
      𝒳.val.val.p))
    ((Category.comp_id _).trans (midPair_comp_prodFst_comm B S hS f))

/-- `(pr₂, pr₃)` has second projection the third factor. -/
theorem homMk_midPair_comp_prodSnd (f : 𝒳 ⟶ 𝒴) :
    IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (relativeInertiaMidPairHom B S hS f ≫
      prodSnd B S hS (relativeInertiaOverStack B S hS f) (relativeInertiaOverStack B S hS f)) =
      IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (prodSnd B S hS (prodObj B S hS
      (relativeInertiaOverStack B S hS f) (relativeInertiaOverStack B S hS f))
      (relativeInertiaOverStack B S hS f)) :=
  SpacesOverStack.homMk_eq_of_comm_eq B S hS
    (relativeInertiaMidPairHom B S hS f ≫ prodSnd B S hS (relativeInertiaOverStack B S hS f)
      (relativeInertiaOverStack B S hS f)) (prodSnd B S hS (prodObj B S hS
      (relativeInertiaOverStack B S hS f) (relativeInertiaOverStack B S hS f))
      (relativeInertiaOverStack B S hS f))
    (algebraicStacksHom_ext B S hS (RelativeInertia.midPair_comp_snd f.hom.hom.toFunctor
      𝒳.val.val.p))
    ((Category.comp_id _).trans (midPair_comp_prodSnd_comm B S hS f))

/-- The comparison 2-morphism of `(id × c) ∘ assoc` followed by the second projection. -/
theorem idCompPair_comp_prodSnd_comm (f : 𝒳 ⟶ 𝒴) :
    (relativeInertiaIdCompPairHom B S hS f ≫ prodSnd B S hS (relativeInertiaOverStack B S hS f)
      (relativeInertiaOverStack B S hS f)).comm =
      (relativeInertiaMidPairHom B S hS f ≫ relativeInertiaMulHom B S hS f).comm :=
  ((SpacesOverStack.comp_comm_eq_whisker B S hS (relativeInertiaIdCompPairHom B S hS f)
        (prodSnd B S hS (relativeInertiaOverStack B S hS f) (relativeInertiaOverStack B S hS f))
          rfl rfl).trans
      ((Category.id_comp _).trans (idCompPair_whiskerLeft_prodSnd_comm B S hS f))).trans
    ((SpacesOverStack.comp_comm_eq B S hS (relativeInertiaMidPairHom B S hS f)
        (relativeInertiaMulHom B S hS f)).trans
      ((congrArg (fun t => (relativeInertiaMidPairHom B S hS f).comm ≫ t)
          (whiskerLeft_id (relativeInertiaMidPairHom B S hS f).map
            (prodObj B S hS (relativeInertiaOverStack B S hS f) (relativeInertiaOverStack
              B S hS f)).map)).trans (Category.comp_id _))).symm

/-- `(id × c) ∘ assoc` has second projection `c` on the last two factors. -/
theorem homMk_idCompPair_comp_prodSnd (f : 𝒳 ⟶ 𝒴) :
    IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳)
        (relativeInertiaIdCompPairHom B S hS f ≫ prodSnd B S hS (relativeInertiaOverStack B S hS f)
          (relativeInertiaOverStack B S hS f)) =
      IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳)
        (relativeInertiaMidPairHom B S hS f ≫ relativeInertiaMulHom B S hS f) :=
  SpacesOverStack.homMk_eq_of_comm_eq B S hS
    (relativeInertiaIdCompPairHom B S hS f ≫ prodSnd B S hS (relativeInertiaOverStack B S hS f)
      (relativeInertiaOverStack B S hS f))
    (relativeInertiaMidPairHom B S hS f ≫ relativeInertiaMulHom B S hS f)
    (algebraicStacksHom_ext B S hS (RelativeInertia.idCompPair_comp_snd f.hom.hom.toFunctor
      𝒳.val.val.p))
    ((Category.comp_id _).trans (idCompPair_comp_prodSnd_comm B S hS f))

section GroupObject

open scoped MonoidalCategory
open CartesianMonoidalCategory

/-- The neutral element composed with the map to the terminal object is the unit of the
group object, followed by `toUnit`. -/
private theorem homMk_toTerminalObj_comp_one (f : 𝒳 ⟶ 𝒴) :
    IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (toTerminalObj B S hS
      (relativeInertiaOverStack B S hS f) ≫ relativeInertiaOneHom B S hS f) =
      toUnit (IsoClassCategory.mk (relativeInertiaOverStack B S hS f)) ≫
        IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (relativeInertiaOneHom B S hS f) :=
  congrArg (fun t => t ≫ IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳)
    (relativeInertiaOneHom B S hS f)) (toUnit_unique (IsoClassCategory.homMk (C :=
    SpacesOverStack B S hS 𝒳) (toTerminalObj B S hS (relativeInertiaOverStack B S hS f)))
    (toUnit (IsoClassCategory.mk (relativeInertiaOverStack B S hS f))))

/-- `⟨e ∘ π, id⟩` is the lift of the neutral element and the identity. -/
theorem homMk_pairNeutralId_eq_lift (f : 𝒳 ⟶ 𝒴) :
    IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (relativeInertiaPairNeutralIdHom
      B S hS f) =
      lift (toUnit (IsoClassCategory.mk (relativeInertiaOverStack B S hS f)) ≫
        IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (relativeInertiaOneHom B S hS f)) (𝟙
        (IsoClassCategory.mk (relativeInertiaOverStack B S hS f))) :=
  SpacesOverStack.prod_hom_ext B S hS _ _
    ((homMk_pairNeutralId_comp_prodFst B S hS f).trans
      ((homMk_toTerminalObj_comp_one B S hS f).trans (lift_fst _ _).symm))
    ((homMk_pairNeutralId_comp_prodSnd B S hS f).trans (lift_snd _ _).symm)

/-- `⟨id, e ∘ π⟩` is the lift of the identity and the neutral element. -/
theorem homMk_pairIdNeutral_eq_lift (f : 𝒳 ⟶ 𝒴) :
    IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (relativeInertiaPairIdNeutralHom
      B S hS f) =
      lift (𝟙 (IsoClassCategory.mk (relativeInertiaOverStack B S hS f))) (toUnit
        (IsoClassCategory.mk (relativeInertiaOverStack B S hS f)) ≫ IsoClassCategory.homMk (C :=
        SpacesOverStack B S hS 𝒳) (relativeInertiaOneHom B S hS f)) :=
  SpacesOverStack.prod_hom_ext B S hS _ _
    ((homMk_pairIdNeutral_comp_prodFst B S hS f).trans (lift_fst _ _).symm)
    ((homMk_pairIdNeutral_comp_prodSnd B S hS f).trans
      ((homMk_toTerminalObj_comp_one B S hS f).trans (lift_snd _ _).symm))

/-- `⟨i, id⟩` is the lift of the inverse and the identity. -/
theorem homMk_pairInverseId_eq_lift (f : 𝒳 ⟶ 𝒴) :
    IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (relativeInertiaPairInverseIdHom
      B S hS f) = lift (IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳)
      (relativeInertiaInvHom B S hS f)) (𝟙 (IsoClassCategory.mk (relativeInertiaOverStack
        B S hS f))) :=
  SpacesOverStack.prod_hom_ext B S hS _ _
    ((homMk_pairInverseId_comp_prodFst B S hS f).trans (lift_fst _ _).symm)
    ((homMk_pairInverseId_comp_prodSnd B S hS f).trans (lift_snd _ _).symm)

/-- `⟨id, i⟩` is the lift of the identity and the inverse. -/
theorem homMk_pairIdInverse_eq_lift (f : 𝒳 ⟶ 𝒴) :
    IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (relativeInertiaPairIdInverseHom
      B S hS f) = lift (𝟙 (IsoClassCategory.mk (relativeInertiaOverStack B S hS f)))
      (IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (relativeInertiaInvHom B S hS f)) :=
  SpacesOverStack.prod_hom_ext B S hS _ _
    ((homMk_pairIdInverse_comp_prodFst B S hS f).trans (lift_fst _ _).symm)
    ((homMk_pairIdInverse_comp_prodSnd B S hS f).trans (lift_snd _ _).symm)

/-- `c × id` is the lift of `pr₁ ≫ c` and `pr₂`. -/
theorem homMk_compFstPair_eq_lift (f : 𝒳 ⟶ 𝒴) :
    IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (relativeInertiaCompFstPairHom B S hS f)
      =
      lift (fst (IsoClassCategory.mk (relativeInertiaOverStack B S hS f) ⊗ IsoClassCategory.mk
        (relativeInertiaOverStack B S hS f)) (IsoClassCategory.mk (relativeInertiaOverStack
          B S hS f)) ≫ IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (relativeInertiaMulHom
          B S hS f)) (snd (IsoClassCategory.mk (relativeInertiaOverStack B S hS f) ⊗
            IsoClassCategory.mk
        (relativeInertiaOverStack B S hS f)) (IsoClassCategory.mk (relativeInertiaOverStack
          B S hS f))) :=
  SpacesOverStack.prod_hom_ext B S hS _ _
    ((homMk_compFstPair_comp_prodFst B S hS f).trans (lift_fst _ _).symm)
    ((homMk_compFstPair_comp_prodSnd B S hS f).trans (lift_snd _ _).symm)

/-- `(pr₂, pr₃)` is the lift of `pr₁ ≫ pr₂` and `pr₂`. -/
theorem homMk_midPair_eq_lift (f : 𝒳 ⟶ 𝒴) :
    IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (relativeInertiaMidPairHom B S hS f) =
      lift (fst (IsoClassCategory.mk (relativeInertiaOverStack B S hS f) ⊗ IsoClassCategory.mk
        (relativeInertiaOverStack B S hS f)) (IsoClassCategory.mk (relativeInertiaOverStack
          B S hS f)) ≫ snd (IsoClassCategory.mk (relativeInertiaOverStack B S hS f))
          (IsoClassCategory.mk
        (relativeInertiaOverStack B S hS f))) (snd (IsoClassCategory.mk (relativeInertiaOverStack
          B S hS f) ⊗ IsoClassCategory.mk (relativeInertiaOverStack B S hS f)) (IsoClassCategory.mk
        (relativeInertiaOverStack B S hS f))) :=
  SpacesOverStack.prod_hom_ext B S hS _ _
    ((homMk_midPair_comp_prodFst B S hS f).trans (lift_fst _ _).symm)
    ((homMk_midPair_comp_prodSnd B S hS f).trans (lift_snd _ _).symm)

/-- `(id × c) ∘ assoc` is the lift of `pr₁ ≫ pr₁` and `(pr₂, pr₃) ≫ c`. -/
theorem homMk_idCompPair_eq_lift (f : 𝒳 ⟶ 𝒴) :
    IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (relativeInertiaIdCompPairHom B S hS f) =
      lift (fst (IsoClassCategory.mk (relativeInertiaOverStack B S hS f) ⊗ IsoClassCategory.mk
        (relativeInertiaOverStack B S hS f)) (IsoClassCategory.mk (relativeInertiaOverStack
          B S hS f)) ≫ fst (IsoClassCategory.mk (relativeInertiaOverStack B S hS f))
          (IsoClassCategory.mk
        (relativeInertiaOverStack B S hS f)))
        (IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (relativeInertiaMidPairHom B S hS f)
          ≫ IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (relativeInertiaMulHom B S hS f))
            :=
  SpacesOverStack.prod_hom_ext B S hS _ _
    ((homMk_idCompPair_comp_prodFst B S hS f).trans (lift_fst _ _).symm)
    ((homMk_idCompPair_comp_prodSnd B S hS f).trans (lift_snd _ _).symm)

/-- **Stacks 050R.** For a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks, the relative inertia
`I_{𝒳/𝒴}` is a *group object* of the category of 1-morphisms to `𝒳` representable by algebraic
spaces (Stacks 04ZQ): its multiplication is the composition law
`c : I_{𝒳/𝒴} ×_𝒳 I_{𝒳/𝒴} ⟶ I_{𝒳/𝒴}`, `((x, α), (x', α'), β) ↦ (x, α ∘ β⁻¹ ∘ α' ∘ β)`, its unit
is the neutral element `e : 𝒳 ⟶ I_{𝒳/𝒴}`, `x ↦ (x, id_x)`, and its inverse is
`i : (x, α) ↦ (x, α⁻¹)`. -/
@[instance_reducible, stacks 050R]
noncomputable def relativeInertiaGrpObj (f : 𝒳 ⟶ 𝒴) : GrpObj (IsoClassCategory.mk
  (relativeInertiaOverStack B S hS f)) where
  one := IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (relativeInertiaOneHom B S hS f)
  mul := IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (relativeInertiaMulHom B S hS f)
  inv := IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (relativeInertiaInvHom B S hS f)
  one_mul := one_mul_of_lift _ _
    ((congrArg (fun t => t ≫ IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳)
      (relativeInertiaMulHom B S hS f)) (homMk_pairNeutralId_eq_lift B S hS f).symm).trans
      (homMk_pairNeutralId_comp_mul B S hS f))
  mul_one := mul_one_of_lift _ _
    ((congrArg (fun t => t ≫ IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳)
      (relativeInertiaMulHom B S hS f)) (homMk_pairIdNeutral_eq_lift B S hS f).symm).trans
      (homMk_pairIdNeutral_comp_mul B S hS f))
  mul_assoc := mul_assoc_of_lift _
    ((congrArg (fun t => t ≫ IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳)
      (relativeInertiaMulHom B S hS f)) (homMk_compFstPair_eq_lift B S hS f).symm).trans
      ((homMk_compFstPair_comp_mul B S hS f).trans
        ((congrArg (fun t => t ≫ IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳)
          (relativeInertiaMulHom B S hS f)) (homMk_idCompPair_eq_lift B S hS f)).trans
          (congrArg (fun t => lift (fst (IsoClassCategory.mk (relativeInertiaOverStack B S hS f) ⊗
            IsoClassCategory.mk (relativeInertiaOverStack B S hS f)) (IsoClassCategory.mk
            (relativeInertiaOverStack B S hS f)) ≫ fst (IsoClassCategory.mk
            (relativeInertiaOverStack B S hS f)) (IsoClassCategory.mk (relativeInertiaOverStack
              B S hS f)))
              (t ≫ IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (relativeInertiaMulHom
                B S hS f)) ≫ IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳)
                (relativeInertiaMulHom B S hS f)) (homMk_midPair_eq_lift B S hS f)))))
  left_inv :=
    (congrArg (fun t => t ≫ IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳)
      (relativeInertiaMulHom B S hS f)) (homMk_pairInverseId_eq_lift B S hS f).symm).trans
      ((homMk_pairInverseId_comp_mul B S hS f).trans
        (congrArg (fun t => t ≫ IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳)
          (relativeInertiaOneHom B S hS f)) (toUnit_unique (IsoClassCategory.homMk (C :=
          SpacesOverStack B S hS 𝒳) (toTerminalObj B S hS (relativeInertiaOverStack B S hS f)))
          (toUnit (IsoClassCategory.mk (relativeInertiaOverStack B S hS f))))))
  right_inv :=
    (congrArg (fun t => t ≫ IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳)
      (relativeInertiaMulHom B S hS f)) (homMk_pairIdInverse_eq_lift B S hS f).symm).trans
      ((homMk_pairIdInverse_comp_mul B S hS f).trans
        (congrArg (fun t => t ≫ IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳)
          (relativeInertiaOneHom B S hS f)) (toUnit_unique (IsoClassCategory.homMk (C :=
          SpacesOverStack B S hS 𝒳) (toTerminalObj B S hS (relativeInertiaOverStack B S hS f)))
          (toUnit (IsoClassCategory.mk (relativeInertiaOverStack B S hS f))))))


/-- **Stacks 050R.** The multiplication of the group object is the composition law `c`. -/
@[stacks 050R "the multiplication of the group object is the composition law"]
theorem relativeInertiaGrpObj_mul (f : 𝒳 ⟶ 𝒴) :
    letI := relativeInertiaGrpObj B S hS f
    MonObj.mul (X := IsoClassCategory.mk (relativeInertiaOverStack B S hS f)) =
      IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (relativeInertiaMulHom B S hS f) := rfl

/-- **Stacks 050R.** The unit of the group object is the neutral element `e`. -/
@[stacks 050R "the unit of the group object is the neutral element"]
theorem relativeInertiaGrpObj_one (f : 𝒳 ⟶ 𝒴) :
    letI := relativeInertiaGrpObj B S hS f
    MonObj.one (X := IsoClassCategory.mk (relativeInertiaOverStack B S hS f)) =
      IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (relativeInertiaOneHom B S hS f) := rfl

/-- **Stacks 050R.** The inverse of the group object is `i`. -/
@[stacks 050R "the inverse of the group object"]
theorem relativeInertiaGrpObj_inv (f : 𝒳 ⟶ 𝒴) :
    GrpObj.inv (X := IsoClassCategory.mk (relativeInertiaOverStack B S hS f)) (self :=
      relativeInertiaGrpObj B S hS f) =
      IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (relativeInertiaInvHom B S hS f) := rfl

end GroupObject

end AlgebraicGeometry.Stack

end
