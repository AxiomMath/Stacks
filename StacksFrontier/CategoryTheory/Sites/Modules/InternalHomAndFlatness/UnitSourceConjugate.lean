module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomMapLeftConjugate
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.PullbackInternalHomFlat

/-!
# The trivialisation of `ℰom_O(O, -)` is the conjugate of the left unitor

Let `(C, J, O)` be a ringed site. The clause of [Stacks, Tag 03EM] which says that a local
homomorphism `O|_U ⟶ G|_U` is its value at the unit section is the isomorphism of functors
`Stacks.SheafOfModules.InternalHom.internalHomSecondFunctorUnitIso`,

`ℰom_O(O, -) ≅ 𝟭`.

Both sides are right adjoints: the left-hand side is right adjoint to `O ⊗_O -` by the sheaf
clause of [Stacks, Tag 03EO]
(`Stacks.SheafOfModules.InternalHom.tensorLeftAdjunction`), and the identity functor is right
adjoint to itself. **This file identifies the trivialisation as the conjugate of the left
unitor**: of the isomorphism of left adjoints `𝟭 ≅ O ⊗_O -` which is the inverse of the left
unitor of the monoidal structure, read at the structure sheaf through
`SheafOfModules.unitIso`.

This is the shape in which the trivialisation enters a computation of the underived form of
[Stacks, Tag 0E2I] at the source `O_Z`: that isomorphism is also a conjugate, of the projection
formula (`…ClosedQuotientMorphismOfRingedSpaces.sheafHomPushforwardNatIso_hom`), and conjugation
turns a composite of transformations of right adjoints into a composite of transformations of
left adjoints (`CategoryTheory.conjugateEquiv_comp`). So a statement about the trivialisation
composed with the 0E2I isomorphism becomes a statement about tensor functors.

## Main results

* `CategoryTheory.counit_eq_conjugateEquiv_unit`: the counit of an adjunction `R₁ ⊣ R₂` is the
  conjugate of the unit of an adjunction `L₁ ⊣ R₁` on its left, for the composite adjunction.
  In the application this says the trace `i_* ℰom(O_Z, -) ⟶ 𝟭` of [Stacks, Tag 0A75] is the
  conjugate of the unit `𝟭 ⟶ i_* i^*`.
* `CategoryTheory.conjugateEquiv_ofNatIsoLeft`: re-seating the left adjoint of an adjunction
  along an isomorphism precomposes the conjugated transformation with that isomorphism. This is
  what crosses between `Stacks.SheafOfModules.InternalHom.tensorLeftAdjunction`, whose left
  adjoint is the `tensorLeft` of the localized monoidal structure, and
  `Stacks.SheafOfModules.InternalHom.sheafTensorHomAdjunction`, whose left adjoint is
  `Stacks.SheafOfModules.Tensor.sheafTensor`; the two adjunctions are the same one re-seated,
  and the underived 0E2I isomorphism is stated over the second.
* `Stacks.SheafOfModules.InternalHom.internalHomSecondFunctorUnitIso_hom_eq`: **the
  trivialisation of `ℰom_O(O, -)` is the conjugate of the inverse left unitor**, for the
  adjunction whose left adjoint is `tensorLeft O`.
* `Stacks.SheafOfModules.InternalHom.internalHomSecondFunctorUnitIso_hom_eq_sheafTensor`: the
  same over the adjunction whose left adjoint is `Stacks.SheafOfModules.Tensor.sheafTensor`.
* `Stacks.SheafOfModules.InternalHom.internalHomSecondFunctorUnitIso_hom_app_eq`: the component
  at `G`, which is the inverse unitor at the internal Hom sheaf followed by the counit of
  [Stacks, Tag 03EO] — the evaluation map.

## Implementation notes

The three factors of `internalHomSecondFunctorUnitIso` are each already a conjugate: the bridge
`Stacks.SheafOfModules.InternalHom.ihomIsoInternalHomSecondFunctor` is
`CategoryTheory.Adjunction.rightAdjointUniq`, hence `CategoryTheory.conjugateIsoEquiv` at the
identity; `CategoryTheory.MonoidalClosed.pre`, which is what `MonoidalClosed.internalHom` does
on morphisms, is by definition the conjugate of the tensor whiskering; and
`CategoryTheory.MonoidalClosed.unitNatIso` is by definition the conjugate isomorphism of the
left unitor. So the identity is `CategoryTheory.conjugateEquiv_comp` twice, the three
transformations of left adjoints being an identity, the whiskering of the unit comparison, and
the inverse left unitor.

## References

* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
* [Stacks Project, Tag 0E2I](https://stacks.math.columbia.edu/tag/0E2I)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

noncomputable section

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

/-- **Re-seating the left adjoint precomposes the conjugate.** For an adjunction `L₁ ⊣ R₁`, an
isomorphism `e : L₁ ≅ L₁'` and an adjunction `L₂ ⊣ R₂`, the conjugate of `α : L₂ ⟶ L₁'` taken
for the re-seated adjunction `CategoryTheory.Adjunction.ofNatIsoLeft` is the conjugate of
`α ≫ e.inv` taken for the original one.

Both are transformations `R₁ ⟶ R₂`, and a conjugate is pinned down by its compatibility with
the two hom-equivalences (`CategoryTheory.conjugateEquiv_eq_of_homEquiv`); the
hom-equivalence of the re-seated adjunction precomposes with `e`
(`CategoryTheory.Adjunction.homEquiv_ofNatIsoLeft_apply`), which is exactly the discrepancy. -/
theorem conjugateEquiv_ofNatIsoLeft {L₁ L₁' L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (e : L₁ ≅ L₁') (α : L₂ ⟶ L₁') :
    conjugateEquiv (Adjunction.ofNatIsoLeft adj₁ e) adj₂ α =
      conjugateEquiv adj₁ adj₂ (α ≫ e.inv) :=
  (conjugateEquiv_eq_of_homEquiv adj₁ adj₂ (α ≫ e.inv)
    (conjugateEquiv (Adjunction.ofNatIsoLeft adj₁ e) adj₂ α) (fun c X f => by
      have key := homEquiv_comp_conjugateEquiv (Adjunction.ofNatIsoLeft adj₁ e) adj₂ α c X
        (e.inv.app c ≫ f)
      rw [Adjunction.homEquiv_ofNatIsoLeft_apply adj₁ e (e.inv.app c ≫ f),
        Iso.hom_inv_id_app_assoc] at key
      rw [key, NatTrans.comp_app, Category.assoc])).symm

/-- **The counit of an adjunction is the conjugate of the unit of an adjunction on its left.**
Let `L₁ ⊣ R₁` and `R₁ ⊣ R₂` be adjunctions, so that `R₁` is both the right adjoint of the first
and the left adjoint of the second. The counit `R₂ ⋙ R₁ ⟶ 𝟭` of the second adjunction is the
conjugate, for the composite adjunction `L₁ ⋙ R₁ ⊣ R₂ ⋙ R₁` and the identity adjunction, of
the unit `𝟭 ⟶ L₁ ⋙ R₁` of the first.

In the application `R₁` is the direct image `i_*` of a closed quotient morphism, `L₁` the
pullback `i^*` and `R₂` the sheaf Hom with exact support of [Stacks, Tag 0A75]: the trace
`i_* ℰom(𝒪_Z, -) ⟶ 𝟭` is the conjugate of the unit `𝟭 ⟶ i_* i^*`.

Componentwise this is one triangle identity: the conjugate of `α` for the identity adjunction
has component `α` at the right adjoint followed by the counit
(`CategoryTheory.conjugateEquiv_adjunction_id`), the counit of a composite adjunction is
`CategoryTheory.Adjunction.comp_counit_app`, and what is left in front of `adj₂.counit` is the
right triangle of `adj₁`. -/
theorem counit_eq_conjugateEquiv_unit {L₁ : C ⥤ D} {R₁ : D ⥤ C} {R₂ : C ⥤ D}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : R₁ ⊣ R₂) :
    adj₂.counit = conjugateEquiv (adj₁.comp adj₂) Adjunction.id adj₁.unit := by
  refine NatTrans.ext (funext fun c => ?_)
  rw [conjugateEquiv_adjunction_id, Adjunction.comp_counit_app, ← Category.assoc,
    show adj₁.unit.app ((R₂ ⋙ R₁).obj c) ≫ R₁.map (adj₁.counit.app (R₂.obj c)) = 𝟙 _ from
      adj₁.right_triangle_components (R₂.obj c),
    Category.id_comp]

section MonoidalConjugates

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

omit [MonoidalCategory C] in
/-- **The comparison of two right adjoints of one functor is the conjugate of the identity**,
read backwards. This is `CategoryTheory.Adjunction.rightAdjointUniq` unfolded to the
`CategoryTheory.conjugateEquiv` it is defined to be, so that it composes with other conjugates
by `CategoryTheory.conjugateEquiv_comp`. -/
theorem rightAdjointUniq_inv_eq_conjugateEquiv {D : Type u₂} [Category.{v₂} D] {F : C ⥤ D}
    {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G') :
    (Adjunction.rightAdjointUniq adj1 adj2).inv = conjugateEquiv adj2 adj1 (𝟙 F) :=
  rfl

/-- **Precomposition on the internal hom is the conjugate of the tensor whiskering**, which is
what `CategoryTheory.MonoidalClosed.pre` is defined to be. -/
theorem pre_eq_conjugateEquiv {A B : C} [Closed A] [Closed B] (f : B ⟶ A) :
    MonoidalClosed.pre f =
      conjugateEquiv (ihom.adjunction A) (ihom.adjunction B) ((tensoringLeft C).map f) :=
  rfl

/-- **The trivialisation of the internal hom out of the monoidal unit is the conjugate of the
left unitor**, which is what `CategoryTheory.MonoidalClosed.unitNatIso` is defined to be. -/
theorem unitNatIso_inv_eq_conjugateEquiv [Closed (𝟙_ C)] :
    (MonoidalClosed.unitNatIso (C := C)).inv =
      conjugateEquiv (ihom.adjunction (𝟙_ C)) Adjunction.id (leftUnitorNatIso C).inv :=
  rfl

/-- **The trivialisation of an internal hom at a trivialised source is the conjugate of the
inverse left unitor.** Let `A` be an object of a monoidal closed category with a chosen
right adjoint `R` of `A ⊗ -`, and let `f : 𝟙_ ⟶ A`. Comparing `R` with the internal hom
`ihom A`, precomposing with `f` on the internal hom, and trivialising the internal hom out of
the monoidal unit gives a transformation `R ⟶ 𝟭`; it is the conjugate of the transformation
`𝟭 ⟶ A ⊗ -` which is the inverse left unitor followed by `f ⊗ -`.

Each of the three factors is a `CategoryTheory.conjugateEquiv` by definition
(`CategoryTheory.rightAdjointUniq_inv_eq_conjugateEquiv`,
`CategoryTheory.pre_eq_conjugateEquiv`, `CategoryTheory.unitNatIso_inv_eq_conjugateEquiv`), so
this is `CategoryTheory.conjugateEquiv_comp` twice.

Stated over an abstract `adj` and at a bare monoidal closed category on purpose: at the monoidal
closed structure on sheaves of modules the same three rewrites are refused, the goal having two
spellings of the sheaf condition on the unit which are not interchangeable at the transparency
`rw` type-checks its motive at. -/
theorem rightAdjointUniq_inv_comp_pre_comp_unitNatIso_inv [MonoidalClosed C]
    {A : C} {R : C ⥤ C} (adj : tensorLeft A ⊣ R) (f : 𝟙_ C ⟶ A) :
    (Adjunction.rightAdjointUniq (ihom.adjunction A) adj).inv ≫
        (MonoidalClosed.pre f ≫ (MonoidalClosed.unitNatIso (C := C)).inv) =
      conjugateEquiv adj Adjunction.id
        ((leftUnitorNatIso C).inv ≫ (tensoringLeft C).map f) := by
  rw [rightAdjointUniq_inv_eq_conjugateEquiv, pre_eq_conjugateEquiv,
    unitNatIso_inv_eq_conjugateEquiv, conjugateEquiv_comp, conjugateEquiv_comp,
    Category.comp_id]

end MonoidalConjugates

end CategoryTheory

namespace Stacks.SheafOfModules.InternalHom

universe u

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (O : Sheaf J CommRingCat.{u})
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] _root_.SheafOfModules.monoidalCategory
  _root_.SheafOfModules.monoidalClosed

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The trivialisation of `ℰom_O(O, -)` is the conjugate of the inverse left unitor.** The
isomorphism `ℰom_O(O, -) ≅ 𝟭` of [Stacks, Tag 03EM] is a comparison of two right adjoints — of
`O ⊗_O -` and of the identity functor — and it is the one conjugate to the isomorphism of left
adjoints `𝟭 ≅ O ⊗_O -` given by the inverse left unitor read at the structure sheaf through
`SheafOfModules.unitIso`.

This is the generic `CategoryTheory.rightAdjointUniq_inv_comp_pre_comp_unitNatIso_inv` at the
adjunction `Stacks.SheafOfModules.InternalHom.tensorLeftAdjunction` and the morphism
`SheafOfModules.unitIso`: the trivialisation *is*, by definition, the three factors that lemma
composes. -/
theorem internalHomSecondFunctorUnitIso_hom_eq :
    (internalHomSecondFunctorUnitIso O).hom =
      conjugateEquiv
        (tensorLeftAdjunction O
          (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)))
        Adjunction.id
        ((leftUnitorNatIso _).inv ≫
          (tensoringLeft _).map (_root_.SheafOfModules.unitIso O).hom) :=
  rightAdjointUniq_inv_comp_pre_comp_unitNatIso_inv
    (tensorLeftAdjunction O
      (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)))
    (_root_.SheafOfModules.unitIso O).hom

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The trivialisation of `ℰom_O(O, -)`, as a conjugate for the adjunction of
[Stacks, Tag 03EO] in the spelling `Stacks.SheafOfModules.Tensor.sheafTensor`.** This is the
spelling the underived form of [Stacks, Tag 0E2I] is stated over, so this is the form in which
the trivialisation composes with it. -/
theorem internalHomSecondFunctorUnitIso_hom_eq_sheafTensor :
    (internalHomSecondFunctorUnitIso O).hom =
      conjugateEquiv
        (sheafTensorHomAdjunction O
          (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)))
        Adjunction.id
        (((leftUnitorNatIso _).inv ≫
            (tensoringLeft _).map (_root_.SheafOfModules.unitIso O).hom) ≫
          (_root_.SheafOfModules.sheafTensorIsoApp O
            (_root_.SheafOfModules.unit
              ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O))).hom) := by
  refine Eq.trans (internalHomSecondFunctorUnitIso_hom_eq O) ?_
  exact conjugateEquiv_ofNatIsoLeft
    (sheafTensorHomAdjunction O
      (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)))
    Adjunction.id
    (_root_.SheafOfModules.sheafTensorIsoApp O
      (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O))).symm
    ((leftUnitorNatIso _).inv ≫
      (tensoringLeft _).map (_root_.SheafOfModules.unitIso O).hom)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The component of the trivialisation of `ℰom_O(O, -)` at `G`**: the inverse left unitor at
the internal Hom sheaf, followed by the counit of the adjunction of [Stacks, Tag 03EO], which is
the evaluation map `O ⊗_O ℰom_O(O, G) ⟶ G`. -/
theorem internalHomSecondFunctorUnitIso_hom_app_eq
    (G : _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) :
    (internalHomSecondFunctorUnitIso O).hom.app G =
      ((leftUnitorNatIso _).inv ≫
            (tensoringLeft _).map (_root_.SheafOfModules.unitIso O).hom).app
          ((internalHomSecondFunctor.{u, u, u, u} J O
            (_root_.SheafOfModules.unit
              ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O))).obj G) ≫
        (tensorLeftAdjunction O
          (_root_.SheafOfModules.unit
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O))).counit.app G :=
  Eq.trans (congrArg (fun t => NatTrans.app t G) (internalHomSecondFunctorUnitIso_hom_eq O))
    (conjugateEquiv_adjunction_id _ _ G)

end Stacks.SheafOfModules.InternalHom

end

end
