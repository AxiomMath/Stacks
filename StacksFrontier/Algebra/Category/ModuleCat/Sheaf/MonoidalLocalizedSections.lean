module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalInduced
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAssociatorSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TwistSectionRing
public import StacksFrontier.AlgebraicGeometry.SheafInternalHom.Basic
public import StacksFrontier.CategoryTheory.Localization.MonoidalUnitObject

/-!
# The constraints of the localized monoidal structure on a product section

`Stacks.SheafOfModules.monoidalCategory` is the monoidal structure on sheaves of `𝒪`-modules
obtained by localizing the objectwise one on presheaves of modules along sheafification. Its
tensor product is only *isomorphic* to the tensor product sheaf
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf` of Tag 05NA, by
`Stacks.SheafOfModules.tensorObjIso`, so its three constraints `α_`, `λ_`, `ρ_` and its two
whiskerings had no description on sections: a section of `M ⊗ N` is not of the form
`Stacks.SheafOfModules.tensorSectionsAt`, which is a section of
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf 𝒪 h𝒪 M N`.

**This file supplies those descriptions**, with the crossing `tensorObjIso` written into each
statement. They are what turns an equation between morphisms of the localized structure into a
statement about a section; the equation this development needs is
`Stacks.ProjBundleInverseBaseChange.inverseQuotientBaseChangeIso_evaluation`, the evaluation
normalisation of the comparison of two tensor inverses, whose three constraints are exactly
these.

Nothing new is computed. The tensor product of two morphisms is
`Stacks.SheafOfModules.sheafifyTensorHom_eq_comparison` read against
`Stacks.SheafOfModules.tensorSections_tensorMapAt`, and the two whiskerings follow from it by
`MonoidalCategory.id_tensorHom` and `tensorHom_id`. The three constraints are the conjugation
identities `Stacks.SheafOfModules.Strict.associator_eq`, `Strict.leftUnitor_eq` and
`Strict.rightUnitor_eq` — each a `rfl` — read against the section formulas of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAssociatorSections` for the *strict*
structure, whose tensor product is the tensor product sheaf on the nose. The braiding goes
through `Stacks.SheafOfModules.tensorObjIso_braiding` and
`Stacks.SheafOfModules.tensorSections_braidingAt` instead, there being no braiding formula for
the strict structure.

## Main results

* `Stacks.SheafOfModules.tensorSectionsAt_localizedTensorHom`,
  `tensorSectionsAt_localizedWhiskerLeft` and `tensorSectionsAt_localizedWhiskerRight`: the
  tensor product of two morphisms and the two whiskerings act factorwise on a product section.
* `Stacks.SheafOfModules.tensorSectionsAt_localizedLeftUnitor` and
  `tensorSectionsAt_localizedRightUnitor`: **the unit constraints on a product section**,
  `r ⊗ x ↦ r • x`.
* `Stacks.SheafOfModules.tensorSectionsAt_localizedAssociator` and
  `tensorSectionsAt_localizedAssociator_inv`: **the associativity constraint on a triple product
  section**, in both directions. The crossings are `Stacks.SheafOfModules.tensorObjIsoLeft` and
  `tensorObjIsoRight`, the comparisons of the two threefold tensor products of the localized
  structure with the two threefold tensor product sheaves.
* `Stacks.SheafOfModules.tensorSectionsAt_localizedBraiding`: the braiding exchanges the two
  factors.
* `Stacks.SheafOfModules.tensorSectionsAt_sheafInternalHomRightUnitor` and
  `tensorSectionsAt_sheafInternalHomLeftUnitor`: **the two unit constraints of the other choice
  of unit object on a product section**, through
  `CategoryTheory.Localization.Monoidal.rightUnitor_hom_eq_of_unitIso`.
* `Stacks.SheafOfModules.tensorObjIsoLeft_inv_tensorSectionsAt` and
  `tensorObjIsoRight_inv_tensorSectionsAt`: **the threefold crossings in terms of the twofold
  one**, which is what lets the associator formula be chained with the two whiskerings.
* `Stacks.SheafOfModules.tensorSectionsAt_sheafInternalHomAssociator`: the associativity
  constraint of the other choice of unit object, in the forward direction.
* `Stacks.SheafOfModules.tensorSectionsAt_sheafInternalHomRightUnitor_one`,
  `tensorSectionsAt_sheafInternalHomLeftUnitor_one` and
  `tensorSectionsAt_sheafInternalHomLeftUnitor_inv_one`: **the two unit constraints at a section
  of the unit object that crosses to `1`**, where they are the identity.

## Implementation notes

The localized structure is the only monoidal structure left to instance synthesis, by
`attribute [local instance] monoidalCategory`; the strict structure of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrict` appears only through its
`CategoryTheory.MonoidalCategoryStruct` fields, by `@`-application or through the conjugation
identities, so the two never compete. This is the discipline of `MonoidalStrict` itself, and the
reason its conjugation identities are stated with
`(self := Stacks.SheafOfModules.Strict.monoidalCategoryStruct 𝒪 h𝒪)`.

Each statement names the crossing in the *inverse* direction, `tensorObjIso.inv` applied to a
product section, because that is the direction a consumer meets: the section it holds is a
product section of a tensor product *sheaf*, and the morphism it wants to apply lives on the
localized tensor product. `Stacks.SheafOfModules.crossedMorphism_val_app` is the one step every
proof here consists of — cancel the crossing on the target, recognise the conjugate, apply the
section formula — and is stated once rather than repeated six times.

**Why the threefold crossings have to be rewritten.** The associator formula states its source
through `Stacks.SheafOfModules.tensorObjIsoLeft`, a crossing of `(M ⊗ N) ⊗ P` with the twice
iterated tensor product *sheaf*, while the whiskering formulas state theirs through
`tensorObjIso` of `M ⊗ N` with `P` — the inner factor crossed, the outer one not. The two are
not the same term, so a computation that whiskers into one factor and then reassociates cannot
chain the formulas as they stand. `tensorObjIsoLeft_inv_tensorSectionsAt` and its right
counterpart are that rewriting, and they are the tensor product of two morphisms — the crossing
in one factor and the identity in the other — read on a product section.

`Stacks.SheafOfModules.tensorSectionsAt_eq` is a `rfl`: `tensorSectionsAt` is by definition the
image of a pure tensor under the sheafification unit, which is the spelling
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAssociatorSections` uses. It is named rather
than left to conversion so that a caller mixing the two spellings has something to cite.

## References

* [The Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [The Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite

open scoped TensorProduct

universe v u w

namespace Stacks.SheafOfModules

open Stacks.SheafOfModules.TensorSheafification

attribute [local instance] monoidalCategoryPresheafOfModules symmetricCategoryPresheafOfModules

-- The tensor product sheaf is spelled `Stacks.SheafOfModules.Tensor.sheafTensor` applied to the
-- sheaf of rings `⟨O, _⟩`, whose modules are over `Stacks.SheafOfModules.Tensor.ringSheaf ⟨O, _⟩`,
-- while the binders below are over
-- `Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO`. The two are the same sheaf of
-- rings; this makes instance search cross between the spellings.
attribute [local implicit_reducible] Stacks.SheafOfModules.TensorSheafification.structureSheaf
  Stacks.SheafOfModules.Tensor.ringSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- A morphism read through a crossing on each side, on a section. If conjugating `φ` by `iA`
and `iB` is `ψ`, and `ψ` carries `x` to `y`, then `φ` carries the image of `x` under `iA.inv` to
the image of `y` under `iB.inv`.

This is the single step each formula below consists of: the crossings are
`Stacks.SheafOfModules.tensorObjIso`, `φ` is a morphism of the localized monoidal structure and
`ψ` the corresponding morphism of the tensor product sheaf, whose value on a product section is
known. -/
theorem crossedMorphism_val_app {A B A' B' : SheafOfModules.{w} (structureSheaf O hO)}
    (iA : A ≅ A') (iB : B ≅ B') (φ : A ⟶ B) (ψ : A' ⟶ B')
    (h : iA.inv ≫ φ ≫ iB.hom = ψ) (U : Cᵒᵖ) (x : A'.val.obj U) (y : B'.val.obj U)
    (hy : ψ.val.app U x = y) :
    φ.val.app U (iA.inv.val.app U x) = iB.inv.val.app U y :=
  (inv_val_app_hom_val_app iB U (φ.val.app U (iA.inv.val.app U x))).symm.trans
    (congrArg (iB.inv.val.app U)
      ((congrArg (fun θ : A' ⟶ B' => θ.val.app U x) h).trans hy))

/-- `Stacks.SheafOfModules.tensorSectionsAt` is the image of a pure tensor of local sections
under the unit of the sheafification adjunction, which is the spelling the section formulas of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAssociatorSections` are stated in. -/
theorem tensorSectionsAt_eq (U : Cᵒᵖ) (F G : SheafOfModules.{w} (structureSheaf O hO))
    (s : F.val.obj U) (t : G.val.obj U) :
    tensorSectionsAt O hO U F G s t = (toSheafify O hO (F.val ⊗ G.val)).app U (s ⊗ₜ t) :=
  rfl

attribute [local instance] monoidalCategory braidedCategory symmetricCategory

/-! ### The tensor product of two morphisms, and the two whiskerings -/

/-- **The tensor product of two morphisms of the localized structure on a product section.** It
acts factorwise.

This is `Stacks.SheafOfModules.sheafifyTensorHom_eq_comparison` read against
`Stacks.SheafOfModules.tensorSections_tensorMapAt`. -/
theorem tensorSectionsAt_localizedTensorHom
    {M M' N N' : SheafOfModules.{w} (structureSheaf O hO)} (f : M ⟶ M') (g : N ⟶ N')
    (U : Cᵒᵖ) (s : M.val.obj U) (t : N.val.obj U) :
    (f ⊗ₘ g).val.app U
        ((tensorObjIso O hO M N).inv.val.app U (tensorSectionsAt O hO U M N s t)) =
      (tensorObjIso O hO M' N').inv.val.app U
        (tensorSectionsAt O hO U M' N' (f.val.app U s) (g.val.app U t)) :=
  crossedMorphism_val_app O hO (tensorObjIso O hO M N) (tensorObjIso O hO M' N') (f ⊗ₘ g)
    (sheafifyTensorHom O hO f g) (sheafifyTensorHom_eq_comparison O hO f g).symm U _ _
    (tensorSections_tensorMapAt O hO U M M' N N' f g s t)

/-- **Left whiskering of the localized structure on a product section**: it acts through the
second factor alone. This is
`Stacks.SheafOfModules.tensorSectionsAt_localizedTensorHom` at the identity of the first factor,
through `MonoidalCategory.id_tensorHom`. -/
theorem tensorSectionsAt_localizedWhiskerLeft (M : SheafOfModules.{w} (structureSheaf O hO))
    {N N' : SheafOfModules.{w} (structureSheaf O hO)} (g : N ⟶ N') (U : Cᵒᵖ)
    (s : M.val.obj U) (t : N.val.obj U) :
    (M ◁ g).val.app U
        ((tensorObjIso O hO M N).inv.val.app U (tensorSectionsAt O hO U M N s t)) =
      (tensorObjIso O hO M N').inv.val.app U
        (tensorSectionsAt O hO U M N' s (g.val.app U t)) :=
  by
  rw [← MonoidalCategory.id_tensorHom]
  exact tensorSectionsAt_localizedTensorHom O hO (𝟙 M) g U s t

/-- **Right whiskering of the localized structure on a product section**, the companion of
`Stacks.SheafOfModules.tensorSectionsAt_localizedWhiskerLeft`. -/
theorem tensorSectionsAt_localizedWhiskerRight
    {M M' : SheafOfModules.{w} (structureSheaf O hO)} (f : M ⟶ M')
    (N : SheafOfModules.{w} (structureSheaf O hO)) (U : Cᵒᵖ)
    (s : M.val.obj U) (t : N.val.obj U) :
    (f ▷ N).val.app U
        ((tensorObjIso O hO M N).inv.val.app U (tensorSectionsAt O hO U M N s t)) =
      (tensorObjIso O hO M' N).inv.val.app U
        (tensorSectionsAt O hO U M' N (f.val.app U s) t) :=
  by
  rw [← MonoidalCategory.tensorHom_id]
  exact tensorSectionsAt_localizedTensorHom O hO f (𝟙 N) U s t

/-! ### The unit constraints -/

/-- **The left unit constraint of the localized structure on a product section**: the section
determined by a section `r` of the structure sheaf and a section `m` goes to `r • m`.

This is `Stacks.SheafOfModules.Strict.leftUnitor_eq`, which is a `rfl`, read against
`Stacks.SheafOfModules.leftUnitor_hom_val_app_tmul`. -/
theorem tensorSectionsAt_localizedLeftUnitor (M : SheafOfModules.{w} (structureSheaf O hO))
    (U : Cᵒᵖ) (r : (structureSheaf O hO).obj.obj U) (m : M.val.obj U) :
    (λ_ M).hom.val.app U
        ((tensorObjIso O hO (SheafOfModules.unit (structureSheaf O hO)) M).inv.val.app U
          (tensorSectionsAt O hO U (SheafOfModules.unit (structureSheaf O hO)) M r m)) =
      r • m :=
  (congrArg (fun i : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O,
      Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
      (SheafOfModules.unit (structureSheaf O hO))).obj (M)) ≅ M =>
      i.hom.val.app U
        (tensorSectionsAt O hO U (SheafOfModules.unit (structureSheaf O hO)) M r m))
    (Strict.leftUnitor_eq O hO M)).symm.trans
    (leftUnitor_hom_val_app_tmul O hO M U r m)

/-- **The right unit constraint of the localized structure on a product section.** -/
theorem tensorSectionsAt_localizedRightUnitor (M : SheafOfModules.{w} (structureSheaf O hO))
    (U : Cᵒᵖ) (m : M.val.obj U) (r : (structureSheaf O hO).obj.obj U) :
    (ρ_ M).hom.val.app U
        ((tensorObjIso O hO M (SheafOfModules.unit (structureSheaf O hO))).inv.val.app U
          (tensorSectionsAt O hO U M (SheafOfModules.unit (structureSheaf O hO)) m r)) =
      r • m :=
  (congrArg (fun i : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O,
      Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (M)).obj
      (SheafOfModules.unit (structureSheaf O hO))) ≅ M =>
      i.hom.val.app U
        (tensorSectionsAt O hO U M (SheafOfModules.unit (structureSheaf O hO)) m r))
    (Strict.rightUnitor_eq O hO M)).symm.trans
    (rightUnitor_hom_val_app_tmul O hO M U m r)

/-! ### The associativity constraint -/

variable (M N P : SheafOfModules.{w} (structureSheaf O hO))

/-- The comparison of the left-bracketed threefold tensor product of the localized structure
with the left-bracketed threefold tensor product sheaf: `tensorObjIso` in the first factor, then
`tensorObjIso` again. It is the crossing through which
`Stacks.SheafOfModules.tensorSectionsAt_localizedAssociator` reads the source of the
associator. -/
def tensorObjIsoLeft : (M ⊗ N) ⊗ P ≅ (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O,
    Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂
    CommRingCat RingCat) (hO)⟩).obj (M)).obj (N)))).obj (P)) :=
  (tensorObjIso O hO M N ⊗ᵢ Iso.refl P) ≪≫ tensorObjIso O hO
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O)
      (forget₂ CommRingCat RingCat) (hO)⟩).obj (M)).obj (N))) P

/-- The right-bracketed counterpart of `Stacks.SheafOfModules.tensorObjIsoLeft`. -/
def tensorObjIsoRight : M ⊗ (N ⊗ P) ≅ (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O,
    Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (M)).obj
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂
    CommRingCat RingCat) (hO)⟩).obj (N)).obj (P)))) :=
  (Iso.refl M ⊗ᵢ tensorObjIso O hO N P) ≪≫ tensorObjIso O hO M
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O)
      (forget₂ CommRingCat RingCat) (hO)⟩).obj (N)).obj (P)))

/-- The associator of the strict structure is the localized associator conjugated by the two
crossings. This is `Stacks.SheafOfModules.Strict.associator_eq` with the two bracketings of its
right-hand side named; both sides are the same term, so it is a `rfl`. -/
theorem strictAssociator_eq_conjugate :
    MonoidalCategoryStruct.associator (self := Strict.monoidalCategoryStruct O hO) M N P =
      (tensorObjIsoLeft O hO M N P).symm ≪≫ α_ M N P ≪≫ tensorObjIsoRight O hO M N P :=
  rfl

/-- **The associativity constraint of the localized structure on a triple product section.** The
section of `(M ⊗ N) ⊗ P` that `Stacks.SheafOfModules.tensorObjIsoLeft` identifies with the
product of the product of `m` and `n` with `p` goes to the section of `M ⊗ (N ⊗ P)` that
`Stacks.SheafOfModules.tensorObjIsoRight` identifies with the product of `m` with the product of
`n` and `p`.

This is `Stacks.SheafOfModules.strictAssociator_eq_conjugate` read against
`Stacks.SheafOfModules.associator_hom_val_app_tmul`. -/
theorem tensorSectionsAt_localizedAssociator (U : Cᵒᵖ)
    (m : M.val.obj U) (n : N.val.obj U) (p : P.val.obj U) :
    (α_ M N P).hom.val.app U
        ((tensorObjIsoLeft O hO M N P).inv.val.app U
          (tensorSectionsAt O hO U ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O,
              Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
              (M)).obj (N))) P
            (tensorSectionsAt O hO U M N m n) p)) =
      (tensorObjIsoRight O hO M N P).inv.val.app U
        (tensorSectionsAt O hO U M ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O,
            Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (N)).obj
            (P))) m
          (tensorSectionsAt O hO U N P n p)) :=
  crossedMorphism_val_app O hO (tensorObjIsoLeft O hO M N P) (tensorObjIsoRight O hO M N P)
    (α_ M N P).hom
    (MonoidalCategoryStruct.associator (self := Strict.monoidalCategoryStruct O hO) M N P).hom
    (congrArg Iso.hom (strictAssociator_eq_conjugate O hO M N P)).symm U _ _
    (associator_hom_val_app_tmul O hO M N P U m n p)

/-- **The associativity constraint of the localized structure on a triple product section, in
the inverse direction.** This is the direction a section of a threefold tensor product is read
through. -/
theorem tensorSectionsAt_localizedAssociator_inv (U : Cᵒᵖ)
    (m : M.val.obj U) (n : N.val.obj U) (p : P.val.obj U) :
    (α_ M N P).inv.val.app U
        ((tensorObjIsoRight O hO M N P).inv.val.app U
          (tensorSectionsAt O hO U M ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O,
              Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
              (N)).obj (P))) m
            (tensorSectionsAt O hO U N P n p))) =
      (tensorObjIsoLeft O hO M N P).inv.val.app U
        (tensorSectionsAt O hO U ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O,
            Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (M)).obj
            (N))) P
          (tensorSectionsAt O hO U M N m n) p) :=
  (congrArg ((α_ M N P).inv.val.app U)
      (tensorSectionsAt_localizedAssociator O hO M N P U m n p)).symm.trans
    (inv_val_app_hom_val_app (α_ M N P) U _)

/-! ### The braiding -/

/-- **The braiding of the localized structure on a product section**: it exchanges the two
factors. Unlike the three constraints this goes through
`Stacks.SheafOfModules.tensorObjIso_braiding` and
`Stacks.SheafOfModules.tensorSections_braidingAt`, the strict structure's braiding having no
section formula. -/
theorem tensorSectionsAt_localizedBraiding (U : Cᵒᵖ)
    (s : M.val.obj U) (t : N.val.obj U) :
    (β_ M N).hom.val.app U
        ((tensorObjIso O hO M N).inv.val.app U (tensorSectionsAt O hO U M N s t)) =
      (tensorObjIso O hO N M).inv.val.app U (tensorSectionsAt O hO U N M t s) :=
  crossedMorphism_val_app O hO (tensorObjIso O hO M N) (tensorObjIso O hO N M) (β_ M N).hom
    (Invertible.tensorProductBraiding O hO M N).hom
    ((Iso.inv_comp_eq (tensorObjIso O hO M N)).mpr (tensorObjIso_braiding O hO M N).symm) U _ _
    (tensorSections_braidingAt O hO U M N s t)

/-! ### The same localization, at the other choice of unit object

`Stacks.SheafInternalHom.monoidalCategory` is the same localization of the same monoidal
structure along the same functor, with one difference: the unit object of the localized
structure is chosen to be the sheafification of the presheaf unit rather than
`SheafOfModules.unit`, i.e. the comparison `ε` of
`CategoryTheory.Localization.Monoidal` is `Iso.refl` there and
`Stacks.SheafOfModules.sheafifyUnitIso` here. It is the structure
`Stacks.ProjBundleInverseBaseChange.inverseQuotientBaseChangeIso` is built in.

In `CategoryTheory.Localization.Monoidal` the choice of `ε` enters *only* the two unitors. So
the tensor product, the whiskerings, the tensor product of two morphisms and the associator of
the two structures are the same terms — each identification below is a `rfl` — and the formulas
above apply to the other structure unchanged. The two unitors differ, and are related by
`CategoryTheory.Localization.Monoidal.rightUnitor_hom_eq_of_unitIso` and its left companion:
each is the other precomposed with the comparison `ε₁⁻¹ ≫ ε₂` of the two unit objects, whiskered
into the appropriate factor. That is what the last two statements of this file use. -/

/-- The unit object of `Stacks.SheafInternalHom.monoidalCategory` is the sheafification of the
presheaf unit, not `SheafOfModules.unit`: this is the one difference between that structure and
`Stacks.SheafOfModules.monoidalCategory`, and `Stacks.SheafOfModules.sheafifyUnitIso` is the
comparison of the two unit objects. -/
theorem sheafInternalHom_tensorUnit_eq :
    (@MonoidalCategoryStruct.tensorUnit _ _
        (Stacks.SheafInternalHom.monoidalCategory O hO).toMonoidalCategoryStruct) =
      (sheafifyFunctor O hO).obj (𝟙_ (PresheafOfModules.{w} (structureRingPresheaf O))) :=
  rfl

/-- The two localizations have the same tensor product on objects. -/
theorem sheafInternalHom_tensorObj_eq (A B : SheafOfModules.{w} (structureSheaf O hO)) :
    (@MonoidalCategoryStruct.tensorObj _ _
        (Stacks.SheafInternalHom.monoidalCategory O hO).toMonoidalCategoryStruct A B) = A ⊗ B :=
  rfl

/-- The two localizations have the same left whiskering. -/
theorem sheafInternalHom_whiskerLeft_eq (A : SheafOfModules.{w} (structureSheaf O hO))
    {B B' : SheafOfModules.{w} (structureSheaf O hO)} (g : B ⟶ B') :
    (@MonoidalCategoryStruct.whiskerLeft _ _
        (Stacks.SheafInternalHom.monoidalCategory O hO).toMonoidalCategoryStruct A B B' g) =
      A ◁ g :=
  rfl

/-- The two localizations have the same right whiskering. -/
theorem sheafInternalHom_whiskerRight_eq {A A' : SheafOfModules.{w} (structureSheaf O hO)}
    (f : A ⟶ A') (B : SheafOfModules.{w} (structureSheaf O hO)) :
    (@MonoidalCategoryStruct.whiskerRight _ _
        (Stacks.SheafInternalHom.monoidalCategory O hO).toMonoidalCategoryStruct A A' f B) =
      f ▷ B :=
  rfl

/-- The two localizations have the same tensor product of two morphisms. -/
theorem sheafInternalHom_tensorHom_eq {A A' B B' : SheafOfModules.{w} (structureSheaf O hO)}
    (f : A ⟶ A') (g : B ⟶ B') :
    (@MonoidalCategoryStruct.tensorHom _ _
        (Stacks.SheafInternalHom.monoidalCategory O hO).toMonoidalCategoryStruct A A' B B' f g) =
      f ⊗ₘ g :=
  rfl

/-- **The two localizations have the same associativity constraint.** The choice of unit object
does not enter `CategoryTheory.Localization.Monoidal.associator`, so the hardest of the three
constraints transfers to `Stacks.SheafInternalHom.monoidalCategory` for free. -/
theorem sheafInternalHom_associator_eq (A B D : SheafOfModules.{w} (structureSheaf O hO)) :
    (@MonoidalCategoryStruct.associator _ _
        (Stacks.SheafInternalHom.monoidalCategory O hO).toMonoidalCategoryStruct A B D) =
      α_ A B D :=
  rfl

/-- **The associativity constraint of `Stacks.SheafInternalHom.monoidalCategory` on a triple
product section**, in the direction a section is read through. This is
`Stacks.SheafOfModules.tensorSectionsAt_localizedAssociator_inv` at the other choice of unit
object, which by `Stacks.SheafOfModules.sheafInternalHom_associator_eq` is the same
statement. -/
theorem tensorSectionsAt_sheafInternalHomAssociator_inv (U : Cᵒᵖ)
    (m : M.val.obj U) (n : N.val.obj U) (p : P.val.obj U) :
    (@MonoidalCategoryStruct.associator _ _
          (Stacks.SheafInternalHom.monoidalCategory O hO).toMonoidalCategoryStruct
          M N P).inv.val.app U
        ((tensorObjIsoRight O hO M N P).inv.val.app U
          (tensorSectionsAt O hO U M ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O,
              Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
              (N)).obj (P))) m
            (tensorSectionsAt O hO U N P n p))) =
      (tensorObjIsoLeft O hO M N P).inv.val.app U
        (tensorSectionsAt O hO U ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O,
            Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (M)).obj
            (N))) P
          (tensorSectionsAt O hO U M N m n) p) :=
  tensorSectionsAt_localizedAssociator_inv O hO M N P U m n p

/-- **Left whiskering of `Stacks.SheafInternalHom.monoidalCategory` on a product section.** -/
theorem tensorSectionsAt_sheafInternalHomWhiskerLeft (U : Cᵒᵖ)
    {N' : SheafOfModules.{w} (structureSheaf O hO)} (g : N ⟶ N')
    (s : M.val.obj U) (t : N.val.obj U) :
    (@MonoidalCategoryStruct.whiskerLeft _ _
          (Stacks.SheafInternalHom.monoidalCategory O hO).toMonoidalCategoryStruct
          M N N' g).val.app U
        ((tensorObjIso O hO M N).inv.val.app U (tensorSectionsAt O hO U M N s t)) =
      (tensorObjIso O hO M N').inv.val.app U
        (tensorSectionsAt O hO U M N' s (g.val.app U t)) :=
  tensorSectionsAt_localizedWhiskerLeft O hO M g U s t

/-- **Right whiskering of `Stacks.SheafInternalHom.monoidalCategory` on a product section.** -/
theorem tensorSectionsAt_sheafInternalHomWhiskerRight (U : Cᵒᵖ)
    {M' : SheafOfModules.{w} (structureSheaf O hO)} (f : M ⟶ M')
    (s : M.val.obj U) (t : N.val.obj U) :
    (@MonoidalCategoryStruct.whiskerRight _ _
          (Stacks.SheafInternalHom.monoidalCategory O hO).toMonoidalCategoryStruct
          M M' f N).val.app U
        ((tensorObjIso O hO M N).inv.val.app U (tensorSectionsAt O hO U M N s t)) =
      (tensorObjIso O hO M' N).inv.val.app U
        (tensorSectionsAt O hO U M' N (f.val.app U s) t) :=
  tensorSectionsAt_localizedWhiskerRight O hO f N U s t

/-- **The right unit constraint of `Stacks.SheafInternalHom.monoidalCategory` on a product
section.** The unit object there is the sheafification of the presheaf unit, so the second factor
of the product section is a section `t` of that sheaf and not of the structure sheaf; the
constraint is the right unit constraint of `Stacks.SheafOfModules.monoidalCategory` on the
product section whose second factor is the image of `t` under
`Stacks.SheafOfModules.sheafifyUnitIso`, which
`Stacks.SheafOfModules.tensorSectionsAt_localizedRightUnitor` then evaluates to a scalar
multiple.

The conclusion is stated in that transported form rather than as the scalar multiple itself
because the image of `t` carries the type `(SheafOfModules.unit 𝒪).val.obj U` and not
`𝒪.obj.obj U`: the two are definitionally equal, but a type ascription does not change the type
at which a term's instances are synthesised, and the scalar action is found only at the second
spelling.

`CategoryTheory.Localization.Monoidal.rightUnitor_hom_eq_of_unitIso` reduces the constraint to
the one of `Stacks.SheafOfModules.monoidalCategory` precomposed with the comparison of the two
unit objects whiskered into the second factor, and
`Stacks.SheafOfModules.tensorSectionsAt_localizedWhiskerLeft` reads that whiskering on the
section. -/
theorem tensorSectionsAt_sheafInternalHomRightUnitor (U : Cᵒᵖ) (m : M.val.obj U)
    (t : ((sheafifyFunctor O hO).obj
      (𝟙_ (PresheafOfModules.{w} (structureRingPresheaf O)))).val.obj U) :
    (@MonoidalCategoryStruct.rightUnitor _ _
            (Stacks.SheafInternalHom.monoidalCategory O hO).toMonoidalCategoryStruct
            M).hom.val.app U
        ((tensorObjIso O hO M
              ((sheafifyFunctor O hO).obj
                (𝟙_ (PresheafOfModules.{w} (structureRingPresheaf O))))).inv.val.app U
          (tensorSectionsAt O hO U M
            ((sheafifyFunctor O hO).obj
              (𝟙_ (PresheafOfModules.{w} (structureRingPresheaf O)))) m t)) =
      (ρ_ M).hom.val.app U
        ((tensorObjIso O hO M (SheafOfModules.unit (structureSheaf O hO))).inv.val.app U
          (tensorSectionsAt O hO U M (SheafOfModules.unit (structureSheaf O hO)) m
            ((sheafifyUnitIso O hO).hom.val.app U t))) :=
  Eq.trans
    (congrArg
      (fun φ : M ⊗ (sheafifyFunctor O hO).obj
            (𝟙_ (PresheafOfModules.{w} (structureRingPresheaf O))) ⟶ M =>
        φ.val.app U
          ((tensorObjIso O hO M
                ((sheafifyFunctor O hO).obj
                  (𝟙_ (PresheafOfModules.{w} (structureRingPresheaf O))))).inv.val.app U
            (tensorSectionsAt O hO U M
              ((sheafifyFunctor O hO).obj
                (𝟙_ (PresheafOfModules.{w} (structureRingPresheaf O)))) m t)))
      ((CategoryTheory.Localization.Monoidal.rightUnitor_hom_eq_of_unitIso (sheafifyFunctor O hO)
            (localIso (J := J) O) (Iso.refl _) (sheafifyUnitIso O hO) M).trans
        (congrArg (fun θ : (sheafifyFunctor O hO).obj
              (𝟙_ (PresheafOfModules.{w} (structureRingPresheaf O))) ⟶
                SheafOfModules.unit (structureSheaf O hO) =>
            (M ◁ θ) ≫ (ρ_ M).hom)
          (Category.id_comp (sheafifyUnitIso O hO).hom))))
    ((SheafOfModules.comp_val_app_apply (M ◁ (sheafifyUnitIso O hO).hom) (ρ_ M).hom U _).trans
      (congrArg (fun y : (M ⊗ SheafOfModules.unit (structureSheaf O hO)).val.obj U =>
          (ρ_ M).hom.val.app U y)
        (tensorSectionsAt_localizedWhiskerLeft O hO M (sheafifyUnitIso O hO).hom U m t)))

/-- **The left unit constraint of `Stacks.SheafInternalHom.monoidalCategory` on a product
section**, the companion of
`Stacks.SheafOfModules.tensorSectionsAt_sheafInternalHomRightUnitor`, and stated in the same
transported form for the same reason. -/
theorem tensorSectionsAt_sheafInternalHomLeftUnitor (U : Cᵒᵖ)
    (t : ((sheafifyFunctor O hO).obj
      (𝟙_ (PresheafOfModules.{w} (structureRingPresheaf O)))).val.obj U) (m : M.val.obj U) :
    (@MonoidalCategoryStruct.leftUnitor _ _
            (Stacks.SheafInternalHom.monoidalCategory O hO).toMonoidalCategoryStruct
            M).hom.val.app U
        ((tensorObjIso O hO
              ((sheafifyFunctor O hO).obj
                (𝟙_ (PresheafOfModules.{w} (structureRingPresheaf O)))) M).inv.val.app U
          (tensorSectionsAt O hO U
            ((sheafifyFunctor O hO).obj
              (𝟙_ (PresheafOfModules.{w} (structureRingPresheaf O)))) M t m)) =
      (λ_ M).hom.val.app U
        ((tensorObjIso O hO (SheafOfModules.unit (structureSheaf O hO)) M).inv.val.app U
          (tensorSectionsAt O hO U (SheafOfModules.unit (structureSheaf O hO)) M
            ((sheafifyUnitIso O hO).hom.val.app U t) m)) :=
  Eq.trans
    (congrArg
      (fun φ : (sheafifyFunctor O hO).obj
            (𝟙_ (PresheafOfModules.{w} (structureRingPresheaf O))) ⊗ M ⟶ M =>
        φ.val.app U
          ((tensorObjIso O hO
                ((sheafifyFunctor O hO).obj
                  (𝟙_ (PresheafOfModules.{w} (structureRingPresheaf O)))) M).inv.val.app U
            (tensorSectionsAt O hO U
              ((sheafifyFunctor O hO).obj
                (𝟙_ (PresheafOfModules.{w} (structureRingPresheaf O)))) M t m)))
      ((CategoryTheory.Localization.Monoidal.leftUnitor_hom_eq_of_unitIso (sheafifyFunctor O hO)
            (localIso (J := J) O) (Iso.refl _) (sheafifyUnitIso O hO) M).trans
        (congrArg (fun θ : (sheafifyFunctor O hO).obj
              (𝟙_ (PresheafOfModules.{w} (structureRingPresheaf O))) ⟶
                SheafOfModules.unit (structureSheaf O hO) =>
            (θ ▷ M) ≫ (λ_ M).hom)
          (Category.id_comp (sheafifyUnitIso O hO).hom))))
    ((SheafOfModules.comp_val_app_apply ((sheafifyUnitIso O hO).hom ▷ M) (λ_ M).hom U _).trans
      (congrArg (fun y : (SheafOfModules.unit (structureSheaf O hO) ⊗ M).val.obj U =>
          (λ_ M).hom.val.app U y)
        (tensorSectionsAt_localizedWhiskerRight O hO (sheafifyUnitIso O hO).hom M U t m)))

/-! ### The threefold crossings in terms of the twofold one -/

/-- **The left-bracketed threefold crossing in terms of the twofold one.** The section of
`(M ⊗ N) ⊗ P` that `Stacks.SheafOfModules.tensorObjIsoLeft` identifies with the product of `x`
and `p` is the one that `tensorObjIso` of `M ⊗ N` with `P` identifies with the product of
`tensorObjIso.inv x` and `p`.

This is what lets `Stacks.SheafOfModules.tensorSectionsAt_localizedAssociator` be chained with
`tensorSectionsAt_localizedWhiskerRight`, whose conclusion crosses only the inner factor; see the
implementation notes. The two crossings differ by the tensor product of `tensorObjIso.inv` with
an identity, which `tensorSectionsAt_localizedTensorHom` reads on a product section. -/
theorem tensorObjIsoLeft_inv_tensorSectionsAt
    (U : Cᵒᵖ) (x : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp
        _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (M)).obj (N))).val.obj U) (p : P.val.obj U) :
    (tensorObjIsoLeft O hO M N P).inv.val.app U
        (tensorSectionsAt O hO U ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O,
            Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (M)).obj
            (N))) P x p) =
      (tensorObjIso O hO (@MonoidalCategoryStruct.tensorObj _ _
            (Stacks.SheafInternalHom.monoidalCategory O hO).toMonoidalCategoryStruct M N)
          P).inv.val.app U
        (tensorSectionsAt O hO U (@MonoidalCategoryStruct.tensorObj _ _
            (Stacks.SheafInternalHom.monoidalCategory O hO).toMonoidalCategoryStruct M N) P
          ((tensorObjIso O hO M N).inv.val.app U x) p) := by
  rw [show (tensorObjIsoLeft O hO M N P).inv = _ ≫ ((tensorObjIso O hO M N).inv ⊗ₘ 𝟙 P) from rfl,
    comp_val_app_apply]
  exact tensorSectionsAt_localizedTensorHom O hO (tensorObjIso O hO M N).inv (𝟙 P) U x p

/-- **The right-bracketed threefold crossing in terms of the twofold one**, the counterpart of
`Stacks.SheafOfModules.tensorObjIsoLeft_inv_tensorSectionsAt`: it is what chains the associator
formula's target with `tensorSectionsAt_localizedWhiskerLeft`. -/
theorem tensorObjIsoRight_inv_tensorSectionsAt
    (U : Cᵒᵖ) (m : M.val.obj U) (y : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O,
        Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (N)).obj
        (P))).val.obj U) :
    (tensorObjIsoRight O hO M N P).inv.val.app U
        (tensorSectionsAt O hO U M ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O,
            Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (N)).obj
            (P))) m y) =
      (tensorObjIso O hO M (@MonoidalCategoryStruct.tensorObj _ _
          (Stacks.SheafInternalHom.monoidalCategory O hO).toMonoidalCategoryStruct
          N P)).inv.val.app U
        (tensorSectionsAt O hO U M (@MonoidalCategoryStruct.tensorObj _ _
            (Stacks.SheafInternalHom.monoidalCategory O hO).toMonoidalCategoryStruct N P) m
          ((tensorObjIso O hO N P).inv.val.app U y)) := by
  rw [show (tensorObjIsoRight O hO M N P).inv = _ ≫ (𝟙 M ⊗ₘ (tensorObjIso O hO N P).inv) from rfl,
    comp_val_app_apply]
  exact tensorSectionsAt_localizedTensorHom O hO (𝟙 M) (tensorObjIso O hO N P).inv U m y

/-- **The associativity constraint of `Stacks.SheafInternalHom.monoidalCategory` on a triple
product section**, in the forward direction. This is
`Stacks.SheafOfModules.tensorSectionsAt_sheafInternalHomAssociator_inv` undone by
`Stacks.SheafOfModules.hom_val_app_inv_val_app`. -/
theorem tensorSectionsAt_sheafInternalHomAssociator (U : Cᵒᵖ)
    (m : M.val.obj U) (n : N.val.obj U) (p : P.val.obj U) :
    (@MonoidalCategoryStruct.associator _ _
          (Stacks.SheafInternalHom.monoidalCategory O hO).toMonoidalCategoryStruct
          M N P).hom.val.app U
        ((tensorObjIsoLeft O hO M N P).inv.val.app U
          (tensorSectionsAt O hO U ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O,
              Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
              (M)).obj (N))) P
            (tensorSectionsAt O hO U M N m n) p)) =
      (tensorObjIsoRight O hO M N P).inv.val.app U
        (tensorSectionsAt O hO U M ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O,
            Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (N)).obj
            (P))) m
          (tensorSectionsAt O hO U N P n p)) :=
  (congrArg ((@MonoidalCategoryStruct.associator _ _
        (Stacks.SheafInternalHom.monoidalCategory O hO).toMonoidalCategoryStruct
        M N P).hom.val.app U)
      (tensorSectionsAt_sheafInternalHomAssociator_inv O hO M N P U m n p)).symm.trans
    (hom_val_app_inv_val_app (@MonoidalCategoryStruct.associator _ _
      (Stacks.SheafInternalHom.monoidalCategory O hO).toMonoidalCategoryStruct M N P) U _)

/-! ### The unit constraints at a section of the unit object that crosses to `1` -/

/-- **The right unit constraint of `Stacks.SheafInternalHom.monoidalCategory` is the identity on
a product section whose unit factor crosses to `1`.** The hypothesis `ht` is the only thing asked
of `t`: that `Stacks.SheafOfModules.sheafifyUnitIso` carries it to the unit section of the
structure sheaf. This is
`Stacks.SheafOfModules.tensorSectionsAt_sheafInternalHomRightUnitor` followed by
`tensorSectionsAt_localizedRightUnitor` and `one_smul`. -/
theorem tensorSectionsAt_sheafInternalHomRightUnitor_one (U : Cᵒᵖ) (m : M.val.obj U)
    (t : (@MonoidalCategoryStruct.tensorUnit _ _
      (Stacks.SheafInternalHom.monoidalCategory O hO).toMonoidalCategoryStruct).val.obj U)
    (ht : (sheafifyUnitIso O hO).hom.val.app U t = (1 : (structureSheaf O hO).obj.obj U)) :
    (@MonoidalCategoryStruct.rightUnitor _ _
            (Stacks.SheafInternalHom.monoidalCategory O hO).toMonoidalCategoryStruct
            M).hom.val.app U
        ((tensorObjIso O hO M
              (@MonoidalCategoryStruct.tensorUnit _ _
                (Stacks.SheafInternalHom.monoidalCategory O
                  hO).toMonoidalCategoryStruct)).inv.val.app U
          (tensorSectionsAt O hO U M
            (@MonoidalCategoryStruct.tensorUnit _ _
              (Stacks.SheafInternalHom.monoidalCategory O hO).toMonoidalCategoryStruct)
            m t)) = m :=
  by
  refine (tensorSectionsAt_sheafInternalHomRightUnitor O hO M U m t).trans ?_
  rw [ht, tensorSectionsAt_localizedRightUnitor, one_smul]

/-- **The left unit constraint of `Stacks.SheafInternalHom.monoidalCategory` is the identity on a
product section whose unit factor crosses to `1`**, the companion of
`Stacks.SheafOfModules.tensorSectionsAt_sheafInternalHomRightUnitor_one`. -/
theorem tensorSectionsAt_sheafInternalHomLeftUnitor_one (U : Cᵒᵖ)
    (t : (@MonoidalCategoryStruct.tensorUnit _ _
      (Stacks.SheafInternalHom.monoidalCategory O hO).toMonoidalCategoryStruct).val.obj U)
    (ht : (sheafifyUnitIso O hO).hom.val.app U t = (1 : (structureSheaf O hO).obj.obj U))
    (m : M.val.obj U) :
    (@MonoidalCategoryStruct.leftUnitor _ _
            (Stacks.SheafInternalHom.monoidalCategory O hO).toMonoidalCategoryStruct
            M).hom.val.app U
        ((tensorObjIso O hO
              (@MonoidalCategoryStruct.tensorUnit _ _
                (Stacks.SheafInternalHom.monoidalCategory O hO).toMonoidalCategoryStruct)
              M).inv.val.app U
          (tensorSectionsAt O hO U
            (@MonoidalCategoryStruct.tensorUnit _ _
              (Stacks.SheafInternalHom.monoidalCategory O hO).toMonoidalCategoryStruct)
            M t m)) = m :=
  by
  refine (tensorSectionsAt_sheafInternalHomLeftUnitor O hO M U t m).trans ?_
  rw [ht, tensorSectionsAt_localizedLeftUnitor, one_smul]

/-- **The inverse of the left unit constraint of `Stacks.SheafInternalHom.monoidalCategory`
inserts a section of the unit object that crosses to `1`.** This is the direction a computation
that *starts* from a section of `M` reads the constraint through, and it is
`Stacks.SheafOfModules.tensorSectionsAt_sheafInternalHomLeftUnitor_one` undone by
`inv_val_app_hom_val_app`. -/
theorem tensorSectionsAt_sheafInternalHomLeftUnitor_inv_one (U : Cᵒᵖ)
    (t : (@MonoidalCategoryStruct.tensorUnit _ _
      (Stacks.SheafInternalHom.monoidalCategory O hO).toMonoidalCategoryStruct).val.obj U)
    (ht : (sheafifyUnitIso O hO).hom.val.app U t = (1 : (structureSheaf O hO).obj.obj U))
    (m : M.val.obj U) :
    (@MonoidalCategoryStruct.leftUnitor _ _
            (Stacks.SheafInternalHom.monoidalCategory O hO).toMonoidalCategoryStruct
            M).inv.val.app U m =
      (tensorObjIso O hO
            (@MonoidalCategoryStruct.tensorUnit _ _
              (Stacks.SheafInternalHom.monoidalCategory O hO).toMonoidalCategoryStruct)
            M).inv.val.app U
        (tensorSectionsAt O hO U
          (@MonoidalCategoryStruct.tensorUnit _ _
            (Stacks.SheafInternalHom.monoidalCategory O hO).toMonoidalCategoryStruct)
          M t m) :=
  (congrArg ((@MonoidalCategoryStruct.leftUnitor _ _
        (Stacks.SheafInternalHom.monoidalCategory O hO).toMonoidalCategoryStruct M).inv.val.app U)
      (tensorSectionsAt_sheafInternalHomLeftUnitor_one O hO M U t ht m)).symm.trans
    (inv_val_app_hom_val_app (@MonoidalCategoryStruct.leftUnitor _ _
      (Stacks.SheafInternalHom.monoidalCategory O hO).toMonoidalCategoryStruct M) U _)

end Stacks.SheafOfModules

end
