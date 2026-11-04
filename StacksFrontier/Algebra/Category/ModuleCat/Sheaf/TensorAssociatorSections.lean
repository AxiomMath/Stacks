module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalFiniteFreeSummand
public import StacksCore.Tactic.StacksAttribute

/-!
# The structural morphisms of the tensor product sheaf on local pure tensors

Let `O` be a sheaf of commutative rings on a site `(C, J)`, and consider the monoidal structure
on sheaves of `O`-modules whose tensor product is the tensor product sheaf
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf O hO`, the sheafification of the
objectwise tensor product of the underlying presheaves of modules (Stacks 01CA, 05NA). A local
section of `F ⊗ G` of the shape
`(Stacks.SheafOfModules.TensorSheafification.toSheafify O hO (F.val ⊗ G.val)).app V (x ⊗ₜ y)`,
the image under the sheafification unit of a pure tensor of local sections, is called a *local
pure tensor*. The associator takes the local pure tensor of a local pure tensor with a section
to the local pure tensor of a section with a local pure tensor, re-bracketing the underlying
tensors; each unitor takes a local pure tensor with a section of the structure sheaf to the
corresponding scalar multiple. As a consequence, a sheaf of `O`-modules with a left dual is
locally a direct summand of a finite free module (Stacks 0FNZ).

## Main results

* `Stacks.SheafOfModules.tensorSheafAssociator_hom_val_app_tmul`: the associativity constraint
  of the tensor product sheaf on local pure tensors.
* `Stacks.SheafOfModules.associator_hom_val_app_tmul`,
  `Stacks.SheafOfModules.associator_inv_val_app_tmul`,
  `Stacks.SheafOfModules.leftUnitor_hom_val_app_tmul` and
  `Stacks.SheafOfModules.rightUnitor_hom_val_app_tmul`: the same for the associator and the two
  unitors of the monoidal structure itself, i.e. for `α_`, `λ_` and `ρ_`.
* `Stacks.SheafOfModules.exists_cover_retract_finiteFree_of_exactPairing_tensorSheaf`: a sheaf
  of modules with a left dual is, on the members of a covering of any object, a direct summand
  of a finite free module. `Stacks.SheafOfModules.exists_cover_localDualBasis_tensorSheaf` is
  the corresponding local dual-basis identity.
* `Stacks.SheafOfModules.tensorSheafAssocLeft_hom_val_app_tmul`,
  `Stacks.SheafOfModules.tensorSheafAssocRight_hom_val_app_tmul`,
  `Stacks.SheafOfModules.sheafify_map_associator_val_app_tmul` and
  `Stacks.SheafOfModules.tensorSheafLeftUnitor_hom_val_app_tmul`: the comparison isomorphisms,
  the sheafified presheaf associator and the left unitor of the tensor product sheaf on local
  pure tensors.
* `Stacks.SheafOfModules.comp_val_app_apply`,
  `Stacks.SheafOfModules.inv_val_app_hom_val_app` and
  `Stacks.SheafOfModules.hom_val_app_inv_val_app` evaluate a composite and cancel an isomorphism
  on a local section.

## References

* [The Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA) — the tensor product
  of sheaves of modules.
* [The Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA) — sheafification and
  tensor products.
* [The Stacks Project, Tag 0FNZ](https://stacks.math.columbia.edu/tag/0FNZ)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Localization Opposite

open scoped TensorProduct

universe v u w

namespace Stacks.SheafOfModules

attribute [local implicit_reducible] TensorSheafification.structureSheaf

attribute [local instance] monoidalCategoryPresheafOfModules symmetricCategoryPresheafOfModules

section Sections

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {Rg : Sheaf J RingCat.{w}}

/-- A composite of morphisms of sheaves of modules, evaluated on a local section. -/
theorem comp_val_app_apply {A B D : SheafOfModules.{w} Rg} (f : A ⟶ B) (g : B ⟶ D) (V : Cᵒᵖ)
    (x : A.val.obj V) :
    (f ≫ g).val.app V x = g.val.app V (f.val.app V x) :=
  rfl

/-- The inverse of an isomorphism of sheaves of modules undoes it on local sections. -/
theorem inv_val_app_hom_val_app {A B : SheafOfModules.{w} Rg} (e : A ≅ B) (V : Cᵒᵖ)
    (x : A.val.obj V) :
    e.inv.val.app V (e.hom.val.app V x) = x :=
  (comp_val_app_apply e.hom e.inv V x).symm.trans
    (congrArg (fun f : A ⟶ A ↦ f.val.app V x) e.hom_inv_id)

/-- An isomorphism of sheaves of modules undoes its inverse on local sections. -/
theorem hom_val_app_inv_val_app {A B : SheafOfModules.{w} Rg} (e : A ≅ B) (V : Cᵒᵖ)
    (y : B.val.obj V) :
    e.hom.val.app V (e.inv.val.app V y) = y :=
  inv_val_app_hom_val_app e.symm V y

/-- Equal isomorphisms of sheaves of modules have equal forward maps on local sections. -/
private theorem hom_val_app_congr {A B : SheafOfModules.{w} Rg} {e e' : A ≅ B} (h : e = e')
    (V : Cᵒᵖ) (x : A.val.obj V) : e.hom.val.app V x = e'.hom.val.app V x := by
  rw [h]

/-- If an isomorphism of sheaves of modules sends `x` to `y` on local sections, its inverse
sends `y` back to `x`. -/
private theorem inv_val_app_eq_of_hom_val_app_eq {A B : SheafOfModules.{w} Rg} (e : A ≅ B)
    {V : Cᵒᵖ} {x : A.val.obj V} {y : B.val.obj V} (h : e.hom.val.app V x = y) :
    e.inv.val.app V y = x := by
  rw [← h, inv_val_app_hom_val_app]

end Sections

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

section Steps

variable (M N P : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
  hO)) (V : Cᵒᵖ)

/-- The comparison isomorphism `tensorSheafAssocLeft` carries the sheafification unit of a
left-bracketed triple pure tensor to the local pure tensor of a local pure tensor with a
section. -/
theorem tensorSheafAssocLeft_hom_val_app_tmul
    (m : M.val.obj V) (n : N.val.obj V) (p : P.val.obj V) :
    (tensorSheafAssocLeft O hO M N P).hom.val.app V
        ((Stacks.SheafOfModules.TensorSheafification.toSheafify O hO ((M.val ⊗ N.val) ⊗ P.val)).app
          V ((m ⊗ₜ n) ⊗ₜ p)) =
      (Stacks.SheafOfModules.TensorSheafification.toSheafify O hO
        (((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
            (M)).obj (N))).val ⊗ P.val)).app V
        ((Stacks.SheafOfModules.TensorSheafification.toSheafify O hO (M.val ⊗ N.val)).app V (m ⊗ₜ n)
          ⊗ₜ p) :=
  sheafify_map_toSheafify_app O hO
    (Stacks.SheafOfModules.TensorSheafification.toSheafify O hO (M.val ⊗ N.val) ▷ P.val) V ((m ⊗ₜ n)
      ⊗ₜ p)

/-- The comparison isomorphism `tensorSheafAssocRight` carries the sheafification unit of a
right-bracketed triple pure tensor to the local pure tensor of a section with a local pure
tensor. -/
theorem tensorSheafAssocRight_hom_val_app_tmul
    (m : M.val.obj V) (n : N.val.obj V) (p : P.val.obj V) :
    (tensorSheafAssocRight O hO M N P).hom.val.app V
        ((Stacks.SheafOfModules.TensorSheafification.toSheafify O hO (M.val ⊗ N.val ⊗ P.val)).app V
          (m ⊗ₜ (n ⊗ₜ p))) =
      (Stacks.SheafOfModules.TensorSheafification.toSheafify O hO (M.val ⊗
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
            (N)).obj (P))).val)).app V
        (m ⊗ₜ (Stacks.SheafOfModules.TensorSheafification.toSheafify O hO (N.val ⊗ P.val)).app V (n
          ⊗ₜ p)) :=
  sheafify_map_toSheafify_app O hO
    (M.val ◁ Stacks.SheafOfModules.TensorSheafification.toSheafify O hO (N.val ⊗ P.val)) V (m ⊗ₜ (n
      ⊗ₜ p))

/-- The sheafified presheaf associator re-brackets the sheafification unit of a triple pure
tensor. -/
theorem sheafify_map_associator_val_app_tmul
    (m : M.val.obj V) (n : N.val.obj V) (p : P.val.obj V) :
    ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map (α_ M.val N.val
      P.val).hom).val.app V
        ((Stacks.SheafOfModules.TensorSheafification.toSheafify O hO ((M.val ⊗ N.val) ⊗ P.val)).app
          V ((m ⊗ₜ n) ⊗ₜ p)) =
      (Stacks.SheafOfModules.TensorSheafification.toSheafify O hO (M.val ⊗ N.val ⊗ P.val)).app V (m
        ⊗ₜ (n ⊗ₜ p)) :=
  sheafify_map_toSheafify_app O hO (α_ M.val N.val P.val).hom V ((m ⊗ₜ n) ⊗ₜ p)

/-- The associativity constraint of the tensor product sheaf takes the local pure tensor of a
local pure tensor `m ⊗ₜ n` with a section `p` to the local pure tensor of `m` with the local pure
tensor `n ⊗ₜ p`. -/
theorem tensorSheafAssociator_hom_val_app_tmul
    (m : M.val.obj V) (n : N.val.obj V) (p : P.val.obj V) :
    (tensorSheafAssociator O hO M N P).hom.val.app V
        ((Stacks.SheafOfModules.TensorSheafification.toSheafify O hO
          (((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
              (M)).obj (N))).val ⊗ P.val)).app V
          ((Stacks.SheafOfModules.TensorSheafification.toSheafify O hO (M.val ⊗ N.val)).app V (m ⊗ₜ
            n) ⊗ₜ p)) =
      (Stacks.SheafOfModules.TensorSheafification.toSheafify O hO (M.val ⊗
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
            (N)).obj (P))).val)).app V
        (m ⊗ₜ (Stacks.SheafOfModules.TensorSheafification.toSheafify O hO (N.val ⊗ P.val)).app V (n
          ⊗ₜ p)) := by
  have hinv := inv_val_app_eq_of_hom_val_app_eq _
    (tensorSheafAssocLeft_hom_val_app_tmul O hO M N P V m n p)
  refine Eq.trans ?_ (tensorSheafAssocRight_hom_val_app_tmul O hO M N P V m n p)
  rw [← sheafify_map_associator_val_app_tmul O hO M N P V m n p, ← hinv]
  rfl

/-- The left unit constraint of the tensor product sheaf takes the local pure tensor `r ⊗ₜ m`
of a section `r` of the structure sheaf with a section `m` to `r • m`. -/
theorem tensorSheafLeftUnitor_hom_val_app_tmul
    (r : (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj.obj V) (m : M.val.obj
      V) :
    (tensorSheafLeftUnitor O hO M).hom.val.app V
        ((Stacks.SheafOfModules.TensorSheafification.toSheafify O hO
          (𝟙_ (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
            hO).obj) ⊗ M.val)).app V
            (r ⊗ₜ m)) = r • m :=
  (congrArg (fun z ↦ ((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction O
    hO).counit.app M).val.app V z)
      (sheafify_map_toSheafify_app O hO (λ_ M.val).hom V (r ⊗ₜ m))).trans
    ((counit_toSheafify_app O hO M V ((λ_ M.val).hom.app V (r ⊗ₜ m))).trans
      (ModuleCat.MonoidalCategory.leftUnitor_hom_apply r m))

end Steps

section MonoidalStructure

attribute [local instance] Strict.monoidalCategory

variable (M N P : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
  hO)) (V : Cᵒᵖ)

/-- The associator of the monoidal structure of sheaves of modules takes the local pure tensor
of a local pure tensor `m ⊗ₜ n` with a section `p` to the local pure tensor of `m` with the
local pure tensor `n ⊗ₜ p`. -/
theorem associator_hom_val_app_tmul
    (m : M.val.obj V) (n : N.val.obj V) (p : P.val.obj V) :
    (α_ M N P).hom.val.app V
        ((Stacks.SheafOfModules.TensorSheafification.toSheafify O hO ((M ⊗ N).val ⊗ P.val)).app V
          ((Stacks.SheafOfModules.TensorSheafification.toSheafify O hO (M.val ⊗ N.val)).app V (m ⊗ₜ
            n) ⊗ₜ p)) =
      (Stacks.SheafOfModules.TensorSheafification.toSheafify O hO (M.val ⊗ (N ⊗ P).val)).app V
        (m ⊗ₜ (Stacks.SheafOfModules.TensorSheafification.toSheafify O hO (N.val ⊗ P.val)).app V (n
          ⊗ₜ p)) :=
  (hom_val_app_congr (associator_eq_tensorSheafAssociator O hO M N P) V _).trans
    (tensorSheafAssociator_hom_val_app_tmul O hO M N P V m n p)

/-- The inverse associator of the monoidal structure of sheaves of modules takes the local pure
tensor of a section `m` with a local pure tensor `n ⊗ₜ p` to the local pure tensor of the local
pure tensor `m ⊗ₜ n` with `p`. -/
theorem associator_inv_val_app_tmul
    (m : M.val.obj V) (n : N.val.obj V) (p : P.val.obj V) :
    (α_ M N P).inv.val.app V
        ((Stacks.SheafOfModules.TensorSheafification.toSheafify O hO (M.val ⊗ (N ⊗ P).val)).app V
          (m ⊗ₜ (Stacks.SheafOfModules.TensorSheafification.toSheafify O hO (N.val ⊗ P.val)).app V
            (n ⊗ₜ p))) =
      (Stacks.SheafOfModules.TensorSheafification.toSheafify O hO ((M ⊗ N).val ⊗ P.val)).app V
        ((Stacks.SheafOfModules.TensorSheafification.toSheafify O hO (M.val ⊗ N.val)).app V (m ⊗ₜ n)
          ⊗ₜ p) :=
  inv_val_app_eq_of_hom_val_app_eq _ (associator_hom_val_app_tmul O hO M N P V m n p)

/-- The left unitor of the monoidal structure of sheaves of modules takes the local pure tensor
`r ⊗ₜ m` of a section `r` of the structure sheaf with a section `m` to `r • m`. -/
theorem leftUnitor_hom_val_app_tmul
    (r : (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj.obj V) (m : M.val.obj
      V) :
    (λ_ M).hom.val.app V
        ((Stacks.SheafOfModules.TensorSheafification.toSheafify O hO
          ((𝟙_ (SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
            hO))).val ⊗ M.val)).app V
            (r ⊗ₜ m)) = r • m :=
  (hom_val_app_congr (leftUnitor_eq_tensorSheafLeftUnitor O hO M) V _).trans
    (tensorSheafLeftUnitor_hom_val_app_tmul O hO M V r m)

/-- The right unitor of the monoidal structure of sheaves of modules takes the local pure tensor
`m ⊗ₜ r` of a section `m` with a section `r` of the structure sheaf to `r • m`. -/
theorem rightUnitor_hom_val_app_tmul
    (m : M.val.obj V) (r : (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj.obj
      V) :
    (ρ_ M).hom.val.app V
        ((Stacks.SheafOfModules.TensorSheafification.toSheafify O hO
          (M.val ⊗ (𝟙_ (SheafOfModules.{w}
            (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))).val)).app V
            (m ⊗ₜ r)) = r • m :=
  (hom_val_app_congr (rightUnitor_eq_tensorSheafRightUnitor O hO M) V _).trans
    (tensorLeftFunctorObjUnitIso_hom_app O hO M V m r)

section LocalFiniteFreeSummand

/-- The tensor product `f ⊗ₘ g` of two morphisms in the monoidal structure of sheaves of
modules, conjugated by the identities `eqToHom rfl` identifying its tensor product with
`sheafTensor`, is `(sheafTensor.map f).app B ≫ (sheafTensor.obj A').map g`. -/
theorem tensorSheafMap_eq
    {A A' B B' : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO)} (f : A ⟶ A')
    (g : B ⟶ B') :
    eqToHom (rfl : A ⊗ B = (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        (A)).obj (B))).symm ≫
      (f ⊗ₘ g) ≫
        eqToHom (rfl : A' ⊗ B' = (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O,
          Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
            (A')).obj (B')))
          =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} (J := J)
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).map f).app B ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} (J := J)
            ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).obj
              A').map g :=
  (Category.id_comp _).trans ((Category.comp_id _).trans
    ((tensorHom_eq_sheafify_map O hO f g).trans
      (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map
        (R := ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩)
        f g).symm))

variable (F G : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))

/-- For the monoidal structure of sheaves of modules, on a covering of any object the
coevaluation of a left-dual pairing is a finite sum of local pure tensors, and every local
section of `F` is the corresponding dual-basis combination. -/
theorem exists_cover_localDualBasis_tensorSheaf (p : ExactPairing F G) (U : C) :
    ∃ S : Sieve U, S ∈ J U ∧
      ∀ (V : C) (i : V ⟶ U), S i →
        ∃ n : ℕ, ∃ (f : Fin n → F.val.obj (op V)) (g : Fin n → G.val.obj (op V)),
          (ExactPairing.coevaluation F G).val.app (op V) (1 : O.obj (op V)) =
              ∑ j, (Stacks.SheafOfModules.TensorSheafification.toSheafify O hO (F.val ⊗ G.val)).app
                (op V) (f j ⊗ₜ g j) ∧
          ∀ (W : C) (k : W ⟶ V) (x : F.val.obj (op W)),
            x = ∑ j, @SMul.smul ((Stacks.SheafOfModules.TensorSheafification.structureSheaf O
              hO).obj.obj (op W))
                (F.val.obj (op W)) _
                ((ExactPairing.evaluation F G).val.app (op W)
                  ((Stacks.SheafOfModules.TensorSheafification.toSheafify O hO (G.val ⊗ F.val)).app
                    (op W)
                    (G.val.map k.op (g j) ⊗ₜ x)))
                (F.val.map k.op (f j)) :=
  exists_cover_localDualBasis O hO F G (Strict.monoidalCategory O hO) rfl (fun _ _ ↦ rfl)
    (fun f g ↦ tensorSheafMap_eq O hO f g)
    (fun A B D V a b c ↦ associator_hom_val_app_tmul O hO A B D V a b c)
    (fun A V r a ↦ leftUnitor_hom_val_app_tmul O hO A V r a)
    (fun A V a r ↦ rightUnitor_hom_val_app_tmul O hO A V a r) p U

/-- Let `(C, O)` be a ringed site and let `F` be a sheaf of `O`-modules with a left dual `G` for
the monoidal structure given by the tensor product sheaf. Then every object `U` of the site has
a covering on whose members `F` restricts to a direct summand of a finite free module. -/
@[stacks 0FNZ "local_finite_free_summand"]
theorem exists_cover_retract_finiteFree_of_exactPairing_tensorSheaf
    [HasSheafify J AddCommGrpCat.{w}]
    [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{w}]
    [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (p : ExactPairing F G) (U : C) :
    ∃ S : Sieve U, S ∈ J U ∧
      ∀ (V : C) (i : V ⟶ U), S i →
        ∃ I : Type w, Finite I ∧
          Nonempty (Retract (F.over V)
            (SheafOfModules.free (R := (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
              hO).over V) I)) :=
  exists_cover_retract_finiteFree_of_exactPairing O hO F G (Strict.monoidalCategory O hO) rfl
    (fun _ _ ↦ rfl) (fun f g ↦ tensorSheafMap_eq O hO f g)
    (fun A B D V a b c ↦ associator_hom_val_app_tmul O hO A B D V a b c)
    (fun A V r a ↦ leftUnitor_hom_val_app_tmul O hO A V r a)
    (fun A V a r ↦ rightUnitor_hom_val_app_tmul O hO A V a r) p U

end LocalFiniteFreeSummand

end MonoidalStructure

end Stacks.SheafOfModules

end
