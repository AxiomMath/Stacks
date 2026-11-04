module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackBraiding
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.ChartModuleUnit

/-!
# Stacks 03EL read through an identification of the pullback is monoidal

Let `f : X ⟶ Y` be a morphism of ringed topoi and `α : f^* ≅ L` an identification of the
pullback of modules with a functor `L`.  The comparison of Stacks 03EL read through `α`,
`Stacks.SheafOfModules.pullbackTensorIsoTransport`, `L(M ⊗ N) ≅ L M ⊗ L N`, and the identification
of the units read through `α`, `Stacks.SheafOfModules.pullbackUnitIsoTransport`, `L 𝒪_Y ≅ 𝒪_X`,
are compatible with the associator, the two unitors and the braiding of the strict monoidal
structure of Tag 01CA on both sides.

For `L = f^*` and `α` the identity these are the four coherences of the base,
`Stacks.SheafOfModules.RingedToposPullback.associativity`, `leftUnitality`, `rightUnitality` and
`braiding`; in general each coherence transports along `α`, by an abstract lemma over monoidal
categories proved once in the first section.  No naturality of the comparison is needed for the
transport, only that of `α` and of the structural morphisms.

## Main results

* `Stacks.SheafOfModules.pullbackTensorIsoTransport_whiskerLeft_naturality` and
  `Stacks.SheafOfModules.pullbackTensorIsoTransport_whiskerRight_naturality`: the naturality of
  the transported comparison in each variable, in whiskered form.
* `Stacks.SheafOfModules.pullbackTensorIsoTransport_associativity`: **the transported comparison
  of Stacks 03EL is compatible with the associator.**
* `Stacks.SheafOfModules.pullbackTensorIsoTransport_braiding`: it is compatible with the braiding.
* `Stacks.SheafOfModules.pullbackTensorIsoTransport_leftUnitality` and
  `Stacks.SheafOfModules.pullbackTensorIsoTransport_rightUnitality`: it is compatible with the two
  unitors, the units being matched by `Stacks.SheafOfModules.pullbackUnitIsoTransport`.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

/-! ### Transport of the coherences along an isomorphism of functors -/

/-- A map relation for `F` transports to `L` by conjugating with the components of `α`. -/
private theorem map_eq_conj_of_map_eq {C D : Type*} [Category C] [Category D] {F L : C ⥤ D}
    (α : F ≅ L) {X Y : C} {φ : X ⟶ Y} {ψ : F.obj X ⟶ F.obj Y} (h : F.map φ = ψ) :
    L.map φ = α.inv.app X ≫ ψ ≫ α.hom.app Y := by
  rw [← h]; simp

section Transport

variable {C D : Type*} [Category C] [MonoidalCategory C] [Category D] [MonoidalCategory D]
  {F L : C ⥤ D} (α : F ≅ L) (δ : ∀ A B : C, F.obj (A ⊗ B) ≅ F.obj A ⊗ F.obj B)
  (δ' : ∀ A B : C, L.obj (A ⊗ B) ≅ L.obj A ⊗ L.obj B)
  (hδ : ∀ A B : C, (δ' A B).hom = α.inv.app (A ⊗ B) ≫ (δ A B).hom ≫
    (α.hom.app A ⊗ₘ α.hom.app B))
include hδ

/-- **Associativity transports along an isomorphism of functors.** -/
private theorem transport_associativity (A B E : C)
    (h : F.map (α_ A B E).hom ≫ (δ A (B ⊗ E)).hom ≫ (F.obj A ◁ (δ B E).hom) =
      (δ (A ⊗ B) E).hom ≫ ((δ A B).hom ▷ F.obj E) ≫ (α_ (F.obj A) (F.obj B) (F.obj E)).hom) :
    L.map (α_ A B E).hom ≫ (δ' A (B ⊗ E)).hom ≫ (L.obj A ◁ (δ' B E).hom) =
      (δ' (A ⊗ B) E).hom ≫ ((δ' A B).hom ▷ L.obj E) ≫ (α_ (L.obj A) (L.obj B) (L.obj E)).hom := by
  calc _ = α.inv.app _ ≫ (F.map (α_ A B E).hom ≫ (δ A (B ⊗ E)).hom ≫ (F.obj A ◁ (δ B E).hom)) ≫
        (α.hom.app A ⊗ₘ (α.hom.app B ⊗ₘ α.hom.app E)) := by
        simp only [hδ, Category.assoc, NatTrans.naturality_assoc, ← id_tensorHom,
          tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id, Iso.hom_inv_id_app_assoc]
    _ = α.inv.app _ ≫ ((δ (A ⊗ B) E).hom ≫ ((δ A B).hom ▷ F.obj E) ≫
        (α_ (F.obj A) (F.obj B) (F.obj E)).hom) ≫
        (α.hom.app A ⊗ₘ (α.hom.app B ⊗ₘ α.hom.app E)) := by rw [h]
    _ = _ := by
        simp only [hδ, Category.assoc, ← associator_naturality, ← tensorHom_id,
          tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id,
          Iso.hom_inv_id_app_assoc]

/-- **The braiding transports along an isomorphism of functors.** -/
private theorem transport_braiding [BraidedCategory C] [BraidedCategory D] (A B : C)
    (h : F.map (β_ A B).hom ≫ (δ B A).hom = (δ A B).hom ≫ (β_ (F.obj A) (F.obj B)).hom) :
    L.map (β_ A B).hom ≫ (δ' B A).hom = (δ' A B).hom ≫ (β_ (L.obj A) (L.obj B)).hom := by
  rw [hδ, hδ, NatTrans.naturality_assoc, reassoc_of% h, Category.assoc, Category.assoc,
    BraidedCategory.braiding_naturality]

variable {u : F.obj (𝟙_ C) ⟶ 𝟙_ D} {u' : L.obj (𝟙_ C) ⟶ 𝟙_ D}
  (hu : u' = α.inv.app (𝟙_ C) ≫ u)
include hu

/-- **The left unitor transports along an isomorphism of functors.** -/
private theorem transport_leftUnitality (A : C)
    (h : F.map (λ_ A).hom = (δ (𝟙_ C) A).hom ≫ (u ▷ F.obj A) ≫ (λ_ (F.obj A)).hom) :
    L.map (λ_ A).hom = (δ' (𝟙_ C) A).hom ≫ (u' ▷ L.obj A) ≫ (λ_ (L.obj A)).hom := by
  rw [map_eq_conj_of_map_eq α h]
  simp only [hδ, hu, Category.assoc, ← leftUnitor_naturality, ← id_tensorHom,
    ← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id,
    Iso.hom_inv_id_app_assoc]

/-- **The right unitor transports along an isomorphism of functors.** -/
private theorem transport_rightUnitality (A : C)
    (h : F.map (ρ_ A).hom = (δ A (𝟙_ C)).hom ≫ (F.obj A ◁ u) ≫ (ρ_ (F.obj A)).hom) :
    L.map (ρ_ A).hom = (δ' A (𝟙_ C)).hom ≫ (L.obj A ◁ u') ≫ (ρ_ (L.obj A)).hom := by
  rw [map_eq_conj_of_map_eq α h]
  simp only [hδ, hu, Category.assoc, ← rightUnitor_naturality, ← id_tensorHom,
    ← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id,
    Iso.hom_inv_id_app_assoc]

end Transport

namespace Stacks.SheafOfModules

universe w w' v u₁ v' u'

attribute [local instance] Strict.monoidalUnderlyingRingSheaf Strict.braidedUnderlyingRingSheaf

variable {X : AlgebraicGeometry.RingedTopos.{v, u₁, w}}
    {Y : AlgebraicGeometry.RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
  {L : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O) ⥤
    _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O)}
  (α : f.pullbackModules ≅ L)

/-- The transported comparison of Stacks 03EL is the comparison of the base conjugated by `α`,
with the tensor product of the components of `α` taken in the strict monoidal structure. -/
theorem pullbackTensorIsoTransport_hom_eq
    (M N : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) :
    (Iso.hom (X := L.obj (M ⊗ N)) (Y := L.obj M ⊗ L.obj N)
        (pullbackTensorIsoTransport f α M N)) =
      α.inv.app (M ⊗ N) ≫ RingedToposPullback.pullbackTensorComparison f M N ≫
        (α.hom.app M ⊗ₘ α.hom.app N) := by
  rw [Strict.tensorHom_eq_tensorSheafBifunctor_map]
  rfl

/-- **The transported comparison of Stacks 03EL is natural in its second variable**, in
whiskered form for the strict monoidal structure. -/
theorem pullbackTensorIsoTransport_whiskerLeft_naturality
    (M : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
    {N N' : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)} (b : N ⟶ N') :
    L.map (M ◁ b) ≫ (Iso.hom (X := L.obj (M ⊗ N')) (Y := L.obj M ⊗ L.obj N')
        (pullbackTensorIsoTransport f α M N')) =
      (Iso.hom (X := L.obj (M ⊗ N)) (Y := L.obj M ⊗ L.obj N)
        (pullbackTensorIsoTransport f α M N)) ≫ (L.obj M ◁ L.map b) := by
  have h := pullbackTensorIsoTransport_hom_naturality f α (𝟙 M) b
  rw [L.map_id] at h
  rw [Strict.whiskerLeft_eq_tensorSheafBifunctor_map,
      Strict.whiskerLeft_eq_tensorSheafBifunctor_map]
  exact h

/-- **The transported comparison of Stacks 03EL is natural in its first variable**, in
whiskered form for the strict monoidal structure. -/
theorem pullbackTensorIsoTransport_whiskerRight_naturality
    {M M' : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)} (a : M ⟶ M')
    (N : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) :
    L.map (a ▷ N) ≫ (Iso.hom (X := L.obj (M' ⊗ N)) (Y := L.obj M' ⊗ L.obj N)
        (pullbackTensorIsoTransport f α M' N)) =
      (Iso.hom (X := L.obj (M ⊗ N)) (Y := L.obj M ⊗ L.obj N)
        (pullbackTensorIsoTransport f α M N)) ≫ (L.map a ▷ L.obj N) := by
  have h := pullbackTensorIsoTransport_hom_naturality f α a (𝟙 N)
  rw [L.map_id] at h
  rw [Strict.whiskerRight_eq_tensorSheafBifunctor_map,
    Strict.whiskerRight_eq_tensorSheafBifunctor_map]
  exact h

/-- **The comparison of Stacks 03EL read through an identification of the pullback is compatible
with the associator** of the strict monoidal structure of Tag 01CA. -/
theorem pullbackTensorIsoTransport_associativity
    (M N K : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) :
    L.map (α_ M N K).hom ≫ (Iso.hom (X := L.obj (M ⊗ (N ⊗ K))) (Y := L.obj M ⊗ L.obj (N ⊗ K))
        (pullbackTensorIsoTransport f α M (N ⊗ K))) ≫
        (L.obj M ◁ (Iso.hom (X := L.obj (N ⊗ K)) (Y := L.obj N ⊗ L.obj K)
        (pullbackTensorIsoTransport f α N K))) =
      (Iso.hom (X := L.obj ((M ⊗ N) ⊗ K)) (Y := L.obj (M ⊗ N) ⊗ L.obj K)
        (pullbackTensorIsoTransport f α (M ⊗ N) K)) ≫
        ((Iso.hom (X := L.obj (M ⊗ N)) (Y := L.obj M ⊗ L.obj N)
        (pullbackTensorIsoTransport f α M N)) ▷ L.obj K) ≫
          (α_ (L.obj M) (L.obj N) (L.obj K)).hom :=
  transport_associativity α (RingedToposPullback.pullbackTensorComparisonIso f)
    (fun A B => pullbackTensorIsoTransport f α A B)
    (fun A B => pullbackTensorIsoTransport_hom_eq f α A B) M N K
    (RingedToposPullback.associativity f M N K)

/-- **The comparison of Stacks 03EL read through an identification of the pullback is compatible
with the braiding** of the strict monoidal structure of Tag 01CA. -/
theorem pullbackTensorIsoTransport_braiding
    (M N : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) :
    L.map (β_ M N).hom ≫ (Iso.hom (X := L.obj (N ⊗ M)) (Y := L.obj N ⊗ L.obj M)
        (pullbackTensorIsoTransport f α N M)) =
      (Iso.hom (X := L.obj (M ⊗ N)) (Y := L.obj M ⊗ L.obj N)
        (pullbackTensorIsoTransport f α M N)) ≫ (β_ (L.obj M) (L.obj N)).hom :=
  transport_braiding α (RingedToposPullback.pullbackTensorComparisonIso f)
    (fun A B => pullbackTensorIsoTransport f α A B)
    (fun A B => pullbackTensorIsoTransport_hom_eq f α A B) M N
    (RingedToposPullback.braiding f M N)

/-- **The comparison of Stacks 03EL read through an identification of the pullback is compatible
with the left unitor** of the strict monoidal structure of Tag 01CA, the units being matched by
`Stacks.SheafOfModules.pullbackUnitIsoTransport`. -/
theorem pullbackTensorIsoTransport_leftUnitality
    (M : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) :
    L.map (λ_ M).hom = (Iso.hom (X := L.obj ((𝟙_ _) ⊗ M)) (Y := L.obj (𝟙_ _) ⊗ L.obj M)
        (pullbackTensorIsoTransport f α (𝟙_ _) M)) ≫
      ((pullbackUnitIsoTransport f α).hom ▷ L.obj M) ≫ (λ_ (L.obj M)).hom :=
  transport_leftUnitality α (RingedToposPullback.pullbackTensorComparisonIso f)
    (fun A B => pullbackTensorIsoTransport f α A B)
    (fun A B => pullbackTensorIsoTransport_hom_eq f α A B)
    (u := (RingedToposPullback.pullbackUnitComparison f).hom) rfl M
    (RingedToposPullback.leftUnitality f M)

/-- **The comparison of Stacks 03EL read through an identification of the pullback is compatible
with the right unitor** of the strict monoidal structure of Tag 01CA, the units being matched by
`Stacks.SheafOfModules.pullbackUnitIsoTransport`. -/
theorem pullbackTensorIsoTransport_rightUnitality
    (M : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) :
    L.map (ρ_ M).hom = (Iso.hom (X := L.obj (M ⊗ (𝟙_ _))) (Y := L.obj M ⊗ L.obj (𝟙_ _))
        (pullbackTensorIsoTransport f α M (𝟙_ _))) ≫
      (L.obj M ◁ (pullbackUnitIsoTransport f α).hom) ≫ (ρ_ (L.obj M)).hom :=
  transport_rightUnitality α (RingedToposPullback.pullbackTensorComparisonIso f)
    (fun A B => pullbackTensorIsoTransport f α A B)
    (fun A B => pullbackTensorIsoTransport_hom_eq f α A B)
    (u := (RingedToposPullback.pullbackUnitComparison f).hom) rfl M
    (RingedToposPullback.rightUnitality f M)

end Stacks.SheafOfModules

end
