module

public import StacksFrontier.AlgebraicGeometry.Stacks.HomFromTruncations
public import StacksFrontier.Deformation.Artin.FormalObject.ApproximationRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.IsomSpaceFpqcSheaf

/-!
# Full faithfulness of the approximation functor for algebraic stacks

Let `p : F ⥤ (big fppf site over S)` be a category fibred in groupoids. The approximation
functor of **Stacks 07X6** sends an object of `F` over the spectrum of a Noetherian complete
local `S`-algebra to the system of its restrictions to the infinitesimal thickenings of the
closed point. **Stacks 07X8** says it is an equivalence when `p` is an algebraic stack over a
locally Noetherian scheme. This file proves the first half of the source's Case III: the
functor is **fully faithful** as soon as the isomorphism presheaves `Isom(x, y)` of `p` are
algebraic spaces (condition (2) of Stacks 045G), in particular for every algebraic stack.

The source's argument: "As `𝒳` is an algebraic stack `Isom(x, x')` is representable by an
algebraic space `I` over `Spec(R)`. Applying Case II to `I` over `Spec(R)` implies immediately
that (07X6) is fully faithful on fibre categories over `Spec(R)`. Hence the functor is fully
faithful by Categories, Lemma 003Z." The fibrewise statement is
`AlgebraicGeometry.Stack.existsUnique_hom_of_compatible_truncations`; the passage from fibre
categories to the whole functor is done here directly: a morphism of formal objects induces a
morphism of complete local bases (`Deformation.Artin.FormalObject.Hom.baseMap`), any morphism
of `F` over that base map factors through a cartesian lift, and the remaining morphism lies in
a fibre.

## Main results

* `Deformation.Artin.faithful_of_isApproximationFunctor_of_isAlgebraicSpaceIsom` and
  `Deformation.Artin.full_of_isApproximationFunctor_of_isAlgebraicSpaceIsom`: faithfulness and
  fullness of any functor satisfying the equations of the approximation functor.
* `Deformation.Artin.fullyFaithful_approximationFunctor_of_isAlgebraicSpaceIsomPresheaf`: the
  same for the approximation functor of a category fibred in groupoids whose isomorphism
  presheaves are algebraic spaces, and
  `Deformation.Artin.fullyFaithful_approximationFunctor_of_isAlgebraicStack` for an algebraic
  stack.
* `Deformation.Artin.full_approximationFunctor_algebraicStacks`,
  `Deformation.Artin.faithful_approximationFunctor_algebraicStacks`: the two halves for an object
  of the 2-category `AlgebraicGeometry.Stack.AlgebraicStacks`.

## Implementation notes

The source assumes `S` locally Noetherian; full faithfulness does not need it, and it is not
imposed. Nor does it need `p` to be a stack, nor the existence of a smooth presentation: only
the isomorphism presheaves enter.

## References

* [Stacks Project, Tag 07X8](https://stacks.math.columbia.edu/tag/07X8)
* [Stacks Project, Tag 003Z](https://stacks.math.columbia.edu/tag/003Z)
-/

@[expose] public noncomputable section

namespace Deformation.Artin

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u v w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : Type v} [Category.{w} F] {p : F ⥤ BigFppfOver B S hS}

/-- The isomorphism presheaves of `p` are algebraic spaces: condition (2) of Stacks 045G, for a
category over the big fppf site written through its structure functor. -/
abbrev IsAlgebraicSpaceIsom (p : F ⥤ BigFppfOver B S hS) [p.IsFibered] : Prop :=
  ∀ (U : BigFppfOver B S hS) (x y : p.Fiber U),
    ∃ Fsp : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace B U.left.1 U.left.2 Fsp ∧
        Nonempty (Fsp ⋙ uliftFunctor.{w, u} ≅
          ((Over.iteratedSliceBackward U).op ⋙ p.isomPresheaf x y) ⋙ uliftFunctor.{u, w})

/-- The restriction maps of an approximation functor, read in schemes through the identifications
of their source and target with the infinitesimal thickenings of the complete local base. -/
private lemma toScheme_map_eq_adicThickeningι {A A' : FormalBase S} (h : A' = A)
    (hA : B.Contains (Spec (.of A.R))) (c : ∀ n, B.Contains (A'.truncation n)) (n : ℕ)
    {U W : BigFppfOver B S hS} (hU : U = baseOver B S hS A hA)
    (hW : W = truncationOver B S hS A' c n) (f : W ⟶ U)
    (hf : (BigFppfOver.toScheme B S hS).map (eqToHom hW.symm ≫ f ≫ eqToHom hU) =
      adicThickeningι A'.R (maximalIdeal A'.R) n ≫
        eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) h)) :
    (BigFppfOver.toScheme B S hS).map f ≫
        eqToHom ((congrArg (BigFppfOver.toScheme B S hS).obj hU).trans
          (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) h.symm)) =
      eqToHom (congrArg (BigFppfOver.toScheme B S hS).obj hW) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A'.R ^ (n + 1)))) := by
  subst h hU hW
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf ⊢
  exact hf

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **Morphisms out of a complete local object, from the restrictions.** For an approximation
functor `G` of `p` and a complete local object `x`, a compatible family of morphisms from the
levels of `G x` to an object `y` over the base of `x`, lying over the restriction maps, comes
from a unique morphism `x ⟶ y` over the identity. -/
theorem existsUnique_hom_of_isApproximationFunctor [p.IsFibered] (hp : p.IsFiberedInGroupoids)
    (hI : IsAlgebraicSpaceIsom p)
    {G : CompleteLocalObjects B S hS p ⥤ FormalObject B S hS p}
    (r : ∀ (x : CompleteLocalObjects B S hS p) (n : ℕ), (G.obj x).level n ⟶ x.obj.1)
    (hb : ∀ x, (G.obj x).base = chosenBase B S hS p x.obj)
    (htrans : ∀ x n, (G.obj x).transition n ≫ r x (n + 1) = r x n)
    (hι : ∀ x n,
      (BigFppfOver.toScheme B S hS).map
          (eqToHom ((G.obj x).level_eq n).symm ≫ p.map (r x n) ≫
            eqToHom (chosenBase_eq B S hS p x.obj)) =
        adicThickeningι (G.obj x).base.R
          (maximalIdeal (G.obj x).base.R) n ≫
          eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) (hb x)))
    (x : CompleteLocalObjects B S hS p) {y : F} (hy : p.obj y = p.obj x.obj.1)
    (m : ∀ n, (G.obj x).level n ⟶ y) [∀ n, p.IsHomLift (p.map (r x n)) (m n)]
    (hm : ∀ n, (G.obj x).transition n ≫ m (n + 1) = m n) :
    ∃! φ : x.obj.1 ⟶ y, p.IsHomLift (𝟙 (p.obj x.obj.1)) φ ∧ ∀ n, r x n ≫ φ = m n := by
  let A := (G.obj x).base
  have hR : IsNoetherianCompleteLocalRing A.R := ⟨A.noetherian, inferInstance, A.complete⟩
  have hT : (BigFppfOver.toScheme B S hS).obj (p.obj x.obj.1) = Spec (.of A.R) :=
    (congrArg (BigFppfOver.toScheme B S hS).obj (chosenBase_eq B S hS p x.obj)).trans
      (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) (hb x).symm)
  have hW : ∀ n, (BigFppfOver.toScheme B S hS).obj (p.obj ((G.obj x).level n)) =
      Spec (.of (A.R ⧸ maximalIdeal A.R ^ (n + 1))) := fun n =>
    congrArg (BigFppfOver.toScheme B S hS).obj ((G.obj x).level_eq n)
  let eT := eqToIso hT
  let eW := fun n => eqToIso (hW n)
  have hιx : ∀ n, (BigFppfOver.toScheme B S hS).map (p.map (r x n)) ≫ eT.hom =
      (eW n).hom ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A.R ^ (n + 1)))) := fun n =>
    toScheme_map_eq_adicThickeningι (hb x) (chosenContains B S hS p x.obj)
      (G.obj x).contains n (chosenBase_eq B S hS p x.obj) ((G.obj x).level_eq n)
      (p.map (r x n)) (hι x n)
  exact Stack.existsUnique_hom_of_compatible_truncations p hp (p.obj x.obj.1) ⟨x.obj.1, rfl⟩
    ⟨y, hy⟩ (hI _ _ _) hR (fun n => maximalIdeal A.R ^ (n + 1))
    (fun n => Ideal.pow_le_self n.succ_ne_zero) (fun n => Ideal.pow_le_pow_right (Nat.le_succ _))
    (fun n => ⟨n + 1, le_rfl⟩) (fun k => ⟨k, Ideal.pow_le_pow_right (Nat.le_succ k)⟩) eT
    (fun n => p.obj ((G.obj x).level n)) eW (fun n => p.map (r x n)) hιx
    (fun n => p.map ((G.obj x).transition n))
    (fun n => by rw [← p.map_comp, htrans]) (fun n => (G.obj x).level n) (fun n => r x n)
    (fun n => (G.obj x).transition n) (htrans x) m hm

/-- Two transport isomorphisms which are mutually inverse cancel. -/
private lemma eqToHom_comp_eqToHom_comp_of_eq {C : Type*} [Category C] {X Y Z : C}
    (h : X = Y) (h' : Y = X) (f : X ⟶ Z) : eqToHom h ≫ eqToHom h' ≫ f = f := by
  subst h
  simp

/-- A morphism conjugated by transport isomorphisms into a monomorphism is a monomorphism. -/
private lemma mono_of_mono_eqToHom_comp_comp_eqToHom {C : Type*} [Category C] {X Y Z W : C}
    (h : X = Y) (h' : Z = W) (g : Y ⟶ Z) [Mono (eqToHom h ≫ g ≫ eqToHom h')] : Mono g := by
  subst h h'
  simpa using (inferInstance : Mono (eqToHom (rfl : X = X) ≫ g ≫ eqToHom (rfl : Z = Z)))

/-- In a category fibred in groupoids, a morphism lying over a monomorphism of the base is a
monomorphism. -/
private lemma cancel_of_isHomLift_mono (hp : p.IsFiberedInGroupoids) {a b c : F}
    (φ : b ⟶ c) [Mono (p.map φ)] {u v : a ⟶ b} (h : u ≫ φ = v ≫ φ) : u = v := by
  have hmap : p.map u = p.map v := by
    rw [← cancel_mono (p.map φ), ← p.map_comp, ← p.map_comp, h]
  have : p.IsHomLift (p.map u) v := by
    rw [hmap]
    infer_instance
  exact hp.hom_ext (f := p.map φ) (p.map u) φ h

/-- A morphism of `F` which, through the identifications of its source and target with an
infinitesimal thickening and the complete local base, is the inclusion of the thickening, is a
monomorphism. -/
private lemma mono_map_of_toScheme_map_eq_adicThickeningι {A A' : FormalBase S} (h : A' = A)
    (hA : B.Contains (Spec (.of A.R))) (c : ∀ n, B.Contains (A'.truncation n)) (n : ℕ)
    {a b : F} (hW : p.obj a = truncationOver B S hS A' c n) (hU : p.obj b = baseOver B S hS A hA)
    (f : a ⟶ b)
    (hf : (BigFppfOver.toScheme B S hS).map (eqToHom hW.symm ≫ p.map f ≫ eqToHom hU) =
      adicThickeningι A'.R (maximalIdeal A'.R) n ≫
        eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) h)) :
    Mono (p.map f) := by
  have : Mono ((BigFppfOver.toScheme B S hS).map (eqToHom hW.symm ≫ p.map f ≫ eqToHom hU)) := by
    rw [hf]
    let f : CommRingCat.of A'.R ⟶ CommRingCat.of (A'.R ⧸ maximalIdeal A'.R ^ (n + 1)) :=
      CommRingCat.ofHom (Ideal.Quotient.mk _)
    have : IsClosedImmersion (Spec.map f) :=
      IsClosedImmersion.spec_of_surjective f Ideal.Quotient.mk_surjective
    have : Mono (Spec.map f) := inferInstance
    exact @mono_comp _ _ _ _ _ (Spec.map f) this
      (eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) h)) inferInstance
  have := (BigFppfOver.toScheme B S hS).mono_of_mono_map this
  exact mono_of_mono_eqToHom_comp_comp_eqToHom hW.symm hU _

/-- **Unique extension of compatible families from the restrictions**, the fibrewise half of
full faithfulness of an approximation functor `G` of `p`: for every choice of restriction maps
`r` satisfying the equations of `Deformation.Artin.IsApproximationFunctor`, every complete local
object `x` and every object `y` over the base of `x`, a compatible family of morphisms from the
levels of `G x` to `y` lying over the restriction maps comes from a unique morphism `x ⟶ y` over
the identity.

For a category fibred in groupoids whose isomorphism presheaves are algebraic spaces this is
`Deformation.Artin.existsUnique_hom_of_isApproximationFunctor`; Categories, Lemma 003Z then makes
the functor fully faithful, which is
`Deformation.Artin.faithful_of_isApproximationFunctor_of_hasUniqueExtensions` and
`Deformation.Artin.full_of_isApproximationFunctor_of_hasUniqueExtensions`. -/
def HasUniqueExtensions (G : CompleteLocalObjects B S hS p ⥤ FormalObject B S hS p) : Prop :=
  ∀ (r : ∀ (x : CompleteLocalObjects B S hS p) (n : ℕ), (G.obj x).level n ⟶ x.obj.1)
    (hb : ∀ x, (G.obj x).base = chosenBase B S hS p x.obj),
    (∀ x n, (G.obj x).transition n ≫ r x (n + 1) = r x n) →
    (∀ x n,
      (BigFppfOver.toScheme B S hS).map
          (eqToHom ((G.obj x).level_eq n).symm ≫ p.map (r x n) ≫
            eqToHom (chosenBase_eq B S hS p x.obj)) =
        adicThickeningι (G.obj x).base.R
          (maximalIdeal (G.obj x).base.R) n ≫
          eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) (hb x))) →
    ∀ (x : CompleteLocalObjects B S hS p) {y : F} (_ : p.obj y = p.obj x.obj.1)
      (m : ∀ n, (G.obj x).level n ⟶ y), (∀ n, p.IsHomLift (p.map (r x n)) (m n)) →
      (∀ n, (G.obj x).transition n ≫ m (n + 1) = m n) →
      ∃! φ : x.obj.1 ⟶ y, p.IsHomLift (𝟙 (p.obj x.obj.1)) φ ∧ ∀ n, r x n ≫ φ = m n

/-- The isomorphism presheaves of `p` being algebraic spaces, every approximation functor of `p`
has unique extensions. -/
theorem hasUniqueExtensions_of_isAlgebraicSpaceIsom [p.IsFibered] (hp : p.IsFiberedInGroupoids)
    (hI : IsAlgebraicSpaceIsom p) (G : CompleteLocalObjects B S hS p ⥤ FormalObject B S hS p) :
    HasUniqueExtensions G := fun r hb htrans hι x _ hy m hml hm =>
  have := hml
  existsUnique_hom_of_isApproximationFunctor hp hI r hb htrans hι x hy m hm

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **Faithfulness of the approximation functor from unique extensions** (Stacks 07X8, Case III,
with Categories, Lemma 003Z). -/
theorem faithful_of_isApproximationFunctor_of_hasUniqueExtensions [p.IsFibered]
    (hp : p.IsFiberedInGroupoids)
    {G : CompleteLocalObjects B S hS p ⥤ FormalObject B S hS p} (hU : HasUniqueExtensions G)
    (hG : IsApproximationFunctor B S hS p G) : G.Faithful := by
  obtain ⟨r, hb, -, htrans, hnat, hι⟩ := hG
  constructor
  intro x y f g hfg
  have hrfg : ∀ n, r x n ≫ f.1.1 = r x n ≫ g.1.1 := fun n => by
    rw [← hnat x y f n, ← hnat x y g n, hfg]
  have hpfg : p.map f.1.1 = p.map g.1.1 := by
    have key : ∀ n, (eqToHom ((G.obj x).level_eq n).symm ≫ p.map (r x n) ≫
        eqToHom (chosenBase_eq B S hS p x.obj)) ≫
          (eqToHom (chosenBase_eq B S hS p x.obj).symm ≫ p.map f.1.1) =
        (eqToHom ((G.obj x).level_eq n).symm ≫ p.map (r x n) ≫
          eqToHom (chosenBase_eq B S hS p x.obj)) ≫
          (eqToHom (chosenBase_eq B S hS p x.obj).symm ≫ p.map g.1.1) := by
      intro n
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [← p.map_comp, ← p.map_comp, hrfg n]
    exact (cancel_epi (eqToHom _)).1
      (toScheme_restriction B S hS p (G := G) (r := r) (hb := hb) hι x _ _ key)
  have hg : p.IsHomLift (p.map f.1.1) g.1.1 := by
    rw [hpfg]
    infer_instance
  let φ := hp.fill (f := p.map f.1.1) (g := 𝟙 _) (f' := p.map f.1.1) (by simp) f.1.1 g.1.1
  have hφ : p.IsHomLift (𝟙 _) φ := hp.fill_isHomLift _ _ _
  have hφc : φ ≫ f.1.1 = g.1.1 := hp.fill_fac _ _ _
  obtain ⟨_, -, huniq⟩ := hU r hb htrans hι x rfl (fun n => r x n) (fun _ => inferInstance)
    (htrans x)
  have h1 := huniq (𝟙 _) ⟨inferInstance, fun n => Category.comp_id _⟩
  have h2 := huniq φ ⟨hφ, fun n => by
    refine hp.hom_ext (f := p.map f.1.1) (p.map (r x n)) f.1.1 ?_
    rw [Category.assoc, hφc, hrfg n]⟩
  refine (wideSubcategoryInclusion (localBaseMaps B S hS p)).map_injective ?_
  refine ObjectProperty.hom_ext (P := IsCompleteLocalObject B S hS p) ?_
  change f.1.1 = g.1.1
  rw [← hφc, h2, ← h1, Category.id_comp]

/-- **Faithfulness of the approximation functor** (Stacks 07X8, Case III), for a category
fibred in groupoids whose isomorphism presheaves are algebraic spaces. -/
theorem faithful_of_isApproximationFunctor_of_isAlgebraicSpaceIsom [p.IsFibered]
    (hp : p.IsFiberedInGroupoids) (hI : IsAlgebraicSpaceIsom p)
    {G : CompleteLocalObjects B S hS p ⥤ FormalObject B S hS p}
    (hG : IsApproximationFunctor B S hS p G) : G.Faithful :=
  faithful_of_isApproximationFunctor_of_hasUniqueExtensions hp
    (hasUniqueExtensions_of_isAlgebraicSpaceIsom hp hI G) hG

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The map of complete local bases induced by a morphism of formal objects preserves the closed
points. -/
private theorem FormalObject.Hom.baseMap_closedPoint {X Y : FormalObject B S hS p} (Φ : X ⟶ Y) :
    Φ.baseMap (closedPoint X.base.R) = closedPoint Y.base.R := by
  have hψ : (BigFppfOver.toScheme B S hS).map
        (eqToHom (X.level_eq 0).symm ≫ p.map (Φ.app 0) ≫ eqToHom (Y.level_eq 0)) ≫
        adicThickeningι Y.base.R (maximalIdeal Y.base.R) 0 =
      adicThickeningι X.base.R (maximalIdeal X.base.R) 0 ≫ Φ.baseMap :=
    Φ.baseMap_spec.2 0
  have hpt : adicThickeningι Y.base.R (maximalIdeal Y.base.R) 0
        ((BigFppfOver.toScheme B S hS).map (eqToHom (X.level_eq 0).symm ≫
          p.map (Φ.app 0) ≫ eqToHom (Y.level_eq 0))
          (closedPoint (X.base.R ⧸ maximalIdeal X.base.R ^ (0 + 1)))) =
      Φ.baseMap (adicThickeningι X.base.R (maximalIdeal X.base.R) 0
        (closedPoint (X.base.R ⧸ maximalIdeal X.base.R ^ (0 + 1)))) :=
    congrArg (fun e : adicThickening X.base.R (maximalIdeal X.base.R) 0 ⟶
        Spec (.of Y.base.R) => e (closedPoint (X.base.R ⧸ maximalIdeal X.base.R ^ (0 + 1)))) hψ
  have hz : (BigFppfOver.toScheme B S hS).map
      (eqToHom (X.level_eq 0).symm ≫ p.map (Φ.app 0) ≫ eqToHom (Y.level_eq 0))
      (closedPoint (X.base.R ⧸ maximalIdeal X.base.R ^ (0 + 1))) =
      closedPoint (Y.base.R ⧸ maximalIdeal Y.base.R ^ (0 + 1)) :=
    eq_closedPoint_of_adicThickening 0 _
  rw [hz, adicThickeningι_closedPoint, adicThickeningι_closedPoint] at hpt
  exact hpt.symm

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The base map of a morphism of formal objects, transported to chosen complete local bases, is
the image of a morphism of the big fppf site over `S`. -/
private lemma exists_baseOver_hom_toScheme_map_eq {X Y : FormalObject B S hS p} (Φ : X ⟶ Y)
    {x y : CompleteLocalObjectsFull B S hS p} (hx : X.base = chosenBase B S hS p x)
    (hy : Y.base = chosenBase B S hS p y) :
    ∃ ab : baseOver B S hS (chosenBase B S hS p x) (chosenContains B S hS p x) ⟶
      baseOver B S hS (chosenBase B S hS p y) (chosenContains B S hS p y),
      (BigFppfOver.toScheme B S hS).map ab =
        eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) hx).symm ≫ Φ.baseMap ≫
          eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) hy) := by
  have hαS :
      (eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) hx).symm ≫ Φ.baseMap ≫
          eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) hy)) ≫
        (chosenBase B S hS p y).toS = (chosenBase B S hS p x).toS := by
    rw [Category.assoc, Category.assoc, eqToHom_formalBase_toS hy,
      Φ.baseMap_spec.1, ← eqToHom_formalBase_toS hx, ← Category.assoc,
      eqToHom_trans, eqToHom_refl, Category.id_comp]
  exact ⟨Over.homMk (ObjectProperty.homMk
      (X := B.obj (chosenContains B S hS p x))
      (Y := B.obj (chosenContains B S hS p y)) _)
    (ObjectProperty.hom_ext _ hαS), rfl⟩

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- A morphism of formal objects `G x ⟶ G y` between the images of complete local objects under an
approximation functor lies over a morphism `b` of the bases of `x` and `y`, compatible with the
restriction maps, such that every morphism `x ⟶ y` over `b` preserves the closed points. -/
private lemma exists_base_hom_of_formalObject_hom
    {G : CompleteLocalObjects B S hS p ⥤ FormalObject B S hS p}
    (r : ∀ (x : CompleteLocalObjects B S hS p) (n : ℕ), (G.obj x).level n ⟶ x.obj.1)
    (hb : ∀ x, (G.obj x).base = chosenBase B S hS p x.obj)
    (hι : ∀ x n,
      (BigFppfOver.toScheme B S hS).map
          (eqToHom ((G.obj x).level_eq n).symm ≫ p.map (r x n) ≫
            eqToHom (chosenBase_eq B S hS p x.obj)) =
        adicThickeningι (G.obj x).base.R
          (maximalIdeal (G.obj x).base.R) n ≫
          eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) (hb x)))
    {x y : CompleteLocalObjects B S hS p} (Φ : G.obj x ⟶ G.obj y) :
    ∃ b : p.obj x.obj.1 ⟶ p.obj y.obj.1,
      (∀ n, p.map (r x n) ≫ b = p.map (Φ.app n) ≫ p.map (r y n)) ∧
        ∀ f : x.obj ⟶ y.obj, p.map f.1 = b → localBaseMaps B S hS p f := by
  obtain ⟨ab, hab⟩ := exists_baseOver_hom_toScheme_map_eq Φ (hb x) (hb y)
  have hψ : ∀ n, (BigFppfOver.toScheme B S hS).map
        (eqToHom ((G.obj x).level_eq n).symm ≫ p.map (Φ.app n) ≫
          eqToHom ((G.obj y).level_eq n)) ≫
        adicThickeningι (G.obj y).base.R (maximalIdeal (G.obj y).base.R) n =
      adicThickeningι (G.obj x).base.R (maximalIdeal (G.obj x).base.R) n ≫ Φ.baseMap :=
    Φ.baseMap_spec.2
  have hρab : ∀ n,
      (eqToHom ((G.obj x).level_eq n).symm ≫ p.map (r x n) ≫
          eqToHom (chosenBase_eq B S hS p x.obj)) ≫ ab =
        (eqToHom ((G.obj x).level_eq n).symm ≫ p.map (Φ.app n) ≫
            eqToHom ((G.obj y).level_eq n)) ≫
          (eqToHom ((G.obj y).level_eq n).symm ≫ p.map (r y n) ≫
            eqToHom (chosenBase_eq B S hS p y.obj)) := by
    intro n
    refine (BigFppfOver.toScheme B S hS).map_injective ?_
    rw [Functor.map_comp, hι x n, hab, Functor.map_comp, hι y n]
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (fun z => adicThickeningι (G.obj x).base.R
      (maximalIdeal (G.obj x).base.R) n ≫ z) (eqToHom_comp_eqToHom_comp_of_eq _ _ _)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun z => z ≫ eqToHom
      (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) (hb y))) (hψ n).symm) ?_
    exact Category.assoc _ _ _
  refine ⟨eqToHom (chosenBase_eq B S hS p x.obj) ≫ ab ≫
    eqToHom (chosenBase_eq B S hS p y.obj).symm, fun n => ?_, fun f hf => ?_⟩
  · simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      eqToHom_trans, Category.comp_id] using congrArg (fun z => eqToHom ((G.obj x).level_eq n) ≫
        z ≫ eqToHom (chosenBase_eq B S hS p y.obj).symm) (hρab n)
  have hbm : baseMap B S hS p f = (BigFppfOver.toScheme B S hS).map ab := by
    change (BigFppfOver.toScheme B S hS).map
      (eqToHom (chosenBase_eq B S hS p x.obj).symm ≫ p.map f.1 ≫
        eqToHom (chosenBase_eq B S hS p y.obj)) = _
    rw [hf]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      eqToHom_trans, Category.comp_id]
  change baseMap B S hS p f (closedPoint (chosenBase B S hS p x.obj).R) =
    closedPoint (chosenBase B S hS p y.obj).R
  rw [hbm, hab]
  change eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) (hb y))
      (Φ.baseMap (eqToHom
        (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) (hb x)).symm
        (closedPoint (chosenBase B S hS p x.obj).R))) =
    closedPoint (chosenBase B S hS p y.obj).R
  rw [eqToHom_symm_formalBase_closedPoint (hb x), Φ.baseMap_closedPoint,
    eqToHom_formalBase_closedPoint (hb y)]

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **Fullness of the approximation functor from unique extensions** (Stacks 07X8, Case III,
with Categories, Lemma 003Z).  A morphism of formal objects induces a morphism of complete local
bases; a cartesian lift of it to the target, followed by the morphism of the fibre over the
source given by the unique extension, is a preimage. -/
theorem full_of_isApproximationFunctor_of_hasUniqueExtensions [p.IsFibered]
    (hp : p.IsFiberedInGroupoids)
    {G : CompleteLocalObjects B S hS p ⥤ FormalObject B S hS p} (hU : HasUniqueExtensions G)
    (hG : IsApproximationFunctor B S hS p G) : G.Full := by
  obtain ⟨r, hb, -, htrans, hnat, hι⟩ := hG
  constructor
  intro x y Φ
  obtain ⟨b, hcompat, hloc⟩ := exists_base_hom_of_formalObject_hom r hb hι Φ
  obtain ⟨y', c, hc⟩ := hp.exists_lift' b y.obj.1 rfl
  have hy' : p.obj y' = p.obj x.obj.1 := IsHomLift.domain_eq p b c
  have hlift : ∀ n, p.IsHomLift (p.map (r x n) ≫ b) (Φ.app n ≫ r y n) := fun n => by
    rw [hcompat n, ← p.map_comp]
    infer_instance
  let m : ∀ n, (G.obj x).level n ⟶ y' := fun n =>
    hp.fill (f := b) (g := p.map (r x n)) (f' := p.map (r x n) ≫ b) rfl c (Φ.app n ≫ r y n)
  have hmlift : ∀ n, p.IsHomLift (p.map (r x n)) (m n) := fun n => hp.fill_isHomLift _ _ _
  have hmc : ∀ n, m n ≫ c = Φ.app n ≫ r y n := fun n => hp.fill_fac _ _ _
  have hm : ∀ n, (G.obj x).transition n ≫ m (n + 1) = m n := by
    intro n
    have : p.IsHomLift (p.map (r x n)) ((G.obj x).transition n ≫ m (n + 1)) := by
      have : p.IsHomLift (p.map ((G.obj x).transition n) ≫ p.map (r x (n + 1)))
          ((G.obj x).transition n ≫ m (n + 1)) := inferInstance
      rwa [← p.map_comp, htrans] at this
    refine hp.hom_ext (f := b) (p.map (r x n)) c ?_
    rw [Category.assoc, hmc, hmc, ← Category.assoc, Φ.naturality n, Category.assoc,
      htrans]
  obtain ⟨φ, ⟨hφ, hφr⟩, -⟩ := hU r hb htrans hι x hy' m hmlift hm
  have hf₀ : p.map (φ ≫ c) = b := (IsHomLift.eq_of_isHomLift (p := p) b (φ ≫ c)).symm
  let fm : x.obj ⟶ y.obj := ObjectProperty.homMk (φ ≫ c)
  refine ⟨⟨fm, hloc fm hf₀⟩, ?_⟩
  apply FormalObject.Hom.ext
  intro n
  have := mono_map_of_toScheme_map_eq_adicThickeningι (hb y) (chosenContains B S hS p y.obj)
    (G.obj y).contains n ((G.obj y).level_eq n) (chosenBase_eq B S hS p y.obj) (r y n) (hι y n)
  refine cancel_of_isHomLift_mono hp (r y n) ?_
  rw [hnat x y ⟨fm, hloc fm hf₀⟩ n]
  change r x n ≫ φ ≫ c = _
  rw [← Category.assoc, hφr n, hmc n]

/-- **Fullness of the approximation functor** (Stacks 07X8, Case III), for a category fibred in
groupoids whose isomorphism presheaves are algebraic spaces. -/
theorem full_of_isApproximationFunctor_of_isAlgebraicSpaceIsom [p.IsFibered]
    (hp : p.IsFiberedInGroupoids) (hI : IsAlgebraicSpaceIsom p)
    {G : CompleteLocalObjects B S hS p ⥤ FormalObject B S hS p}
    (hG : IsApproximationFunctor B S hS p G) : G.Full :=
  full_of_isApproximationFunctor_of_hasUniqueExtensions hp
    (hasUniqueExtensions_of_isAlgebraicSpaceIsom hp hI G) hG

/-- **Stacks 07X8, full faithfulness**: the approximation functor of Stacks 07X6 of a category
fibred in groupoids over the big fppf site of `S` whose isomorphism presheaves are algebraic
spaces is fully faithful. -/
theorem fullyFaithful_approximationFunctor_of_isAlgebraicSpaceIsomPresheaf
    (𝒳 : CatFiberedInGroupoids.{u, w, u + 1, v} (BigFppfOver B S hS))
    (h𝒳 : Stack.IsAlgebraicSpaceIsomPresheaf B S hS 𝒳) :
    (approximationFunctor B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids).Full ∧
      (approximationFunctor B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids).Faithful := by
  have : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  exact ⟨full_of_isApproximationFunctor_of_isAlgebraicSpaceIsom 𝒳.isFiberedInGroupoids h𝒳
      (approximationFunctorData B S hS _ _).2,
    faithful_of_isApproximationFunctor_of_isAlgebraicSpaceIsom 𝒳.isFiberedInGroupoids h𝒳
      (approximationFunctorData B S hS _ _).2⟩

/-- **Stacks 07X8, full faithfulness, for an algebraic stack**: the approximation functor of
Stacks 07X6 of an algebraic stack over `S` is fully faithful. -/
theorem fullyFaithful_approximationFunctor_of_isAlgebraicStack
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : Stack.IsAlgebraicStack.{u, v} B S hS 𝒳.val) :
    (approximationFunctor B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids).Full ∧
      (approximationFunctor B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids).Faithful :=
  fullyFaithful_approximationFunctor_of_isAlgebraicSpaceIsomPresheaf 𝒳
    (Stack.isAlgebraicSpaceIsomPresheaf_of_isAlgebraicStack B S hS 𝒳 h𝒳)

/-- **Stacks 07X8, fullness, for an object of the 2-category of algebraic stacks**: the
approximation functor of Stacks 07X6 of an algebraic stack over `S` is full. -/
theorem full_approximationFunctor_algebraicStacks (𝒳 : Stack.AlgebraicStacks.{u, v} B S hS) :
    (approximationFunctor B S hS 𝒳.val.val.p 𝒳.val.property).Full :=
  (fullyFaithful_approximationFunctor_of_isAlgebraicStack 𝒳.val 𝒳.property).1

/-- **Stacks 07X8, faithfulness, for an object of the 2-category of algebraic stacks**: the
approximation functor of Stacks 07X6 of an algebraic stack over `S` is faithful. -/
theorem faithful_approximationFunctor_algebraicStacks (𝒳 : Stack.AlgebraicStacks.{u, v} B S hS) :
    (approximationFunctor B S hS 𝒳.val.val.p 𝒳.val.property).Faithful :=
  (fullyFaithful_approximationFunctor_of_isAlgebraicStack 𝒳.val 𝒳.property).2

end Deformation.Artin

end
