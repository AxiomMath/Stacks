module

public import Mathlib.CategoryTheory.Presentable.Directed
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.FieldPoint

/-!
# Reducing a property of schemes to a field-valued point: directed inverse systems

[Stacks, Tag 0F06] asks the property `P` to pass to limits of *directed* inverse systems of
quasi-compact quasi-separated schemes with affine transition morphisms.
`AlgebraicGeometry.exists_field_point` asks it to pass to limits of arbitrary small cofiltered
diagrams, which is a stronger hypothesis. This file removes the difference: by Deligne's lemma
(`CategoryTheory.IsCardinalFiltered.exists_cardinal_directed` for the cardinal `ℵ₀`), every small
filtered category receives a final functor from a directed partial order, so every small
cofiltered limit is a limit over (the opposite of) a directed set, and the limit hypothesis for
directed sets implies the one for cofiltered diagrams.

## Main results

* `AlgebraicGeometry.limit_property_of_isCofiltered` — the limit hypothesis for directed sets
  implies the limit hypothesis for small cofiltered diagrams.
* `AlgebraicGeometry.exists_field_point_of_isDirected` — [Stacks, Tag 0F06] with the limit
  hypothesis for directed inverse systems, as in the source.

## References

* [Stacks Project, Tag 0F06](https://stacks.math.columbia.edu/tag/0F06)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry

/-- **A property passing to directed limits passes to cofiltered limits.** Let `P` be a property
of schemes over `B` which holds at the limit of every directed inverse system of quasi-compact
quasi-separated schemes over `B` with affine transition morphisms, as soon as it holds at every
stage. Then it holds at the limit of every small cofiltered diagram of such schemes.

By Deligne's lemma the filtered category `Iᵒᵖ` receives a final functor `F : α ⥤ Iᵒᵖ` from a
directed partial order `α`, so `F.leftOp : αᵒᵖ ⥤ I` is initial and the limit cone of `D`
restricts to a limit cone of `F.leftOp ⋙ D`, with the same cone point. -/
public theorem limit_property_of_isCofiltered {B : Scheme.{u}}
    (P : ∀ Y : Scheme.{u}, (Y ⟶ B) → Prop)
    (hLimit : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
      (D : Iᵒᵖ ⥤ Scheme.{u})
      [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
      [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
      (c : Cone D) (_ : IsLimit c)
      [CompactSpace c.pt] [QuasiSeparatedSpace c.pt]
      (f : c.pt ⟶ B) (fi : ∀ i, D.obj i ⟶ B),
      (∀ {i j : Iᵒᵖ} (a : i ⟶ j), D.map a ≫ fi j = fi i) →
      (∀ i, c.π.app i ≫ fi i = f) →
      (∀ i, P (D.obj i) (fi i)) → P c.pt f)
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) [CompactSpace c.pt] [QuasiSeparatedSpace c.pt]
    (f : c.pt ⟶ B) (fi : ∀ i, D.obj i ⟶ B)
    (hfi : ∀ {i j : I} (a : i ⟶ j), D.map a ≫ fi j = fi i)
    (hcf : ∀ i, c.π.app i ≫ fi i = f) (hP : ∀ i, P (D.obj i) (fi i)) : P c.pt f := by
  have : Fact Cardinal.aleph0.{u}.IsRegular := ⟨Cardinal.isRegular_aleph0⟩
  have : IsCardinalFiltered Iᵒᵖ Cardinal.aleph0.{u} :=
    (isCardinalFiltered_aleph0_iff Iᵒᵖ).2 inferInstance
  obtain ⟨α, _, hα, F, _⟩ := IsCardinalFiltered.exists_cardinal_directed Iᵒᵖ Cardinal.aleph0.{u}
  have : IsFiltered α := (isCardinalFiltered_aleph0_iff α).1 hα
  have : IsDirected α (· ≤ ·) := ⟨fun a b => by
    obtain ⟨k, f, g, -⟩ := IsFilteredOrEmpty.cocone_objs a b
    exact ⟨k, leOfHom f, leOfHom g⟩⟩
  have : Nonempty α := IsFiltered.nonempty
  have : F.leftOp.Initial := inferInstance
  have : ∀ {i j : αᵒᵖ} (a : i ⟶ j), IsAffineHom ((F.leftOp ⋙ D).map a) :=
    fun a => inferInstanceAs (IsAffineHom (D.map (F.leftOp.map a)))
  have : ∀ i, CompactSpace ((F.leftOp ⋙ D).obj i) :=
    fun i => inferInstanceAs (CompactSpace (D.obj (F.leftOp.obj i)))
  have : ∀ i, QuasiSeparatedSpace ((F.leftOp ⋙ D).obj i) :=
    fun i => inferInstanceAs (QuasiSeparatedSpace (D.obj (F.leftOp.obj i)))
  have : CompactSpace (c.whisker F.leftOp).pt := inferInstanceAs (CompactSpace c.pt)
  have : QuasiSeparatedSpace (c.whisker F.leftOp).pt :=
    inferInstanceAs (QuasiSeparatedSpace c.pt)
  exact hLimit (F.leftOp ⋙ D) (c.whisker F.leftOp)
    ((Functor.Initial.isLimitWhiskerEquiv F.leftOp c).symm hc) f
    (fun i => fi (F.leftOp.obj i)) (fun a => hfi (F.leftOp.map a)) (fun i => hcf _)
    (fun i => hP _)

/-- **Stacks Project, Tag 0F06.** Let `T` be a nonempty quasi-compact quasi-separated scheme and
`P` a property of quasi-compact quasi-separated schemes over `T` such that

1. `P` is invariant under thickenings;
2. if `T'` is the limit of a directed inverse system of quasi-compact quasi-separated schemes
   `Tᵢ` over `T` with affine transition morphisms and `P(Tᵢ)` holds for all `i`, then `P(T')`
   holds;
3. if `P(T')` holds, `Z ⊂ T'` is a closed subscheme and its complement `U` is quasi-compact, then
   `P(U)` or `P(Z)` holds;

and such that `P(T)` holds. Then there are a field `K` and a morphism `Spec K ⟶ T` with
`P(Spec K)`.

The limit hypothesis is the source's, for directed inverse systems; it is reduced to the one of
`AlgebraicGeometry.exists_field_point`, for small cofiltered diagrams, by
`AlgebraicGeometry.limit_property_of_isCofiltered`. The `[Nonempty T]` hypothesis is necessary,
as recorded at `AlgebraicGeometry.exists_field_point`. -/
@[stacks 0F06 "the limit hypothesis for directed inverse systems, as in the source"]
public theorem exists_field_point_of_isDirected {T : Scheme.{u}} [Nonempty T] [CompactSpace T]
    [QuasiSeparatedSpace T] (P : ∀ X : Scheme.{u}, (X ⟶ T) → Prop)
    (hThickening : ∀ {X X' : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      [CompactSpace X'] [QuasiSeparatedSpace X'] (i : X ⟶ X') (f : X' ⟶ T),
      IsThickening i → (P X (i ≫ f) ↔ P X' f))
    (hLimit : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
      (D : Iᵒᵖ ⥤ Scheme.{u})
      [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
      [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
      (c : Cone D) (_ : IsLimit c)
      [CompactSpace c.pt] [QuasiSeparatedSpace c.pt]
      (f : c.pt ⟶ T) (fi : ∀ i, D.obj i ⟶ T),
      (∀ {i j : Iᵒᵖ} (a : i ⟶ j), D.map a ≫ fi j = fi i) →
      (∀ i, c.π.app i ≫ fi i = f) →
      (∀ i, P (D.obj i) (fi i)) → P c.pt f)
    (hClosedOrOpen : ∀ {X : Scheme.{u}} [CompactSpace X]
      [QuasiSeparatedSpace X] (f : X ⟶ T) (J : X.IdealSheafData)
      [CompactSpace J.subscheme] [QuasiSeparatedSpace J.subscheme]
      (V : X.Opens) (_hV : (V : Set X) = (J.support : Set X)ᶜ)
      [CompactSpace V.toScheme] [QuasiSeparatedSpace V.toScheme],
      P X f → (P V.toScheme (V.ι ≫ f) ∨
        P J.subscheme (J.subschemeι ≫ f)))
    (hP : P T (𝟙 T)) :
    ∃ (K : Type u) (_ : Field K) (g : Spec (.of K) ⟶ T),
      P (Spec (.of K)) g :=
  exists_field_point P hThickening
    (fun D _ _ _ c hc _ _ f fi hfi hcf hPi =>
      limit_property_of_isCofiltered P hLimit D c hc f fi hfi hcf hPi)
    hClosedOrOpen hP

end AlgebraicGeometry
