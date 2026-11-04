module

public import StacksFrontier.CategoryTheory.Functor.Derived.DefinedAt

/-!
# A functor inverting a class of morphisms is derivable

Let `F : 𝒟 ⥤ 𝒟'` be a functor and let `W` be a class of morphisms of `𝒟` containing the
identities. If `F` inverts `W` then the right derived functor `RF` of Stacks 05S9 is defined at
every object, with value `RF(X) = F(X)`, so `F` is right derivable in the sense of
Stacks 05SV — and dually for `LF`. This is the degenerate case of the theory, and it is the one
that occurs whenever the functor to be derived already factors through the localization: no
resolutions are needed, and the derived functor is the factorisation itself.

The argument uses nothing about `W` beyond that it contains the identities. For an object `X`,
the ind-object of Stacks 05S9
$$ X/W ⟶ 𝒟', \quad (s : X ⟶ X') ⟼ F(X') $$
carries the cocone with vertex `F(X)` whose coprojection at `s` is the *inverse* of `F(s)`;
naturality is exactly the triangle `s ≫ u = t` defining a morphism of `X/W`, and in particular
the morphisms of `X/W` are not themselves required to lie in `W`. That cocone is essentially
constant with index `𝟙 X` — this is where `W.ContainsIdentities` is used, and without a
nonempty index category the statement is false, as `W = ⊥` on a nonempty `𝒟` shows — and
retraction the identity.

## Main definitions

* `CategoryTheory.Functor.valueCoconeOfInverts` is the cocone on the ind-object with vertex
  `F(X)`, and `CategoryTheory.Functor.valueConeOfInverts` is the cone on the pro-object with
  vertex `F(X)`.

## Main results

* `CategoryTheory.Functor.isRightDerivedValueAt_valueCoconeOfInverts` and
  `CategoryTheory.Functor.isLeftDerivedValueAt_valueConeOfInverts`: those two are values of `RF`,
  resp. `LF`, at `X` in the sense of Stacks 05S9.
* `CategoryTheory.Functor.IsRightDerivedValueAt.isoObjOfInverts` and
  `CategoryTheory.Functor.IsLeftDerivedValueAt.isoObjOfInverts`: *every* value of `RF`, resp.
  `LF`, at `X` is then isomorphic to `F(X)`.
* `CategoryTheory.Functor.IsRightDerivedValueAt.isIso_ι_app`: *every* coprojection of such a
  value of `RF` is invertible, being the inverse of `F(s)` through that isomorphism. At the index
  `𝟙 X` this is the canonical map `F(X) ⟶ RF(X)`, so `X` computes `RF` in the sense of
  Stacks 05SX.
* `CategoryTheory.Functor.exists_isRightDerivedValueAt_of_isInvertedBy` and its dual
  `CategoryTheory.Functor.exists_isLeftDerivedValueAt_of_isInvertedBy`: a factorisation
  `F ≅ L ⋙ G` produces, at every object, the derived-functor data of Stacks 0FTR — the value,
  the identification of its vertex with `G(L(X))` and the statement that the comparison map is
  the coprojection, resp. the projection, of the value.
* `CategoryTheory.Functor.isRightDerivable_of_isInvertedBy`: a functor inverting `W` is right
  derivable with respect to `W`, i.e. `RF` is everywhere defined in the sense of Stacks 05SV.
* `CategoryTheory.Functor.isLeftDerivable_of_isInvertedBy`: the dual statement for `LF`.

## Implementation notes

*Relation to Mathlib.* Mathlib's `Functor.hasPointwiseRightDerivedFunctor_of_inverts` draws the
corresponding conclusion for Mathlib's condition `Functor.HasPointwiseRightDerivedFunctor`,
which asks for a pointwise left Kan extension along a localization functor. That is a different
condition from the essential constancy of Stacks 05S9 — the latter in addition makes the value a
retract of a term of the diagram — and no bridge between the two is claimed, here or in
`StacksFrontier.CategoryTheory.Functor.Derived.DefinedAt`; each is proved from the hypothesis
separately. The companion fact that the factorisation `CategoryTheory.Localization.lift F hF L`
is a left Kan extension of `F` along `L`, with unit `(CategoryTheory.Localization.fac F hF L).inv`,
is already Mathlib's `Functor.isRightDerivedFunctor_of_inverts` read through
`Functor.isRightDerivedFunctor_iff_isLeftKanExtension`.

*The cocone and the cone are named.* A consumer which has to exhibit the value together with
its coprojections — as the derived-value hypotheses of Stacks 0FTR do, since they ask that the
prescribed comparison map *be* the coprojection — needs the cocone itself and not merely its
existence, so `valueCoconeOfInverts` and `valueConeOfInverts` are definitions and the two
derivability statements are read off them.

## References

* [Stacks Project, Tag 05SV](https://stacks.math.columbia.edu/tag/05SV), the definition of a
  right, resp. left, derivable functor; being defined at an object is
  [Tag 05S9](https://stacks.math.columbia.edu/tag/05S9).
-/

@[expose] public section

namespace CategoryTheory.Functor

open Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {D : Type u₁} [Category.{v₁} D] {D' : Type u₂} [Category.{v₂} D']

/-- The cocone with vertex `F.obj X` on the ind-object
`X/W ⟶ 𝒟'`, `(s : X ⟶ X') ↦ F(X')`
of Stacks 05S9, available whenever `F` inverts `W`: the coprojection at `s` is the inverse of
`F.map s`, and naturality is the triangle `s ≫ u = t` defining a morphism of `X/W`. -/
noncomputable def valueCoconeOfInverts (F : D ⥤ D') (W : MorphismProperty D)
    (hW : W.IsInvertedBy F) (X : D) :
    Cocone (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F) where
  pt := F.obj X
  ι :=
    { app s := (@asIso _ _ _ _ (F.map s.hom) (hW s.hom s.prop)).inv
      naturality := by
        intro s t u
        have h₁ := hW s.hom s.prop
        have h₂ := hW t.hom t.prop
        dsimp
        rw [Category.comp_id, IsIso.comp_inv_eq, IsIso.eq_inv_comp, ← F.map_comp,
          MorphismProperty.Under.w u] }

/-- The vertex of `valueCoconeOfInverts F W hW X` is `F.obj X`. -/
@[simp]
lemma valueCoconeOfInverts_pt (F : D ⥤ D') (W : MorphismProperty D)
    (hW : W.IsInvertedBy F) (X : D) : (valueCoconeOfInverts F W hW X).pt = F.obj X :=
  rfl

/-- The coprojection of `valueCoconeOfInverts` at `s : X ⟶ X'` composed with `F.map s` is the
identity: the coprojection is a section of `F.map s`. -/
@[reassoc (attr := simp)]
lemma valueCoconeOfInverts_ι_app_comp (F : D ⥤ D') (W : MorphismProperty D)
    (hW : W.IsInvertedBy F) (X : D) (s : W.Under ⊤ X) :
    (valueCoconeOfInverts F W hW X).ι.app s ≫ F.map s.hom = 𝟙 (F.obj s.right) := by
  have h := hW s.hom s.prop
  show (@asIso _ _ _ _ (F.map s.hom) h).inv ≫ F.map s.hom = _
  simp

/-- The cone with vertex `F.obj X` on the pro-object
`W/X ⟶ 𝒟'`, `(s : X' ⟶ X) ↦ F(X')`
of Stacks 05S9, available whenever `F` inverts `W`: the projection at `s` is the inverse of
`F.map s`, and naturality is the triangle `u ≫ t = s` defining a morphism of `W/X`. -/
noncomputable def valueConeOfInverts (F : D ⥤ D') (W : MorphismProperty D)
    (hW : W.IsInvertedBy F) (X : D) :
    Cone (MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ F) where
  pt := F.obj X
  π :=
    { app s := (@asIso _ _ _ _ (F.map s.hom) (hW s.hom s.prop)).inv
      naturality := by
        intro s t u
        have h₁ := hW s.hom s.prop
        have h₂ := hW t.hom t.prop
        dsimp
        rw [Category.id_comp, IsIso.eq_inv_comp, IsIso.comp_inv_eq, ← F.map_comp,
          MorphismProperty.Over.w u] }

/-- The vertex of `valueConeOfInverts F W hW X` is `F.obj X`. -/
@[simp]
lemma valueConeOfInverts_pt (F : D ⥤ D') (W : MorphismProperty D)
    (hW : W.IsInvertedBy F) (X : D) : (valueConeOfInverts F W hW X).pt = F.obj X :=
  rfl

/-- `F.map s` composed with the projection of `valueConeOfInverts` at `s : X' ⟶ X` is the
identity: the projection is a retraction of `F.map s`. -/
@[reassoc (attr := simp)]
lemma comp_valueConeOfInverts_π_app (F : D ⥤ D') (W : MorphismProperty D)
    (hW : W.IsInvertedBy F) (X : D) (s : W.Over ⊤ X) :
    F.map s.hom ≫ (valueConeOfInverts F W hW X).π.app s = 𝟙 (F.obj s.left) := by
  have h := hW s.hom s.prop
  show F.map s.hom ≫ (@asIso _ _ _ _ (F.map s.hom) h).inv = _
  simp

variable (F : D ⥤ D') (W : MorphismProperty D) [W.ContainsIdentities]

/-- A functor inverting `W` has a value of its right derived functor at every object, namely its
own value there: the ind-object of Stacks 05S9 is essentially constant with index `𝟙 X` and
retraction the identity. -/
theorem isRightDerivedValueAt_valueCoconeOfInverts (hW : W.IsInvertedBy F) (X : D) :
    F.IsRightDerivedValueAt W X (valueCoconeOfInverts F W hW X) := by
  refine ⟨MorphismProperty.Under.mk ⊤ (𝟙 X) (W.id_mem X), 𝟙 _, ?_, fun s => ?_⟩
  · have h := hW (𝟙 X) (W.id_mem X)
    show 𝟙 _ ≫ (@asIso _ _ _ _ (F.map (𝟙 X)) h).inv = 𝟙 _
    simp
  · refine ⟨s, 𝟙 s, MorphismProperty.Under.homMk s.hom (by simp), ?_⟩
    have h₁ := hW s.hom s.prop
    show F.map (𝟙 s.right) = (@asIso _ _ _ _ (F.map s.hom) h₁).inv ≫ 𝟙 _ ≫ F.map s.hom
    simp

/-- A functor inverting `W` has a value of its left derived functor at every object, namely its
own value there: the pro-object of Stacks 05S9 is essentially constant with index `𝟙 X` and
retraction the identity. -/
theorem isLeftDerivedValueAt_valueConeOfInverts (hW : W.IsInvertedBy F) (X : D) :
    F.IsLeftDerivedValueAt W X (valueConeOfInverts F W hW X) := by
  refine ⟨MorphismProperty.Over.mk ⊤ (𝟙 X) (W.id_mem X), 𝟙 _, ?_, fun s => ?_⟩
  · have h := hW (𝟙 X) (W.id_mem X)
    show (@asIso _ _ _ _ (F.map (𝟙 X)) h).inv ≫ 𝟙 _ = 𝟙 _
    simp
  · have h₁ := hW s.hom s.prop
    refine ⟨s, 𝟙 s, MorphismProperty.Over.homMk
      (B := MorphismProperty.Over.mk ⊤ (𝟙 X) (W.id_mem X)) s.hom (Category.comp_id _), ?_⟩
    show F.map (𝟙 s.left) = F.map s.hom ≫ 𝟙 _ ≫ (@asIso _ _ _ _ (F.map s.hom) h₁).inv
    simp

/-- A functor inverting `W` is right derivable with respect to `W`: the right derived functor
`RF` of Stacks 05S9 is defined at every object `X`, the value being `F(X)` itself. -/
theorem isRightDerivable_of_isInvertedBy (hW : W.IsInvertedBy F) : F.IsRightDerivable W :=
  fun X => ⟨_, isRightDerivedValueAt_valueCoconeOfInverts F W hW X⟩

/-- A functor inverting `W` is left derivable with respect to `W`: the left derived functor `LF`
of Stacks 05S9 is defined at every object `X`, the value being `F(X)` itself. -/
theorem isLeftDerivable_of_isInvertedBy (hW : W.IsInvertedBy F) : F.IsLeftDerivable W :=
  fun X => ⟨_, isLeftDerivedValueAt_valueConeOfInverts F W hW X⟩

variable {F W}

/-- A factorisation of `F` through a functor `L` — in practice the localization functor at `W` —
produces the derived-functor data of Stacks 0FTR at every object: a value of `RF` at `X`, an
isomorphism of its vertex with `G(L(X))`, and the statement that the given comparison map
`β : F ⟶ L ⋙ G` is the coprojection of the value. Only the isomorphism `F ≅ L ⋙ G` is used; `L`
is not required to be a localization functor. -/
theorem exists_isRightDerivedValueAt_of_isInvertedBy {E : Type u₃} [Category.{v₃} E]
    (hW : W.IsInvertedBy F) (L : D ⥤ E) (G : E ⥤ D') (β : F ≅ L ⋙ G) (X : D) :
    ∃ (c : Cocone (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F))
      (_ : F.IsRightDerivedValueAt W X c) (ε : c.pt ≅ G.obj (L.obj X)),
      ∀ s : W.Under ⊤ X, c.ι.app s ≫ ε.hom ≫ G.map (L.map s.hom) = β.hom.app s.right := by
  refine ⟨_, isRightDerivedValueAt_valueCoconeOfInverts F W hW X, β.app X, fun s => ?_⟩
  have key : β.hom.app X ≫ G.map (L.map s.hom) = F.map s.hom ≫ β.hom.app s.right :=
    (β.hom.naturality s.hom).symm
  rw [Iso.app_hom]
  erw [key]
  erw [← Category.assoc, valueCoconeOfInverts_ι_app_comp, Category.id_comp]

/-- The dual of `exists_isRightDerivedValueAt_of_isInvertedBy`: a factorisation of `F` through a
functor `L` produces a value of `LF` at every object, an isomorphism of `G(L(X))` with its
vertex, and the statement that the given comparison map `α : L ⋙ G ⟶ F` is its projection. -/
theorem exists_isLeftDerivedValueAt_of_isInvertedBy {E : Type u₃} [Category.{v₃} E]
    (hW : W.IsInvertedBy F) (L : D ⥤ E) (G : E ⥤ D') (α : L ⋙ G ≅ F) (X : D) :
    ∃ (c : Cone (MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ F))
      (_ : F.IsLeftDerivedValueAt W X c) (ε : G.obj (L.obj X) ≅ c.pt),
      ∀ s : W.Over ⊤ X, G.map (L.map s.hom) ≫ ε.hom ≫ c.π.app s = α.hom.app s.left := by
  refine ⟨_, isLeftDerivedValueAt_valueConeOfInverts F W hW X, α.app X, fun s => ?_⟩
  have key : G.map (L.map s.hom) ≫ α.hom.app X = α.hom.app s.left ≫ F.map s.hom :=
    α.hom.naturality s.hom
  rw [Iso.app_hom]
  erw [← Category.assoc, key]
  erw [Category.assoc, comp_valueConeOfInverts_π_app, Category.comp_id]

/-- If `F` inverts `W`, then every value of the right derived functor of `F` at `X` is isomorphic
to `F.obj X`: both are colimits of the ind-object of Stacks 05S9. -/
noncomputable def IsRightDerivedValueAt.isoObjOfInverts (hW : W.IsInvertedBy F) {X : D}
    {c : Cocone (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F)}
    (hc : F.IsRightDerivedValueAt W X c) : c.pt ≅ F.obj X :=
  IsColimit.coconePointUniqueUpToIso hc.isColimit
    (isRightDerivedValueAt_valueCoconeOfInverts F W hW X).isColimit

/-- If `F` inverts `W`, then every coprojection of a value of `RF` at `X` is an isomorphism:
through the identification of the value with `F(X)` it is the inverse of `F(s)`. -/
theorem IsRightDerivedValueAt.isIso_ι_app (hW : W.IsInvertedBy F) {X : D}
    {c : Cocone (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F)}
    (hc : F.IsRightDerivedValueAt W X c) (s : W.Under ⊤ X) : IsIso (c.ι.app s) := by
  have := hW s.hom s.prop
  have hv : IsIso ((valueCoconeOfInverts F W hW X).ι.app s) :=
    inferInstanceAs (IsIso (@asIso _ _ _ _ (F.map s.hom) _).inv)
  have key : c.ι.app s ≫ (hc.isoObjOfInverts hW).hom =
      (valueCoconeOfInverts F W hW X).ι.app s :=
    IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _
  have h : c.ι.app s =
      (valueCoconeOfInverts F W hW X).ι.app s ≫ (hc.isoObjOfInverts hW).inv :=
    (Iso.eq_comp_inv _).mpr key
  rw [h]
  exact IsIso.comp_isIso' hv (Iso.isIso_inv (hc.isoObjOfInverts hW))

/-- If `F` inverts `W`, then every value of the left derived functor of `F` at `X` is isomorphic
to `F.obj X`: both are limits of the pro-object of Stacks 05S9. -/
noncomputable def IsLeftDerivedValueAt.isoObjOfInverts (hW : W.IsInvertedBy F) {X : D}
    {c : Cone (MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ F)}
    (hc : F.IsLeftDerivedValueAt W X c) : c.pt ≅ F.obj X :=
  IsLimit.conePointUniqueUpToIso hc.isLimit
    (isLeftDerivedValueAt_valueConeOfInverts F W hW X).isLimit

end CategoryTheory.Functor

end
