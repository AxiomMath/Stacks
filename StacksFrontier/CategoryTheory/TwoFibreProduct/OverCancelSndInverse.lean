module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverCancelSnd

/-!
# The inverse of the cancellation comparison of Stacks 02XD over a base

`CategoryTheory.TwoFibreProductOver.cancelSnd` is the comparison
`(𝒵 ×_𝒴 𝒳) ×_𝒳 𝒰 ⥤ 𝒵 ×_𝒴 𝒰` of Stacks 02XD over a base category `𝒞`, and
`CategoryTheory.TwoFibreProductOver.isEquivalence_cancelSnd` says it is an equivalence. That
statement is proved by fullness, faithfulness and essential surjectivity, so the quasi-inverse it
provides is a choice and nothing is known about it. This file writes the quasi-inverse down: it
inserts the middle factor as `c u` with the identity comparison, exactly as the witness of
essential surjectivity does, and it is *strictly* compatible with all three structural functors
in sight — the structure functor to `𝒞`, the projection to `𝒵` and the projection to `𝒰`.

Those three strict compatibilities are what a 2-categorical consumer needs. A cancellation known
only as an equivalence of the two structure functors identifies the two apexes and says nothing
about the two projections, so it cannot be used to recognise one apex as a 2-fibre product of the
other's cospan; with the compatibilities below the comparison and its inverse are pre-morphisms
of 2-commutative squares whose comparison 2-cells are identities, and the unit of the equivalence
is an identity along both projections.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.cancelSndInv`: the quasi-inverse, inserting the middle
  factor with the identity comparison.
* `CategoryTheory.TwoFibreProductOver.cancelSndUnitIso`: the isomorphism
  `cancelSnd ⋙ cancelSndInv ≅ 𝟭`.

## Main results

* `CategoryTheory.TwoFibreProductOver.cancelSndInv_comp_structureFunctor`,
  `CategoryTheory.TwoFibreProductOver.cancelSndInv_comp_fst_comp_fst` and
  `CategoryTheory.TwoFibreProductOver.cancelSndInv_comp_snd`: the inverse is strictly over `𝒞`
  and strictly compatible with the two projections.
* `CategoryTheory.TwoFibreProductOver.cancelSnd_comp_snd`: the missing companion of
  `CategoryTheory.TwoFibreProductOver.cancelSnd_comp_fst`, for the projection to `𝒰`.
* `CategoryTheory.TwoFibreProductOver.cancelSndUnitIso_hom_app_a_a` and
  `CategoryTheory.TwoFibreProductOver.cancelSndUnitIso_hom_app_b`: the components of the unit
  along the two projections are identities, which is why whiskering the unit by either projection
  is an identity 2-cell.

## Implementation notes

The object part of the inverse is the witness already written in
`CategoryTheory.TwoFibreProductOver.essSurj_cancelSnd`; it is repeated here as a functor because
an essential-surjectivity witness is not a functor and the consumer needs one. The verticality
proofs are the same `IsHomLift` compositions.

The component of the unit is a separate definition rather than a `have` inside the construction
of the natural isomorphism, so that the two statements about its components hold by `rfl`: a
`have` forgets its body and the components are then unreachable.

`attribute [local implicit_reducible]` on the projections and on the comparison is required for
the same reason as in `CategoryTheory.TwoFibreProductOver.full_cancelSnd`: objects of the
iterated product have their comparison isomorphism typed through `(snd …).obj`, and Lean checks
implicit arguments at a transparency that does not unfold a plain `def`.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 02XD](https://stacks.math.columbia.edu/tag/02XD)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.TwoFibreProductOver

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

attribute [local implicit_reducible] fst snd structureFunctor cancelSndObj cancelSnd

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒵 : Type u₂} [Category.{v₂} 𝒵]
  {𝒳 : Type u₃} [Category.{v₃} 𝒳] {𝒴 : Type u₄} [Category.{v₄} 𝒴]
  {𝒰 : Type u₅} [Category.{v₅} 𝒰]
  (p𝒵 : 𝒵 ⥤ 𝒞) (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒰 : 𝒰 ⥤ 𝒞)
  (g : 𝒵 ⥤ 𝒴) (f : 𝒳 ⥤ 𝒴) (c : 𝒰 ⥤ 𝒳) (G : 𝒰 ⥤ 𝒴)
  (hf : f ⋙ p𝒴 = p𝒳) (hc : c ⋙ p𝒳 = p𝒰)
  (θ : c ⋙ f ≅ G) (hθ : ∀ u : 𝒰, p𝒴.IsHomLift (𝟙 (p𝒰.obj u)) (θ.hom.app u))

/-- **The comparison of Stacks 02XD commutes with the projections to `𝒰`** on the nose: the
`𝒰`-entry of an object of the iterated product is unchanged. This is the companion of
`CategoryTheory.TwoFibreProductOver.cancelSnd_comp_fst`, and the two together say that the
comparison is a pre-morphism of 2-commutative squares with identity comparison 2-cells. -/
lemma cancelSnd_comp_snd :
    cancelSnd p𝒵 p𝒳 p𝒴 p𝒰 g f c G hf θ hθ ⋙ snd p𝒵 p𝒰 p𝒴 g G =
      snd (structureFunctor p𝒵 p𝒳 p𝒴 g f) p𝒰 p𝒳 (snd p𝒵 p𝒳 p𝒴 g f) c := rfl

/-- **The quasi-inverse of the comparison of Stacks 02XD on objects.** An object `(U, z, u, χ)`
of `𝒵 ×_𝒴 𝒰` becomes the object `((U, z, c u, θ_u⁻¹ ∘ χ), u, 𝟙)` of `(𝒵 ×_𝒴 𝒳) ×_𝒳 𝒰`: the
middle factor is inserted as `c u`, with the identity as the outer comparison. -/
def cancelSndInvObj (Q : TwoFibreProductOver p𝒵 p𝒰 p𝒴 g G) :
    TwoFibreProductOver (structureFunctor p𝒵 p𝒳 p𝒴 g f) p𝒰 p𝒳
      (snd p𝒵 p𝒳 p𝒴 g f) c where
  base := Q.base
  x :=
    { base := Q.base
      x := Q.x
      y := c.obj Q.y
      hx := Q.hx
      hy := (Functor.congr_obj hc Q.y).trans Q.hy
      iso := Q.iso ≪≫ (θ.app Q.y).symm
      vertical := by
        have hθQ : p𝒴.IsHomLift (𝟙 Q.base) (θ.hom.app Q.y) := by
          have h := hθ Q.y
          rwa [Q.hy] at h
        have hθQinv : p𝒴.IsHomLift (𝟙 Q.base) (θ.app Q.y).inv :=
          @IsHomLift.lift_id_inv _ _ _ _ p𝒴 Q.base _ _ (θ.app Q.y) hθQ
        exact @IsHomLift.comp_of_lift_id _ _ _ _ p𝒴 Q.base _ _ _ Q.iso.hom
          (θ.app Q.y).inv Q.vertical hθQinv }
  y := Q.y
  hx := rfl
  hy := Q.hy
  iso := Iso.refl (c.obj Q.y)
  vertical := IsHomLift.id ((Functor.congr_obj hc Q.y).trans Q.hy)

/-- **The quasi-inverse of the comparison of Stacks 02XD on morphisms.** The `𝒵`-component and
the `𝒰`-component are kept, the middle component being the image `c b` of the latter. -/
def cancelSndInvMap {Q Q' : TwoFibreProductOver p𝒵 p𝒰 p𝒴 g G} (n : Q ⟶ Q') :
    cancelSndInvObj p𝒵 p𝒳 p𝒴 p𝒰 g f c G hc θ hθ Q ⟶
      cancelSndInvObj p𝒵 p𝒳 p𝒴 p𝒰 g f c G hc θ hθ Q' where
  hbase := n.hbase
  a :=
    { hbase := n.hbase
      a := n.a
      b := c.map n.b
      ha := n.ha
      hb := by
        have := n.hb
        exact Functor.isHomLift_map_of_comp_eq hc n.hbase n.b
      w := by
        have hw : g.map n.a ≫ Q'.iso.hom = Q.iso.hom ≫ G.map n.b := n.w
        have hnat : f.map (c.map n.b) ≫ (θ.app Q'.y).hom
            = (θ.app Q.y).hom ≫ G.map n.b := θ.hom.naturality n.b
        have hnat' : (θ.app Q.y).inv ≫ f.map (c.map n.b)
            = G.map n.b ≫ (θ.app Q'.y).inv := by
          rw [Iso.inv_comp_eq, ← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id,
            Category.comp_id]
        change g.map n.a ≫ Q'.iso.hom ≫ (θ.app Q'.y).inv
            = (Q.iso.hom ≫ (θ.app Q.y).inv) ≫ f.map (c.map n.b)
        rw [← Category.assoc, hw, Category.assoc, ← hnat', Category.assoc] }
  b := n.b
  ha := by
    refine structureFunctor_isHomLift _ n.hbase ?_
    exact n.ha
  hb := n.hb
  w := by
    change c.map n.b ≫ 𝟙 (c.obj Q'.y) = 𝟙 (c.obj Q.y) ≫ c.map n.b
    rw [Category.comp_id, Category.id_comp]

/-- **The quasi-inverse of the comparison functor of Stacks 02XD over a base**, built from
`CategoryTheory.TwoFibreProductOver.cancelSndInvObj` and
`CategoryTheory.TwoFibreProductOver.cancelSndInvMap`. -/
def cancelSndInv :
    TwoFibreProductOver p𝒵 p𝒰 p𝒴 g G ⥤
      TwoFibreProductOver (structureFunctor p𝒵 p𝒳 p𝒴 g f) p𝒰 p𝒳
        (snd p𝒵 p𝒳 p𝒴 g f) c where
  obj Q := cancelSndInvObj p𝒵 p𝒳 p𝒴 p𝒰 g f c G hc θ hθ Q
  map n := cancelSndInvMap p𝒵 p𝒳 p𝒴 p𝒰 g f c G hc θ hθ n
  map_id Q := Hom.ext' (Hom.ext' rfl (c.map_id Q.y)) rfl
  map_comp m n := Hom.ext' (Hom.ext' rfl (c.map_comp m.b n.b)) rfl

/-- **The quasi-inverse is strictly over `𝒞`.** -/
lemma cancelSndInv_comp_structureFunctor :
    cancelSndInv p𝒵 p𝒳 p𝒴 p𝒰 g f c G hc θ hθ ⋙
        structureFunctor (structureFunctor p𝒵 p𝒳 p𝒴 g f) p𝒰 p𝒳 (snd p𝒵 p𝒳 p𝒴 g f) c =
      structureFunctor p𝒵 p𝒰 p𝒴 g G := rfl

/-- **The quasi-inverse commutes with the projections to `𝒵`** on the nose. -/
lemma cancelSndInv_comp_fst_comp_fst :
    cancelSndInv p𝒵 p𝒳 p𝒴 p𝒰 g f c G hc θ hθ ⋙
        (fst (structureFunctor p𝒵 p𝒳 p𝒴 g f) p𝒰 p𝒳 (snd p𝒵 p𝒳 p𝒴 g f) c ⋙
          fst p𝒵 p𝒳 p𝒴 g f) =
      fst p𝒵 p𝒰 p𝒴 g G := rfl

/-- **The quasi-inverse commutes with the projections to `𝒰`** on the nose. -/
lemma cancelSndInv_comp_snd :
    cancelSndInv p𝒵 p𝒳 p𝒴 p𝒰 g f c G hc θ hθ ⋙
        snd (structureFunctor p𝒵 p𝒳 p𝒴 g f) p𝒰 p𝒳 (snd p𝒵 p𝒳 p𝒴 g f) c =
      snd p𝒵 p𝒰 p𝒴 g G := rfl

/-- **The middle component of the unit of the cancellation equivalence.** After cancelling and
reinserting the middle factor, the inner `𝒵 ×_𝒴 𝒳`-entry of `((U, z, x, ψ), u, φ)` has become
`(U, z, c u, θ_u⁻¹ ∘ θ_u ∘ f(φ) ∘ ψ)`, and `φ` identifies it with the original `(U, z, x, ψ)`. -/
noncomputable def cancelSndUnitIsoAppInner
    (P : TwoFibreProductOver (structureFunctor p𝒵 p𝒳 p𝒴 g f) p𝒰 p𝒳
      (snd p𝒵 p𝒳 p𝒴 g f) c) :
    (cancelSndInvObj p𝒵 p𝒳 p𝒴 p𝒰 g f c G hc θ hθ
      (cancelSndObj p𝒵 p𝒳 p𝒴 p𝒰 g f c G hf θ hθ P)).x ≅ P.x :=
  isoMkVertical (U := P.base) (Iso.refl P.x.x) P.iso.symm
    (by
      have h : p𝒵.obj P.x.x = P.base := P.x.hx.trans (show P.x.base = P.base from P.hx)
      exact IsHomLift.id h)
    (@IsHomLift.lift_id_inv _ _ _ _ p𝒳 P.base _ _ P.iso P.vertical)
    (by
      change g.map (𝟙 P.x.x) ≫ P.x.iso.hom
          = ((P.x.iso.hom ≫ f.map P.iso.hom ≫ (θ.app P.y).hom) ≫ (θ.app P.y).inv)
            ≫ f.map P.iso.inv
      simp)

/-- **The unit of the cancellation equivalence of Stacks 02XD, at an object.** Its `𝒵`-component
and its `𝒰`-component are identities; all the content is in the middle factor. -/
noncomputable def cancelSndUnitIsoApp
    (P : TwoFibreProductOver (structureFunctor p𝒵 p𝒳 p𝒴 g f) p𝒰 p𝒳
      (snd p𝒵 p𝒳 p𝒴 g f) c) :
    cancelSndInvObj p𝒵 p𝒳 p𝒴 p𝒰 g f c G hc θ hθ
        (cancelSndObj p𝒵 p𝒳 p𝒴 p𝒰 g f c G hf θ hθ P) ≅ P :=
  isoMkVertical (U := P.base)
    (cancelSndUnitIsoAppInner p𝒵 p𝒳 p𝒴 p𝒰 g f c G hf hc θ hθ P) (Iso.refl P.y)
    (structureFunctor_isHomLift _ (𝟙 P.base) (by
      have h : p𝒵.obj P.x.x = P.base := P.x.hx.trans (show P.x.base = P.base from P.hx)
      exact IsHomLift.id h))
    (IsHomLift.id (show p𝒰.obj P.y = P.base from P.hy))
    (by
      change (cancelSndUnitIsoAppInner p𝒵 p𝒳 p𝒴 p𝒰 g f c G hf hc θ hθ P).hom.b ≫ P.iso.hom
          = 𝟙 (c.obj P.y) ≫ c.map (𝟙 P.y)
      change P.iso.inv ≫ P.iso.hom = 𝟙 (c.obj P.y) ≫ c.map (𝟙 P.y)
      simp)

/-- **The unit of the cancellation equivalence of Stacks 02XD.** Cancelling the middle factor of
the iterated 2-fibre product and then reinserting it is the identity. -/
noncomputable def cancelSndUnitIso :
    cancelSnd p𝒵 p𝒳 p𝒴 p𝒰 g f c G hf θ hθ ⋙ cancelSndInv p𝒵 p𝒳 p𝒴 p𝒰 g f c G hc θ hθ ≅
      𝟭 (TwoFibreProductOver (structureFunctor p𝒵 p𝒳 p𝒴 g f) p𝒰 p𝒳
        (snd p𝒵 p𝒳 p𝒴 g f) c) :=
  NatIso.ofComponents
    (fun P => cancelSndUnitIsoApp p𝒵 p𝒳 p𝒴 p𝒰 g f c G hf hc θ hθ P)
    (fun {P P'} m => by
      refine Hom.ext' (Hom.ext' ?_ ?_) ?_
      · change m.a.a ≫ 𝟙 P'.x.x = 𝟙 P.x.x ≫ m.a.a
        rw [Category.comp_id, Category.id_comp]
      · have hw : m.a.b ≫ P'.iso.hom = P.iso.hom ≫ c.map m.b := m.w
        change c.map m.b ≫ P'.iso.inv = P.iso.inv ≫ m.a.b
        rw [Iso.comp_inv_eq, Category.assoc, hw, Iso.inv_hom_id_assoc]
      · change m.b ≫ 𝟙 P'.y = 𝟙 P.y ≫ m.b
        rw [Category.comp_id, Category.id_comp])

/-- **Reinserting the middle factor and then cancelling it again returns the same object.** The
comparison isomorphism of the result is literally the original one, the two copies of `θ` at the
`𝒰`-entry cancelling against each other. This is the counit of the cancellation equivalence, in
the form in which a consumer comparing the two fillers needs it. -/
lemma cancelSndObj_cancelSndInvObj_iso_hom (Q : TwoFibreProductOver p𝒵 p𝒰 p𝒴 g G) :
    (cancelSndObj p𝒵 p𝒳 p𝒴 p𝒰 g f c G hf θ hθ
      (cancelSndInvObj p𝒵 p𝒳 p𝒴 p𝒰 g f c G hc θ hθ Q)).iso.hom = Q.iso.hom := by
  show (Q.iso.hom ≫ (θ.app Q.y).inv) ≫ f.map (𝟙 (c.obj Q.y)) ≫ (θ.app Q.y).hom
      = Q.iso.hom
  simp

/-- The verticality of the components of the unit, in the form the 2-category of categories
fibred in groupoids asks for: each component lies over an identity of the base. -/
lemma cancelSndUnitIso_hom_app_isHomLift
    (P : TwoFibreProductOver (structureFunctor p𝒵 p𝒳 p𝒴 g f) p𝒰 p𝒳
      (snd p𝒵 p𝒳 p𝒴 g f) c) :
    (structureFunctor (structureFunctor p𝒵 p𝒳 p𝒴 g f) p𝒰 p𝒳 (snd p𝒵 p𝒳 p𝒴 g f) c).IsHomLift
      (𝟙 ((structureFunctor (structureFunctor p𝒵 p𝒳 p𝒴 g f) p𝒰 p𝒳
        (snd p𝒵 p𝒳 p𝒴 g f) c).obj P))
      ((cancelSndUnitIso p𝒵 p𝒳 p𝒴 p𝒰 g f c G hf hc θ hθ).hom.app P) := by
  have h𝒵 : p𝒵.obj P.x.x = P.base := P.x.hx.trans (show P.x.base = P.base from P.hx)
  refine structureFunctor_isHomLift _ (𝟙 P.base) ?_
  refine structureFunctor_isHomLift _ (𝟙 P.base) ?_
  show p𝒵.IsHomLift (𝟙 P.base) (𝟙 P.x.x)
  exact IsHomLift.id h𝒵

/-- The component of the unit along the projection to `𝒵` is an identity. -/
@[simp] lemma cancelSndUnitIso_hom_app_a_a
    (P : TwoFibreProductOver (structureFunctor p𝒵 p𝒳 p𝒴 g f) p𝒰 p𝒳
      (snd p𝒵 p𝒳 p𝒴 g f) c) :
    ((cancelSndUnitIso p𝒵 p𝒳 p𝒴 p𝒰 g f c G hf hc θ hθ).hom.app P).a.a = 𝟙 P.x.x := rfl

/-- The component of the unit along the projection to `𝒰` is an identity. -/
@[simp] lemma cancelSndUnitIso_hom_app_b
    (P : TwoFibreProductOver (structureFunctor p𝒵 p𝒳 p𝒴 g f) p𝒰 p𝒳
      (snd p𝒵 p𝒳 p𝒴 g f) c) :
    ((cancelSndUnitIso p𝒵 p𝒳 p𝒴 p𝒰 g f c G hf hc θ hθ).hom.app P).b = 𝟙 P.y := rfl

end CategoryTheory.TwoFibreProductOver

end
