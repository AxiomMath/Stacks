module

public import StacksFrontier.CategoryTheory.Monoidal.Reseat

/-!
# The constraints of a re-seated monoidal structure

`CategoryTheory.MonoidalCategory.reseat` transports a monoidal structure on `C` onto a
prescribed tensor bifunctor `T` and a prescribed unit `U`.  Its tensor product and its unit
are then `T` and `U` on the nose, but its *constraints* are the given ones conjugated by the
component isomorphism `CategoryTheory.MonoidalCategory.reseatIso`.  This file writes that
conjugation out, so that a coherence equation for the given structure can be transported to
the re-seated one.

The associator and the two unitors are conjugated visibly, being written out in
`CategoryTheory.MonoidalCategory.reseatStruct`; `reseat_associator_whisker`, `reseat_rightUnitor`
and `reseat_leftUnitor` only convert the `CategoryTheory.MonoidalCategory.tensorIso` factors to
whiskerings.  In particular the left unitor needs no braiding: it is not obtained from the right
one through `CategoryTheory.braiding_rightUnitor`, and `reseat_leftUnitor` assumes no
`CategoryTheory.BraidedCategory`.  The braiding is not written out:
`CategoryTheory.MonoidalCategory.reseatBraided` is `CategoryTheory.BraidedCategory.ofFullyFaithful`
at the identity functor, so its braiding is a `CategoryTheory.Functor.preimage`, and
`reseat_braiding` computes it.  That the preimage along `𝟭 C` of a morphism is the morphism is
`CategoryTheory.Functor.map_preimage` together with `(𝟭 C).map f = f`, which is `rfl`.

## Main results

* `CategoryTheory.MonoidalCategory.reseat_associator_whisker`: the associator of the re-seated
  structure is the given associator conjugated by `reseatIso`.
* `CategoryTheory.MonoidalCategory.reseat_rightUnitor`,
  `CategoryTheory.MonoidalCategory.reseat_leftUnitor` and `reseat_rightUnitor_inv`: the unitors of
  the re-seated structure are the given unitors conjugated by `reseatIso` and the unit
  comparison `ε`.
* `CategoryTheory.MonoidalCategory.reseat_leftUnitor_via_braiding`: the re-seated left unitor
  in terms of the given *right* unitor, over a braided structure.
* `CategoryTheory.MonoidalCategory.reseat_braiding`,
  `CategoryTheory.MonoidalCategory.reseatSymmetric_braiding`: likewise for the braiding of
  `reseatBraided` and of `reseatSymmetric`.
* `CategoryTheory.MonoidalCategory.reseat_associator_comp`,
  `CategoryTheory.MonoidalCategory.reseat_braiding_comp`,
  `CategoryTheory.MonoidalCategory.reseat_rightUnitor_comp`,
  `CategoryTheory.MonoidalCategory.reseat_leftUnitor_comp`, and their `_of_eq` and
  `_of_unitality` variants: a coherence equation for a family of
  comparison morphisms out of the given tensor product, transported to the re-seated
  structure.  These are the form in which the two lemmas above are consumed: a comparison
  `X ⊗ Y ⟶ P` for the given structure becomes `(T.obj X).obj Y ⟶ P` for the re-seated one by
  composing with `(reseatIso e X Y).inv`, and the transported equation is the given one with
  one isomorphism cancelled off the front.

## Implementation notes

`C` carries two monoidal structures throughout, so, as in
`StacksFrontier/CategoryTheory/Monoidal/Reseat.lean`, no declaration here leaves either to
instance synthesis: the re-seated structure is always named by `@`-application, and the
notations `⊗`, `▷`, `◁`, `α_` and `β_` always mean the given one.
-/

@[expose] public section

universe v u

namespace CategoryTheory.MonoidalCategory

open Category

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {T : C ⥤ C ⥤ C} {U : C}

/-- **The associator of the re-seated structure is the given associator, conjugated by
`CategoryTheory.MonoidalCategory.reseatIso`.**  This is the associator field of
`CategoryTheory.MonoidalCategory.reseatStruct` with its two
`CategoryTheory.MonoidalCategory.tensorIso` factors read as whiskerings. -/
lemma reseat_associator_whisker (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U) (X Y Z : C) :
    (@MonoidalCategoryStruct.associator C _ (reseat e ε).toMonoidalCategoryStruct X Y Z).hom =
      (reseatIso e ((T.obj X).obj Y) Z).inv ≫ (reseatIso e X Y).inv ▷ Z ≫ (α_ X Y Z).hom ≫
        X ◁ (reseatIso e Y Z).hom ≫ (reseatIso e X ((T.obj Y).obj Z)).hom := by
  show (((reseatIso e ((T.obj X).obj Y) Z).symm ≪≫ ((reseatIso e X Y).symm ⊗ᵢ Iso.refl Z)) ≪≫
      α_ X Y Z ≪≫ ((Iso.refl X ⊗ᵢ reseatIso e Y Z) ≪≫
        reseatIso e X ((T.obj Y).obj Z))).hom = _
  simp

/-- **The right unitor of the re-seated structure is the given right unitor, conjugated by
`CategoryTheory.MonoidalCategory.reseatIso` and the unit comparison `ε`.**  This is the
`rightUnitor` field of `CategoryTheory.MonoidalCategory.reseatStruct` with its
`CategoryTheory.MonoidalCategory.tensorIso` factor read as a whiskering. -/
lemma reseat_rightUnitor (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U) (X : C) :
    (@MonoidalCategoryStruct.rightUnitor C _ (reseat e ε).toMonoidalCategoryStruct X).hom =
      (reseatIso e X U).inv ≫ X ◁ ε.inv ≫ (ρ_ X).hom := by
  show (((reseatIso e X U).symm ≪≫ (Iso.refl X ⊗ᵢ ε.symm)) ≪≫ ρ_ X).hom = _
  simp

/-- **The left unitor of the re-seated structure is the given left unitor, conjugated by
`CategoryTheory.MonoidalCategory.reseatIso` and the unit comparison `ε`.**  The companion of
`CategoryTheory.MonoidalCategory.reseat_rightUnitor`: like the associator and unlike the
braiding, both unitors are written out in
`CategoryTheory.MonoidalCategory.reseatStruct`, so neither needs a braiding to be computed. -/
lemma reseat_leftUnitor (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U) (X : C) :
    (@MonoidalCategoryStruct.leftUnitor C _ (reseat e ε).toMonoidalCategoryStruct X).hom =
      (reseatIso e U X).inv ≫ ε.inv ▷ X ≫ (λ_ X).hom := by
  show (((reseatIso e U X).symm ≪≫ (ε.symm ⊗ᵢ Iso.refl X)) ≪≫ λ_ X).hom = _
  simp

/-- `CategoryTheory.MonoidalCategory.reseat_rightUnitor` for the inverse. -/
lemma reseat_rightUnitor_inv (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U) (X : C) :
    (@MonoidalCategoryStruct.rightUnitor C _ (reseat e ε).toMonoidalCategoryStruct X).inv =
      (ρ_ X).inv ≫ X ◁ ε.hom ≫ (reseatIso e X U).hom := by
  show (((reseatIso e X U).symm ≪≫ (Iso.refl X ⊗ᵢ ε.symm)) ≪≫ ρ_ X).inv = _
  simp

/-- **The left unitor of the re-seated structure in terms of the given *right* unitor**, when
the given structure is braided.  This is the form a consumer wants when the only unit
comparison it has is a right-handed one, as happens for the derived tensor product, whose left
unit constraint is defined as its right one read through the commutativity constraint.

It is `CategoryTheory.MonoidalCategory.reseat_leftUnitor` combined with
`CategoryTheory.braiding_rightUnitor`, so the braiding here is that of the *given* structure and
no re-seated braiding is involved.  Note that
`CategoryTheory.MonoidalCategory.reseat_leftUnitor` itself needs none of this. -/
lemma reseat_leftUnitor_via_braiding [BraidedCategory C] (e : curriedTensor C ≅ T)
    (ε : 𝟙_ C ≅ U) (X : C) :
    (@MonoidalCategoryStruct.leftUnitor C _ (reseat e ε).toMonoidalCategoryStruct X).hom =
      (reseatIso e U X).inv ≫ (β_ U X).hom ≫ X ◁ ε.inv ≫ (ρ_ X).hom := by
  rw [reseat_leftUnitor e ε X, ← BraidedCategory.braiding_naturality_left_assoc ε.inv X,
    braiding_rightUnitor]

/-- **The braiding of `CategoryTheory.MonoidalCategory.reseatBraided` is the given braiding,
conjugated by `CategoryTheory.MonoidalCategory.reseatIso`.**  The braiding is produced as a
`CategoryTheory.Functor.preimage` along `𝟭 C`, which `CategoryTheory.Functor.map_preimage`
identifies with the morphism itself. -/
lemma reseat_braiding [BraidedCategory C] (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U) (X Y : C) :
    (@BraidedCategory.braiding C _ (reseat e ε) (reseatBraided e ε) X Y).hom =
      (reseatIso e X Y).inv ≫ (β_ X Y).hom ≫ (reseatIso e Y X).hom :=
  (𝟭 C).map_preimage _

/-- **`reseatIso` carries the given braiding to the re-seated one.**  This is `reseat_braiding`
with the source comparison moved to the other side, which is the form a caller uses: it has no
`reseatIso` inverse in it, so it composes with a computation of the given braiding without ever
crossing the comparison backwards. -/
lemma reseat_braiding_aux [BraidedCategory C] (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U)
    (X Y : C) :
    (reseatIso e X Y).hom ≫
        (@BraidedCategory.braiding C _ (reseat e ε) (reseatBraided e ε) X Y).hom =
      (β_ X Y).hom ≫ (reseatIso e Y X).hom :=
  (congrArg (fun f => (reseatIso e X Y).hom ≫ f) (reseat_braiding e ε X Y)).trans
    (Iso.hom_inv_id_assoc _ _)

/-- **The braiding of `CategoryTheory.MonoidalCategory.reseatSymmetric` is the given braiding,
conjugated by `CategoryTheory.MonoidalCategory.reseatIso`.**  Its braided structure is that of
`CategoryTheory.MonoidalCategory.reseatBraided`. -/
lemma reseatSymmetric_braiding [SymmetricCategory C] (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U)
    (X Y : C) :
    (@BraidedCategory.braiding C _ (reseat e ε) (reseatSymmetric e ε).toBraidedCategory X Y).hom =
      (reseatIso e X Y).inv ≫ (β_ X Y).hom ≫ (reseatIso e Y X).hom :=
  reseat_braiding e ε X Y

/-- **A hexagon-shaped coherence equation for a family of comparison morphisms transports to
the re-seated structure.**  Let `m`, `n`, `p`, `q` be morphisms out of the re-seated tensor
products, and let `a` be a morphism of the targets.  If the equation holds for the given
structure and the comparisons read through `reseatIso`, it holds for the re-seated structure
and the comparisons themselves.

Both sides acquire the same prefix `(reseatIso e _ Z).inv ≫ (reseatIso e X Y).inv ▷ Z`, which
is cancelled off. -/
lemma reseat_associator_comp (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U) {X Y Z XY YZ W W' : C}
    (m : (T.obj X).obj Y ⟶ XY) (n : (T.obj Y).obj Z ⟶ YZ) (p : (T.obj XY).obj Z ⟶ W)
    (q : (T.obj X).obj YZ ⟶ W') (a : W ⟶ W')
    (h : ((reseatIso e X Y).hom ≫ m) ▷ Z ≫ ((reseatIso e XY Z).hom ≫ p) ≫ a =
      (α_ X Y Z).hom ≫ X ◁ ((reseatIso e Y Z).hom ≫ n) ≫ ((reseatIso e X YZ).hom ≫ q)) :
    letI := reseat e ε
    m ▷ Z ≫ p ≫ a = (α_ X Y Z).hom ≫ X ◁ n ≫ q := by
  show (T.map m).app Z ≫ p ≫ a =
    (@MonoidalCategoryStruct.associator C _ (reseat e ε).toMonoidalCategoryStruct X Y Z).hom ≫
      (T.obj X).map n ≫ q
  rw [reseat_associator_whisker e ε X Y Z, reseat_whiskerRight e m Z, reseat_whiskerLeft e X n]
  simp only [comp_whiskerRight, whiskerLeft_comp, assoc, Iso.hom_inv_id_assoc] at h ⊢
  rw [← h]
  simp

/-- **A braiding-shaped coherence equation for a family of comparison morphisms transports to
the re-seated structure.**  The companion of
`CategoryTheory.MonoidalCategory.reseat_associator_comp`: here the common prefix is the single
isomorphism `(reseatIso e X Y).inv`. -/
lemma reseat_braiding_comp [BraidedCategory C] (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U)
    {X Y P P' : C} (c : (T.obj X).obj Y ⟶ P) (c' : (T.obj Y).obj X ⟶ P') (b : P ⟶ P')
    (h : (β_ X Y).hom ≫ (reseatIso e Y X).hom ≫ c' = ((reseatIso e X Y).hom ≫ c) ≫ b) :
    (@BraidedCategory.braiding C _ (reseat e ε) (reseatBraided e ε) X Y).hom ≫ c' = c ≫ b := by
  rw [reseat_braiding e ε X Y]
  simp only [assoc] at h ⊢
  rw [h, Iso.inv_hom_id_assoc]

/-- The same for `CategoryTheory.MonoidalCategory.reseatSymmetric`. -/
lemma reseatSymmetric_braiding_comp [SymmetricCategory C] (e : curriedTensor C ≅ T)
    (ε : 𝟙_ C ≅ U) {X Y P P' : C} (c : (T.obj X).obj Y ⟶ P) (c' : (T.obj Y).obj X ⟶ P')
    (b : P ⟶ P')
    (h : (β_ X Y).hom ≫ (reseatIso e Y X).hom ≫ c' = ((reseatIso e X Y).hom ≫ c) ≫ b) :
    (@BraidedCategory.braiding C _ (reseat e ε) (reseatSymmetric e ε).toBraidedCategory X Y).hom ≫
        c' = c ≫ b := by
  exact reseat_braiding_comp e ε c c' b h

/-- `CategoryTheory.MonoidalCategory.reseat_associator_comp` with the four comparisons read
through `reseatIso` supplied as separate equations rather than substituted into the hypothesis.

This is the form a consumer wants.  Substituting them means elaborating the long coherence
equation twice in one declaration — once as the statement, once inside the hypothesis — and on
a concrete monoidal category that is enough to exhaust the heartbeat budget.  Here each
equation is elaborated in its own declaration and this lemma is a single application. -/
lemma reseat_associator_comp_of_eq (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U)
    {X Y Z XY YZ W W' : C} {m : (T.obj X).obj Y ⟶ XY} {n : (T.obj Y).obj Z ⟶ YZ}
    {p : (T.obj XY).obj Z ⟶ W} {q : (T.obj X).obj YZ ⟶ W'} (a : W ⟶ W')
    {m' : X ⊗ Y ⟶ XY} {n' : Y ⊗ Z ⟶ YZ} {p' : XY ⊗ Z ⟶ W} {q' : X ⊗ YZ ⟶ W'}
    (hm : (reseatIso e X Y).hom ≫ m = m') (hn : (reseatIso e Y Z).hom ≫ n = n')
    (hp : (reseatIso e XY Z).hom ≫ p = p') (hq : (reseatIso e X YZ).hom ≫ q = q')
    (h : m' ▷ Z ≫ p' ≫ a = (α_ X Y Z).hom ≫ X ◁ n' ≫ q') :
    letI := reseat e ε
    m ▷ Z ≫ p ≫ a = (α_ X Y Z).hom ≫ X ◁ n ≫ q :=
  reseat_associator_comp e ε m n p q a (by rw [hm, hn, hp, hq]; exact h)

/-- `CategoryTheory.MonoidalCategory.reseatSymmetric_braiding_comp` with the two comparisons
read through `reseatIso` supplied as separate equations; the companion of
`CategoryTheory.MonoidalCategory.reseat_associator_comp_of_eq`. -/
lemma reseatSymmetric_braiding_comp_of_eq [SymmetricCategory C] (e : curriedTensor C ≅ T)
    (ε : 𝟙_ C ≅ U) {X Y P P' : C} {c : (T.obj X).obj Y ⟶ P} {c' : (T.obj Y).obj X ⟶ P'}
    (b : P ⟶ P') {d : X ⊗ Y ⟶ P} {d' : Y ⊗ X ⟶ P'}
    (hc : (reseatIso e X Y).hom ≫ c = d) (hc' : (reseatIso e Y X).hom ≫ c' = d')
    (h : (β_ X Y).hom ≫ d' = d ≫ b) :
    (@BraidedCategory.braiding C _ (reseat e ε) (reseatSymmetric e ε).toBraidedCategory X Y).hom ≫
        c' = c ≫ b :=
  reseatSymmetric_braiding_comp e ε c c' b (by rw [hc', hc]; exact h)

/-- **A right-unitor-shaped coherence equation for a comparison morphism transports to the
re-seated structure.**  The unitor companion of
`CategoryTheory.MonoidalCategory.reseat_associator_comp`: as for the braiding, the common
prefix is the single isomorphism `(reseatIso e X U).inv`, there being one comparison rather
than four.

Note which unit appears on each side.  The re-seated unit is `U`, so the comparison `c` starts
at `(T.obj X).obj U`; the given unit is `𝟙_ C`, so the hypothesis is stated at `X ⊗ U` and the
unit comparison enters as `ε.inv`.  That is the direction forced by
`CategoryTheory.MonoidalCategory.reseat_rightUnitor`. -/
lemma reseat_rightUnitor_comp (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U) {X P : C}
    (c : (T.obj X).obj U ⟶ P) (r : P ⟶ X)
    (h : (reseatIso e X U).hom ≫ c ≫ r = X ◁ ε.inv ≫ (ρ_ X).hom) :
    letI := reseat e ε
    (ρ_ X).hom = c ≫ r := by
  rw [reseat_rightUnitor e ε X, ← h, Iso.inv_hom_id_assoc]

/-- The mirror of `CategoryTheory.MonoidalCategory.reseat_rightUnitor_comp`.  Like
`CategoryTheory.MonoidalCategory.reseat_leftUnitor` it assumes no
`CategoryTheory.BraidedCategory`. -/
lemma reseat_leftUnitor_comp (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U) {X P : C}
    (c : (T.obj U).obj X ⟶ P) (r : P ⟶ X)
    (h : (reseatIso e U X).hom ≫ c ≫ r = ε.inv ▷ X ≫ (λ_ X).hom) :
    letI := reseat e ε
    (λ_ X).hom = c ≫ r := by
  rw [reseat_leftUnitor e ε X, ← h, Iso.inv_hom_id_assoc]

/-- `CategoryTheory.MonoidalCategory.reseat_rightUnitor_comp` with the comparison read through
`reseatIso` supplied as a separate equation, for the reason given on
`CategoryTheory.MonoidalCategory.reseat_associator_comp_of_eq`. -/
lemma reseat_rightUnitor_comp_of_eq (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U) {X P : C}
    {c : (T.obj X).obj U ⟶ P} (r : P ⟶ X) {d : X ⊗ U ⟶ P}
    (hc : (reseatIso e X U).hom ≫ c = d)
    (h : d ≫ r = X ◁ ε.inv ≫ (ρ_ X).hom) :
    letI := reseat e ε
    (ρ_ X).hom = c ≫ r :=
  reseat_rightUnitor_comp e ε c r (by rw [← assoc, hc]; exact h)

/-- `CategoryTheory.MonoidalCategory.reseat_leftUnitor_comp` in the same form. -/
lemma reseat_leftUnitor_comp_of_eq (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U) {X P : C}
    {c : (T.obj U).obj X ⟶ P} (r : P ⟶ X) {d : U ⊗ X ⟶ P}
    (hc : (reseatIso e U X).hom ≫ c = d)
    (h : d ≫ r = ε.inv ▷ X ≫ (λ_ X).hom) :
    letI := reseat e ε
    (λ_ X).hom = c ≫ r :=
  reseat_leftUnitor_comp e ε c r (by rw [← assoc, hc]; exact h)

/-- `CategoryTheory.MonoidalCategory.reseat_rightUnitor_comp_of_eq` with its hypothesis in the
direction a *right unitality axiom* supplies it: `(ρ_ X).hom` written through the comparison,
rather than the comparison written through `(ρ_ X).hom`.

The two differ by cancelling `ε`, and the side it is written on is not a free choice.  The
`_of_eq` form needs `ε.inv`, because that is what
`CategoryTheory.MonoidalCategory.reseat_rightUnitor` produces; the right unitality axiom of a
lax monoidal functor produces `ε.hom`.  So a consumer holding a unitality axiom must cancel `ε`,
and the cancellation has to happen here, with `ε` a *variable*: at a concrete monoidal category
the unit isomorphism carries two names -- the one the comparison is stated with and the one the
re-seating is taken at -- which are only definitionally equal, and `rw` re-checks its motive at
`implicit` transparency and will not match `ε.inv ≫ ε.hom` across that.  With `ε` a variable it
is a single `rw`. -/
lemma reseat_rightUnitor_comp_of_unitality (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U) {X P : C}
    {c : (T.obj X).obj U ⟶ P} (r : P ⟶ X) {d : X ⊗ U ⟶ P}
    (hc : (reseatIso e X U).hom ≫ c = d)
    (h : (ρ_ X).hom = X ◁ ε.hom ≫ d ≫ r) :
    letI := reseat e ε
    (ρ_ X).hom = c ≫ r :=
  reseat_rightUnitor_comp_of_eq e ε r hc (by rw [h, whiskerLeft_inv_hom_assoc])

/-- The mirror of `CategoryTheory.MonoidalCategory.reseat_rightUnitor_comp_of_unitality`.  Like
`CategoryTheory.MonoidalCategory.reseat_leftUnitor_comp` it assumes no
`CategoryTheory.BraidedCategory`: the two unitality axioms are independent fields of a lax
monoidal functor, so a consumer holding the left one needs no detour through the braiding. -/
lemma reseat_leftUnitor_comp_of_unitality (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U) {X P : C}
    {c : (T.obj U).obj X ⟶ P} (r : P ⟶ X) {d : U ⊗ X ⟶ P}
    (hc : (reseatIso e U X).hom ≫ c = d)
    (h : (λ_ X).hom = ε.hom ▷ X ≫ d ≫ r) :
    letI := reseat e ε
    (λ_ X).hom = c ≫ r :=
  reseat_leftUnitor_comp_of_eq e ε r hc (by rw [h, inv_hom_whiskerRight_assoc])

end CategoryTheory.MonoidalCategory

end
