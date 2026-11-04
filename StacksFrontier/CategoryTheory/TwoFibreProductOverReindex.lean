module

public import StacksFrontier.CategoryTheory.TwoFibreProductOver

/-!
# Reindexing the 2-fibre product along a 2-isomorphism of one leg

Let `𝒳`, `𝒴`, `𝒮` be categories over `𝒞`, let `G : 𝒴 ⥤ 𝒮` and let `α : F ≅ F'` be a
2-isomorphism of 1-morphisms `𝒳 ⥤ 𝒮` over `𝒞`, that is a natural isomorphism all of whose
components are vertical. Composing the comparison isomorphism of an object of the 2-fibre product
`𝒳 ×_𝒮 𝒴` taken along `F` with `α` turns it into an object of the 2-fibre product taken along
`F'`. This is the reindexing functor of this file.

Reindexing along `α` and along `α⁻¹` are inverse to each other **on objects**, each round trip
returning the original object; the identification is not definitional, because composing an
isomorphism with `α` and then with `α⁻¹` returns the original isomorphism only up to the
cancellation `α ∘ α⁻¹ = id`. On morphisms both round trips leave every component unchanged, so the
two composites are nonetheless equal to the identity *as functors*, and reindexing is an
equivalence.

Both reindexing functors are strictly over the first projection, so they are 1-morphisms of
categories over `𝒳` — in the application to Stacks 02Y9, over the slice `𝒞/U`.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.reindex`: reindexing along `α : F ≅ F'`.
* `CategoryTheory.TwoFibreProductOver.reindexSymm`: reindexing along `α⁻¹`.
* `CategoryTheory.TwoFibreProductOver.reindexEquivalence`: the two as an equivalence, whose unit
  and counit are the `CategoryTheory.eqToIso` of the two round-trip equations.

## Main results

* `CategoryTheory.TwoFibreProductOver.obj_ext_of_faithful`: when the structure functor of the
  target of the cospan is faithful, an object of the 2-fibre product is determined by its base
  and its two components.
* `CategoryTheory.TwoFibreProductOver.reindex_comp_fst` and
  `CategoryTheory.TwoFibreProductOver.reindexSymm_comp_fst`: reindexing commutes strictly with the
  first projection.
* `CategoryTheory.TwoFibreProductOver.reindexSymm_reindex_obj` and
  `CategoryTheory.TwoFibreProductOver.reindex_reindexSymm_obj`: the two reindexing functors are
  mutually inverse on objects.
* `CategoryTheory.TwoFibreProductOver.reindexSymm_comp_reindex` and
  `CategoryTheory.TwoFibreProductOver.reindex_comp_reindexSymm`: the same two round trips as
  equations of functors.
* `CategoryTheory.TwoFibreProductOver.isEquivalence_reindex` and
  `CategoryTheory.TwoFibreProductOver.reindexSymm_isEquivalence`: both reindexing functors are
  equivalences.
-/

@[expose] public section


namespace CategoryTheory.TwoFibreProductOver

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴] {𝒮 : Type u₄} [Category.{v₄} 𝒮]
  {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒮 : 𝒮 ⥤ 𝒞} {F F' : 𝒳 ⥤ 𝒮} {G : 𝒴 ⥤ 𝒮}

/-- Objects of the 2-fibre product agreeing in every component and with equal comparison
isomorphisms are equal. The remaining fields are propositions, so they need not be compared. -/
lemma obj_ext {base : 𝒞} {x : 𝒳} {y : 𝒴} {hx : p𝒳.obj x = base} {hy : p𝒴.obj y = base}
    {i j : F.obj x ≅ G.obj y} (h : i = j) {vi : p𝒮.IsHomLift (𝟙 base) i.hom}
    {vj : p𝒮.IsHomLift (𝟙 base) j.hom} :
    (⟨base, x, y, hx, hy, i, vi⟩ : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G) =
      ⟨base, x, y, hx, hy, j, vj⟩ := by
  subst h; rfl

/-- **Objects of the 2-fibre product agreeing in their three components are equal as soon as the
structure functor of the target is faithful.** The two comparison isomorphisms are then forced to
agree: both are vertical over the common base, so both have the same image under the structure
functor, and faithfulness identifies them. -/
lemma obj_ext_of_faithful [p𝒮.Faithful] {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G}
    (hbase : P.base = Q.base) (hx : P.x = Q.x) (hy : P.y = Q.y) : P = Q := by
  obtain ⟨b, x, y, hbx, hby, i, vi⟩ := P
  obtain ⟨b', x', y', hb'x, hb'y, j, vj⟩ := Q
  dsimp only at hbase hx hy
  cases hbase
  cases hx
  cases hy
  exact obj_ext (Iso.ext (p𝒮.map_injective (by
    rw [IsHomLift.fac' p𝒮 (𝟙 b) i.hom, IsHomLift.fac' p𝒮 (𝟙 b) j.hom])))

/-- A 2-isomorphism `α : F ≅ F'` of 1-morphisms over `𝒞` reindexes the 2-fibre product taken along
`F` to the one taken along `F'`, replacing the comparison isomorphism `φ : F(x) ≅ G(y)` of an
object by `α_x⁻¹ ≫ φ`. Verticality of `α` is what keeps the new comparison isomorphism vertical,
and naturality of `α` is what keeps the comparison squares of morphisms commutative. -/
def reindex (α : F ≅ F') (hα : ∀ x : 𝒳, p𝒮.IsHomLift (𝟙 (p𝒳.obj x)) (α.hom.app x)) :
    TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G ⥤ TwoFibreProductOver p𝒳 p𝒴 p𝒮 F' G where
  obj P :=
    { base := P.base
      x := P.x
      y := P.y
      hx := P.hx
      hy := P.hy
      iso := (α.app P.x).symm ≪≫ P.iso
      vertical := by
        have hinv : p𝒮.IsHomLift (𝟙 P.base) (α.inv.app P.x) := by
          have : p𝒮.IsHomLift (𝟙 (p𝒳.obj P.x)) (α.app P.x).hom := hα P.x
          have h0 : p𝒮.IsHomLift (𝟙 (p𝒳.obj P.x)) (α.app P.x).inv :=
            IsHomLift.lift_id_inv p𝒮 _ (α.app P.x)
          rwa [P.hx] at h0
        have := P.vertical
        exact IsHomLift.comp_lift_id_right p𝒮 (𝟙 P.base) (α.inv.app P.x) P.iso.hom }
  map {P Q} u :=
    { hbase := u.hbase
      a := u.a
      b := u.b
      ha := u.ha
      hb := u.hb
      w := by
        have hnat := α.inv.naturality u.a
        dsimp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv]
        rw [← Category.assoc, hnat, Category.assoc, u.w]
        simp }
  map_id P := by apply Hom.ext <;> rfl
  map_comp u v := by apply Hom.ext <;> rfl

/-- The comparison isomorphism of a reindexed object. -/
@[simp]
lemma reindex_obj_iso (α : F ≅ F') (hα) (P : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G) :
    ((reindex (G := G) α hα).obj P).iso = (α.app P.x).symm ≪≫ P.iso := rfl

/-- Reindexing does not change the `𝒳`-component of an object. -/
@[simp]
lemma reindex_obj_x (α : F ≅ F') (hα) (P : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G) :
    ((reindex (G := G) α hα).obj P).x = P.x := rfl

/-- Reindexing commutes strictly with the first projection, so it is a 1-morphism of categories
over `𝒳`. -/
lemma reindex_comp_fst (α : F ≅ F') (hα) :
    reindex (G := G) α hα ⋙ fst p𝒳 p𝒴 p𝒮 F' G = fst p𝒳 p𝒴 p𝒮 F G := rfl

/-- Verticality of a single component of a natural isomorphism passes to that component of the
inverse, at an arbitrary object of the base. This is the general form: it fixes neither the
base object nor the functor into which the components are taken, and
`CategoryTheory.TwoFibreProductOver.isHomLift_inv_app` is its instance at
`V = p𝒳.obj x` quantified over `x`. -/
lemma isHomLift_inv_app_of_isHomLift {𝒜 : Type*} [Category 𝒜] {p𝒜 : 𝒜 ⥤ 𝒞} {D : Type*}
    [Category D] {E E' : D ⥤ 𝒜} (e : E ≅ E') {V : 𝒞} (X : D)
    (h : p𝒜.IsHomLift (𝟙 V) (e.hom.app X)) : p𝒜.IsHomLift (𝟙 V) (e.inv.app X) :=
  have : p𝒜.IsHomLift (𝟙 V) (e.app X).hom := h
  IsHomLift.lift_id_inv p𝒜 _ (e.app X)

/-- Verticality passes to the inverse of a 2-isomorphism. -/
lemma isHomLift_inv_app (α : F ≅ F')
    (hα : ∀ x : 𝒳, p𝒮.IsHomLift (𝟙 (p𝒳.obj x)) (α.hom.app x)) (x : 𝒳) :
    p𝒮.IsHomLift (𝟙 (p𝒳.obj x)) (α.symm.hom.app x) :=
  isHomLift_inv_app_of_isHomLift α x (hα x)

/-- Reindexing along the inverse of `α`. -/
def reindexSymm (α : F ≅ F') (hα : ∀ x : 𝒳, p𝒮.IsHomLift (𝟙 (p𝒳.obj x)) (α.hom.app x)) :
    TwoFibreProductOver p𝒳 p𝒴 p𝒮 F' G ⥤ TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G :=
  reindex α.symm (isHomLift_inv_app α hα)

/-- The comparison isomorphism of an object reindexed along `α⁻¹`. -/
@[simp]
lemma reindexSymm_obj_iso_hom (α : F ≅ F') (hα) (R : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F' G) :
    ((reindexSymm (G := G) α hα).obj R).iso.hom = α.hom.app R.x ≫ R.iso.hom := rfl

/-- Reindexing along `α⁻¹` does not change the `𝒳`-component of an object. -/
@[simp]
lemma reindexSymm_obj_x (α : F ≅ F') (hα) (R : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F' G) :
    ((reindexSymm (G := G) α hα).obj R).x = R.x := rfl

/-- Reindexing along `α⁻¹` commutes strictly with the first projection. -/
lemma reindexSymm_comp_fst (α : F ≅ F') (hα) :
    reindexSymm (G := G) α hα ⋙ fst p𝒳 p𝒴 p𝒮 F G = fst p𝒳 p𝒴 p𝒮 F' G := rfl

/-- Reindexing along `α` and then along `α⁻¹` returns the original object. -/
lemma reindexSymm_reindex_obj (α : F ≅ F') (hα) (P : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G) :
    (reindexSymm (G := G) α hα).obj ((reindex (G := G) α hα).obj P) = P := by
  obtain ⟨base, x, y, hx, hy, iso, vertical⟩ := P
  exact obj_ext (Iso.ext (by simp [reindex]))

/-- Reindexing along `α⁻¹` and then along `α` returns the original object. -/
lemma reindex_reindexSymm_obj (α : F ≅ F') (hα) (R : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F' G) :
    (reindex (G := G) α hα).obj ((reindexSymm (G := G) α hα).obj R) = R := by
  obtain ⟨base, x, y, hx, hy, iso, vertical⟩ := R
  exact obj_ext (Iso.ext (by simp [reindexSymm, reindex]))

/-- The `𝒳`-component of the morphism `eqToHom h` attached to an equality of objects of the
2-fibre product is the `eqToHom` of the equality of their `𝒳`-components. This is the
`CategoryTheory.Over`-specialised `CategoryTheory.TwoFibreProductOver.eqToHom_a` of
`StacksFrontier.CategoryTheory.TwoFibreProductOverRelocalize`, stated over an arbitrary base
category and therefore under a name that does not collide with it. -/
theorem Hom.a_eqToHom {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (h : P = Q) :
    (eqToHom h : P ⟶ Q).a =
      eqToHom (congrArg (fun R : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G => R.x) h) := by
  cases h
  rfl

/-- The `𝒴`-component of the morphism `eqToHom h` attached to an equality of objects of the
2-fibre product is the `eqToHom` of the equality of their `𝒴`-components. This is the
`CategoryTheory.Over`-specialised `CategoryTheory.TwoFibreProductOver.eqToHom_b` of
`StacksFrontier.CategoryTheory.TwoFibreProductOverRelocalize`, stated over an arbitrary base
category and therefore under a name that does not collide with it. -/
theorem Hom.b_eqToHom {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (h : P = Q) :
    (eqToHom h : P ⟶ Q).b =
      eqToHom (congrArg (fun R : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G => R.y) h) := by
  cases h
  rfl

/-- An endofunctor of the 2-fibre product that is the identity on objects and on the two components
of every morphism is the identity functor. -/
private theorem eq_id_of_obj_eq_of_components {Φ : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G ⥤
    TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (hobj : ∀ P, Φ.obj P = P)
    (ha : ∀ {P Q} (f : P ⟶ Q), HEq (Φ.map f).a f.a)
    (hb : ∀ {P Q} (f : P ⟶ Q), HEq (Φ.map f).b f.b) :
    Φ = 𝟭 _ := by
  refine Functor.ext hobj fun P Q f => Hom.ext' ?_ ?_
  · exact eq_of_heq ((ha f).trans (by simp))
  · exact eq_of_heq ((hb f).trans (by simp))

/-- **Reindexing along `α⁻¹` and then along `α` is the identity functor.** On objects this is
`CategoryTheory.TwoFibreProductOver.reindex_reindexSymm_obj`; on morphisms both functors are the
identity on every component, so the two sides agree after `Hom.ext'`. -/
theorem reindexSymm_comp_reindex (α : F ≅ F')
    (hα : ∀ x : 𝒳, p𝒮.IsHomLift (𝟙 (p𝒳.obj x)) (α.hom.app x)) :
    reindexSymm (p𝒴 := p𝒴) (G := G) α hα ⋙ reindex (p𝒴 := p𝒴) (G := G) α hα = 𝟭 _ := by
  refine eq_id_of_obj_eq_of_components (reindex_reindexSymm_obj α hα)
    (fun _ => .rfl) fun _ => .rfl

/-- **Reindexing along `α` and then along `α⁻¹` is the identity functor.** The companion of
`CategoryTheory.TwoFibreProductOver.reindexSymm_comp_reindex`, over
`CategoryTheory.TwoFibreProductOver.reindexSymm_reindex_obj`. -/
theorem reindex_comp_reindexSymm (α : F ≅ F')
    (hα : ∀ x : 𝒳, p𝒮.IsHomLift (𝟙 (p𝒳.obj x)) (α.hom.app x)) :
    reindex (p𝒴 := p𝒴) (G := G) α hα ⋙ reindexSymm (p𝒴 := p𝒴) (G := G) α hα = 𝟭 _ := by
  refine eq_id_of_obj_eq_of_components (reindexSymm_reindex_obj α hα)
    (fun _ => .rfl) fun _ => .rfl

/-- **Reindexing along a 2-isomorphism of one leg is an equivalence**, with inverse the
reindexing along the inverse 2-isomorphism. -/
noncomputable def reindexEquivalence (α : F ≅ F')
    (hα : ∀ x : 𝒳, p𝒮.IsHomLift (𝟙 (p𝒳.obj x)) (α.hom.app x)) :
    TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G ≌ TwoFibreProductOver p𝒳 p𝒴 p𝒮 F' G :=
  Equivalence.mk (reindex (p𝒴 := p𝒴) (G := G) α hα) (reindexSymm (p𝒴 := p𝒴) (G := G) α hα)
    (eqToIso (reindex_comp_reindexSymm (p𝒴 := p𝒴) (G := G) α hα).symm)
    (eqToIso (reindexSymm_comp_reindex (p𝒴 := p𝒴) (G := G) α hα))

/-- Reindexing along `α` is an equivalence of categories. -/
theorem isEquivalence_reindex (α : F ≅ F')
    (hα : ∀ x : 𝒳, p𝒮.IsHomLift (𝟙 (p𝒳.obj x)) (α.hom.app x)) :
    (reindex (p𝒴 := p𝒴) (G := G) α hα).IsEquivalence :=
  (reindexEquivalence (p𝒴 := p𝒴) (G := G) α hα).isEquivalence_functor

/-- Reindexing along `α⁻¹` is an equivalence of categories. -/
theorem reindexSymm_isEquivalence (α : F ≅ F')
    (hα : ∀ x : 𝒳, p𝒮.IsHomLift (𝟙 (p𝒳.obj x)) (α.hom.app x)) :
    (reindexSymm (p𝒴 := p𝒴) (G := G) α hα).IsEquivalence :=
  (reindexEquivalence (p𝒴 := p𝒴) (G := G) α hα).isEquivalence_inverse

end CategoryTheory.TwoFibreProductOver
