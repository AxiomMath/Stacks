module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverComp
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverIso
public import StacksFrontier.CategoryTheory.TwoFibreProductOverReindex

/-!
# Reindexing the 2-fibre product along a 2-isomorphism of its second leg

Let `𝒳`, `𝒴`, `𝒮` be categories over `𝒞`, let `F : 𝒳 ⥤ 𝒮` and let `β : G ≅ G'` be a
2-isomorphism of 1-morphisms `𝒴 ⥤ 𝒮` over `𝒞`, that is a natural isomorphism all of whose
components are vertical. Composing the comparison isomorphism `φ : F x ≅ G y` of an object of the
2-fibre product `𝒳 ×_{F, 𝒮, G} 𝒴` with `β` at `y` turns it into an object of
`𝒳 ×_{F, 𝒮, G'} 𝒴`. This is the reindexing functor of this file.

`StacksFrontier.CategoryTheory.TwoFibreProductOverReindex` does the same for the *first* leg, and
`StacksFrontier.CategoryTheory.TwoFibreProductOverRestrict` turns that one into an equivalence over
the first factor. The second-leg case is the one a 2-isomorphism of the 1-morphism *whose base
change is being taken* produces, because the relative properties of **Stacks 03YK** and the
representability predicate of **Stacks 02ZW** put the scheme-valued point of the target in the
first leg and the 1-morphism in the second. It was previously available only as a file-private
helper of `StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityInvariance`, derived there from
the first-leg case through a symmetry functor.

As for the first leg, reindexing along `β` and along `β⁻¹` are inverse to each other **on
objects** only, so the unit and the counit of the equivalence are built by hand from
isomorphisms of the 2-fibre product whose two components are identities; the cancellation
`β ∘ β⁻¹ = id` is absorbed into the comparison isomorphism. Both reindexing functors commute
strictly with the first projection, so both are 1-morphisms of categories over `𝒳`.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.reindexSnd`: reindexing along `β : G ≅ G'`.
* `CategoryTheory.TwoFibreProductOver.reindexSndSymm`: reindexing along `β⁻¹`.

## Main results

* `CategoryTheory.TwoFibreProductOver.reindexSnd_comp_fst` and
  `CategoryTheory.TwoFibreProductOver.reindexSndSymm_comp_fst`: reindexing commutes strictly with
  the first projection.
* `CategoryTheory.TwoFibreProductOver.reindexSndEquivalenceOver`: reindexing along a
  2-isomorphism of the second leg is an equivalence over the first factor.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
-/

@[expose] public section

namespace CategoryTheory.TwoFibreProductOver

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴] {𝒮 : Type u₄} [Category.{v₄} 𝒮]
  {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒮 : 𝒮 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒮} {G G' : 𝒴 ⥤ 𝒮}

/-- A 2-isomorphism `β : G ≅ G'` of 1-morphisms over `𝒞` reindexes the 2-fibre product taken
along `G` to the one taken along `G'`, replacing the comparison isomorphism `φ : F(x) ≅ G(y)` of
an object by `φ ≫ β_y`. Verticality of `β` is what keeps the new comparison isomorphism vertical,
and naturality of `β` is what keeps the comparison squares of morphisms commutative. -/
def reindexSnd (β : G ≅ G') (hβ : ∀ y : 𝒴, p𝒮.IsHomLift (𝟙 (p𝒴.obj y)) (β.hom.app y)) :
    TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G ⥤ TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G' where
  obj P :=
    { base := P.base
      x := P.x
      y := P.y
      hx := P.hx
      hy := P.hy
      iso := P.iso ≪≫ β.app P.y
      vertical := by
        have hb : p𝒮.IsHomLift (𝟙 P.base) (β.hom.app P.y) := by
          have h0 : p𝒮.IsHomLift (𝟙 (p𝒴.obj P.y)) (β.hom.app P.y) := hβ P.y
          rwa [P.hy] at h0
        have := P.vertical
        exact IsHomLift.comp_lift_id_right p𝒮 (𝟙 P.base) P.iso.hom (β.hom.app P.y) }
  map {P Q} u :=
    { hbase := u.hbase
      a := u.a
      b := u.b
      ha := u.ha
      hb := u.hb
      w := by
        have hnat := β.hom.naturality u.b
        dsimp only [Iso.trans_hom, Iso.app_hom]
        rw [← Category.assoc, u.w, Category.assoc, hnat, Category.assoc] }
  map_id P := by apply Hom.ext <;> rfl
  map_comp u v := by apply Hom.ext <;> rfl

/-- The comparison isomorphism of a reindexed object. -/
@[simp]
lemma reindexSnd_obj_iso (β : G ≅ G') (hβ) (P : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G) :
    ((reindexSnd (F := F) β hβ).obj P).iso = P.iso ≪≫ β.app P.y := rfl

/-- Reindexing does not change the `𝒳`-component of an object. -/
@[simp]
lemma reindexSnd_obj_x (β : G ≅ G') (hβ) (P : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G) :
    ((reindexSnd (F := F) β hβ).obj P).x = P.x := rfl

/-- Reindexing does not change the `𝒴`-component of an object. -/
@[simp]
lemma reindexSnd_obj_y (β : G ≅ G') (hβ) (P : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G) :
    ((reindexSnd (F := F) β hβ).obj P).y = P.y := rfl

/-- Reindexing the second leg commutes strictly with the first projection, so it is a 1-morphism
of categories over `𝒳`. -/
lemma reindexSnd_comp_fst (β : G ≅ G') (hβ) :
    reindexSnd (F := F) β hβ ⋙ fst p𝒳 p𝒴 p𝒮 F G' = fst p𝒳 p𝒴 p𝒮 F G := rfl

/-- Verticality passes to the inverse of a 2-isomorphism of the second leg. -/
lemma isHomLift_inv_app_snd (β : G ≅ G')
    (hβ : ∀ y : 𝒴, p𝒮.IsHomLift (𝟙 (p𝒴.obj y)) (β.hom.app y)) (y : 𝒴) :
    p𝒮.IsHomLift (𝟙 (p𝒴.obj y)) (β.symm.hom.app y) :=
  have : p𝒮.IsHomLift (𝟙 (p𝒴.obj y)) (β.app y).hom := hβ y
  IsHomLift.lift_id_inv p𝒮 _ (β.app y)

/-- Reindexing the second leg along the inverse of `β`. -/
def reindexSndSymm (β : G ≅ G')
    (hβ : ∀ y : 𝒴, p𝒮.IsHomLift (𝟙 (p𝒴.obj y)) (β.hom.app y)) :
    TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G' ⥤ TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G :=
  reindexSnd (F := F) β.symm (isHomLift_inv_app_snd β hβ)

/-- The comparison isomorphism of an object reindexed along `β⁻¹`. -/
@[simp]
lemma reindexSndSymm_obj_iso_hom (β : G ≅ G') (hβ) (R : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G') :
    ((reindexSndSymm (F := F) β hβ).obj R).iso.hom = R.iso.hom ≫ β.inv.app R.y := rfl

/-- Reindexing along `β⁻¹` does not change the `𝒴`-component of an object. -/
@[simp]
lemma reindexSndSymm_obj_y (β : G ≅ G') (hβ) (R : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G') :
    ((reindexSndSymm (F := F) β hβ).obj R).y = R.y := rfl

/-- Reindexing along `β⁻¹` commutes strictly with the first projection. -/
lemma reindexSndSymm_comp_fst (β : G ≅ G') (hβ) :
    reindexSndSymm (F := F) β hβ ⋙ fst p𝒳 p𝒴 p𝒮 F G = fst p𝒳 p𝒴 p𝒮 F G' := rfl

section EquivalenceOver

attribute [local implicit_reducible] fst

/-- The unit of `CategoryTheory.TwoFibreProductOver.reindexSndEquivalenceOver`: reindexing along
`β` and then along `β⁻¹` returns an object with the same two components, the comparison
isomorphism having been composed with `β ∘ β⁻¹`. The two components of the unit are therefore
identities. -/
noncomputable def reindexSndUnit (β : G ≅ G')
    (hβ : ∀ y : 𝒴, p𝒮.IsHomLift (𝟙 (p𝒴.obj y)) (β.hom.app y)) :
    𝟭 (TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G) ≅
      reindexSnd (F := F) β hβ ⋙ reindexSndSymm (F := F) β hβ := by
  refine NatIso.ofComponents (fun P => ?_) (fun {P Q} φ => ?_)
  · refine isoMkVertical (U := P.base) (Iso.refl P.x) (Iso.refl P.y)
      (IsHomLift.id P.hx) (IsHomLift.id P.hy) ?_
    change F.map (𝟙 P.x) ≫ (P.iso.hom ≫ β.hom.app P.y) ≫ β.inv.app P.y =
      P.iso.hom ≫ G.map (𝟙 P.y)
    simp
  · refine Hom.ext' ?_ ?_
    · change φ.a ≫ 𝟙 Q.x = 𝟙 P.x ≫ φ.a
      simp
    · change φ.b ≫ 𝟙 Q.y = 𝟙 P.y ≫ φ.b
      simp

/-- The counit of `CategoryTheory.TwoFibreProductOver.reindexSndEquivalenceOver`. -/
noncomputable def reindexSndCounit (β : G ≅ G')
    (hβ : ∀ y : 𝒴, p𝒮.IsHomLift (𝟙 (p𝒴.obj y)) (β.hom.app y)) :
    reindexSndSymm (F := F) β hβ ⋙ reindexSnd (F := F) β hβ ≅
      𝟭 (TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G') := by
  refine NatIso.ofComponents (fun P => ?_) (fun {P Q} φ => ?_)
  · refine isoMkVertical (U := P.base) (Iso.refl P.x) (Iso.refl P.y)
      (IsHomLift.id P.hx) (IsHomLift.id P.hy) ?_
    change F.map (𝟙 P.x) ≫ P.iso.hom =
      ((P.iso.hom ≫ β.inv.app P.y) ≫ β.hom.app P.y) ≫ G'.map (𝟙 P.y)
    simp
  · refine Hom.ext' ?_ ?_
    · change φ.a ≫ 𝟙 Q.x = 𝟙 P.x ≫ φ.a
      simp
    · change φ.b ≫ 𝟙 Q.y = 𝟙 P.y ≫ φ.b
      simp

/-- **Reindexing a 2-fibre product along a 2-isomorphism of its second leg is an equivalence over
the first factor.** For `β : G ≅ G'` a natural isomorphism of 1-morphisms `𝒴 ⥤ 𝒮` over `𝒞` all of
whose components are vertical, the first projections of `𝒳 ×_{F, 𝒮, G} 𝒴` and of
`𝒳 ×_{F, 𝒮, G'} 𝒴` are equivalent as categories over `𝒳`. -/
noncomputable def reindexSndEquivalenceOver (β : G ≅ G')
    (hβ : ∀ y : 𝒴, p𝒮.IsHomLift (𝟙 (p𝒴.obj y)) (β.hom.app y)) :
    StacksRepresentableCFG.EquivalenceOver (fst p𝒳 p𝒴 p𝒮 F G) (fst p𝒳 p𝒴 p𝒮 F G') where
  hom := ⟨reindexSnd (F := F) β hβ, reindexSnd_comp_fst β hβ⟩
  inv := ⟨reindexSndSymm (F := F) β hβ, reindexSndSymm_comp_fst β hβ⟩
  unitIso := reindexSndUnit (F := F) β hβ
  counitIso := reindexSndCounit (F := F) β hβ
  unit_over := by
    refine StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ (fun R => ?_)
    refine IsHomLift.of_fac' _ _ _ rfl rfl ?_
    change 𝟙 R.x = eqToHom rfl ≫ 𝟙 R.x ≫ eqToHom rfl
    simp
  counit_over := by
    refine StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ (fun R => ?_)
    refine IsHomLift.of_fac' _ _ _ rfl rfl ?_
    change 𝟙 R.x = eqToHom rfl ≫ 𝟙 R.x ≫ eqToHom rfl
    simp

end EquivalenceOver

end CategoryTheory.TwoFibreProductOver

end
