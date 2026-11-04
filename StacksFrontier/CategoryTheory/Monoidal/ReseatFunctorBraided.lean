module

public import StacksFrontier.CategoryTheory.Monoidal.ReseatFunctor
import all StacksFrontier.CategoryTheory.Monoidal.ReseatFunctor
public import StacksFrontier.CategoryTheory.Monoidal.ReseatConstraints

/-!
# Monoidal and braided functors between re-seated structures

A monoidal functor is monoidal for re-seatings of the monoidal structures of its source and
target, and a braided monoidal functor is braided for them.

## Main definitions

* `CategoryTheory.MonoidalCategory.reseatInverseMonoidal`: the identity functor, from a monoidal
  structure to a re-seating of it, as a monoidal functor.
* `CategoryTheory.MonoidalCategory.reseatFunctorMonoidal`: a monoidal functor as a monoidal
  functor between re-seated structures.
* `CategoryTheory.Functor.Braided.ofOplax`: a monoidal functor whose oplax tensorator commutes
  with the braidings, as a braided functor.
* `CategoryTheory.MonoidalCategory.reseatFunctorBraided`: a braided monoidal functor as a braided
  functor between re-seated structures.

## Main results

* `CategoryTheory.MonoidalCategory.reseatFunctorMonoidal_δ`,
  `CategoryTheory.MonoidalCategory.reseatFunctorMonoidal_η`,
  `CategoryTheory.MonoidalCategory.reseatFunctorMonoidal_ε`: the tensorator and units of
  `reseatFunctorMonoidal`.
* `CategoryTheory.Functor.map_braiding_comp_δ`: the braiding axiom of a braided functor, in
  oplax form.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.MonoidalCategory

open Category CategoryTheory.Functor

section Inverse

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] {T : C ⥤ C ⥤ C} {U : C}

/-- The identity functor, from `C` with the given structure to `C` with the re-seated one, as a
`Functor.CoreMonoidal`: the unit is `ε⁻¹` and the tensorator is the inverse of `reseatIso`. -/
def reseatInverseCoreMonoidal (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U) :
    @Functor.CoreMonoidal C _ _ C _ (reseat e ε) (𝟭 C) :=
  @Functor.CoreMonoidal.mk C _ _ C _ (reseat e ε) (𝟭 C) ε.symm (fun X Y ↦ (reseatIso e X Y).symm)
    (fun {X₁ X₂} f Y ↦ by
      change (T.map f).app Y ≫ (reseatIso e X₂ Y).inv = (reseatIso e X₁ Y).inv ≫ f ▷ Y
      rw [reseat_whiskerRight e f Y]
      simp)
    (fun {Y₁ Y₂} X g ↦ by
      change (T.obj X).map g ≫ (reseatIso e X Y₂).inv = (reseatIso e X Y₁).inv ≫ X ◁ g
      rw [reseat_whiskerLeft e X g]
      simp)
    (fun X Y Z ↦ by
      change (T.map (reseatIso e X Y).inv).app Z ≫ (reseatIso e (X ⊗ Y) Z).inv ≫ (α_ X Y Z).hom =
        (((reseatIso e ((T.obj X).obj Y) Z).inv ≫ ((reseatIso e X Y).inv ⊗ₘ 𝟙 Z)) ≫
          (α_ X Y Z).hom ≫ (𝟙 X ⊗ₘ (reseatIso e Y Z).hom) ≫
            (reseatIso e X ((T.obj Y).obj Z)).hom) ≫
          (T.obj X).map (reseatIso e Y Z).inv ≫ (reseatIso e X (Y ⊗ Z)).inv
      rw [reseat_whiskerRight e _ Z, reseat_whiskerLeft e X _]
      simp [tensorHom_id, id_tensorHom])
    (fun X ↦ by
      change ((reseatIso e U X).inv ≫ (ε.inv ⊗ₘ 𝟙 X)) ≫ (λ_ X).hom =
        (T.map ε.inv).app X ≫ (reseatIso e (𝟙_ C) X).inv ≫ (λ_ X).hom
      rw [reseat_whiskerRight e _ X]
      simp [tensorHom_id])
    (fun X ↦ by
      change ((reseatIso e X U).inv ≫ (𝟙 X ⊗ₘ ε.inv)) ≫ (ρ_ X).hom =
        (T.obj X).map ε.inv ≫ (reseatIso e X (𝟙_ C)).inv ≫ (ρ_ X).hom
      rw [reseat_whiskerLeft e X _]
      simp [id_tensorHom])

/-- **The identity functor, from the given structure to the re-seated one, is monoidal.** -/
@[instance_reducible]
def reseatInverseMonoidal (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U) :
    @Functor.Monoidal C _ _ C _ (reseat e ε) (𝟭 C) :=
  @Functor.CoreMonoidal.toMonoidal C _ _ C _ (reseat e ε) (𝟭 C) (reseatInverseCoreMonoidal e ε)

end Inverse

section Functor

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] {T : C ⥤ C ⥤ C} {U : C}
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] {T' : D ⥤ D ⥤ D} {U' : D}

/-- **A monoidal functor is monoidal for re-seatings of its source and target structures**: it is
the composite of the identity functor from the re-seated source structure to the given one, the
functor itself, and the identity functor from the given target structure to the re-seated one. -/
@[instance_reducible]
def reseatFunctorMonoidal (F : C ⥤ D) [F.Monoidal] (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U)
    (e' : curriedTensor D ≅ T') (ε' : 𝟙_ D ≅ U') :
    @Functor.Monoidal C _ (reseat e ε) D _ (reseat e' ε') F :=
  letI := reseatMonoidal e ε
  letI := reseatInverseMonoidal e' ε'
  @Functor.Monoidal.instComp C _ (reseat e ε) C _ _ D _ (reseat e' ε') (𝟭 C) (F ⋙ 𝟭 D) _
    (@Functor.Monoidal.instComp C _ _ D _ _ D _ (reseat e' ε') F (𝟭 D) _ _)

/-- The tensorator of `reseatFunctorMonoidal`, in its oplax form, is that of `F` conjugated by
the two re-seating isomorphisms. -/
lemma reseatFunctorMonoidal_δ (F : C ⥤ D) [F.Monoidal] (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U)
    (e' : curriedTensor D ≅ T') (ε' : 𝟙_ D ≅ U') (X Y : C) :
    @OplaxMonoidal.δ C _ (reseat e ε) D _ (reseat e' ε') F
        (reseatFunctorMonoidal F e ε e' ε').toOplaxMonoidal X Y =
      F.map (reseatIso e X Y).inv ≫ OplaxMonoidal.δ F X Y ≫
        (reseatIso e' (F.obj X) (F.obj Y)).hom :=
  rfl

/-- The unit of `reseatFunctorMonoidal`, in its oplax form, is that of `F` conjugated by the two
unit isomorphisms. -/
lemma reseatFunctorMonoidal_η (F : C ⥤ D) [F.Monoidal] (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U)
    (e' : curriedTensor D ≅ T') (ε' : 𝟙_ D ≅ U') :
    @OplaxMonoidal.η C _ (reseat e ε) D _ (reseat e' ε') F
        (reseatFunctorMonoidal F e ε e' ε').toOplaxMonoidal =
      F.map ε.inv ≫ OplaxMonoidal.η F ≫ ε'.hom :=
  rfl

/-- The unit of `reseatFunctorMonoidal`, in its lax form, is that of `F` conjugated by the two
unit isomorphisms. -/
lemma reseatFunctorMonoidal_ε (F : C ⥤ D) [F.Monoidal] (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U)
    (e' : curriedTensor D ≅ T') (ε' : 𝟙_ D ≅ U') :
    @LaxMonoidal.ε C _ (reseat e ε) D _ (reseat e' ε') F
        (reseatFunctorMonoidal F e ε e' ε').toLaxMonoidal =
      ε'.inv ≫ LaxMonoidal.ε F ≫ F.map ε.hom := by
  show (ε'.inv ≫ LaxMonoidal.ε F) ≫ F.map ε.hom = _
  rw [Category.assoc]

end Functor

end CategoryTheory.MonoidalCategory

namespace CategoryTheory

open Category MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

section Oplax

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]

/-- **A monoidal functor whose oplax tensorator commutes with the braidings is braided.** -/
@[instance_reducible]
def Functor.Braided.ofOplax (F : C ⥤ D) [F.Monoidal]
    (h : ∀ X Y : C, F.map (β_ X Y).hom ≫ δ F Y X = δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom) :
    F.Braided where
  braided X Y := by
    rw [← cancel_mono (δ F Y X), assoc, h, Functor.Monoidal.μ_δ_assoc, assoc,
      Functor.Monoidal.μ_δ, comp_id]

/-- **The braiding axiom of a braided functor, in oplax form**: `F(β) ≫ δ = δ ≫ β`. -/
@[reassoc]
lemma Functor.map_braiding_comp_δ (F : C ⥤ D) [F.Braided] (X Y : C) :
    F.map (β_ X Y).hom ≫ δ F Y X = δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom := by
  rw [Functor.map_braiding, assoc, assoc, Functor.Monoidal.μ_δ, comp_id]

end Oplax

namespace MonoidalCategory

section BraidedFunctor

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
  {T : C ⥤ C ⥤ C} {U : C}
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
  {T' : D ⥤ D ⥤ D} {U' : D}

/-- **A braided monoidal functor is braided for re-seatings of its source and target
structures**, with the braidings `reseatBraided` on both sides. -/
@[instance_reducible]
noncomputable def reseatFunctorBraided (F : C ⥤ D) [F.Braided] (e : curriedTensor C ≅ T)
    (ε : 𝟙_ C ≅ U) (e' : curriedTensor D ≅ T') (ε' : 𝟙_ D ≅ U') :
    @Functor.Braided C _ (reseat e ε) (reseatBraided e ε) D _ (reseat e' ε')
      (reseatBraided e' ε') F :=
  @Functor.Braided.ofOplax C _ (reseat e ε) (reseatBraided e ε) D _ (reseat e' ε')
    (reseatBraided e' ε') F (reseatFunctorMonoidal F e ε e' ε') fun X Y ↦ by
      rw [reseatFunctorMonoidal_δ, reseatFunctorMonoidal_δ, reseat_braiding, reseat_braiding,
        Functor.map_comp, Functor.map_comp, assoc, assoc, ← Functor.map_comp_assoc F
        (reseatIso e Y X).hom, Iso.hom_inv_id, Functor.map_id, id_comp,
        Functor.map_braiding_comp_δ_assoc, assoc, assoc, Iso.hom_inv_id_assoc]

end BraidedFunctor

end MonoidalCategory

end CategoryTheory

end
