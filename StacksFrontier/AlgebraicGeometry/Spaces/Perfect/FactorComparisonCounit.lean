module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisComparison

/-!
# The comparison of left adjoints attached to a factorization is a counit

Let `R : A ⥤ D` and `Q : D ⥤ E` be composable functors with an identification
`e : R ⋙ Q ≅ T`, and let `L ⊣ T`, `L' ⊣ R` be left adjoints.  The comparison
`CategoryTheory.Adjunction.factorLeftAdjointComparison` is then a natural transformation
`T ⋙ L ⟶ R ⋙ L'`.

Suppose moreover that `Q` itself has a left adjoint `L'' ⊣ Q`.  Then `L'' ⋙ L'` is a left
adjoint of `R ⋙ Q`, hence of `T` through `e`, and this file identifies the comparison: it is the
canonical isomorphism `L ≅ L'' ⋙ L'` of left adjoints of `T`, followed by `L'` applied to the
counit of `L'' ⊣ Q` read through `e`.

In the Mayer–Vietoris situation of Stacks 08GV this says that the comparison
`j_{P!}(F|_P) ⟶ j_{V!}(F|_V)` out of the intersection of an elementary distinguished square is
`j_{V!}` applied to the counit of the extension-by-zero adjunction along the second projection
`P ⟶ V`.  Since Equation 08GU computes the stalk of `j_{V!}` of a map as the direct sum of the
stalks of that map at the lifts, this is what reduces the invertibility of the comparison on
stalks to the invertibility of a counit on stalks.

## Main definitions

* `CategoryTheory.Adjunction.factorComposed`: the composite `L'' ⋙ L'` as a left adjoint of `T`.

## Main results

* `CategoryTheory.Adjunction.factorUnit_app` and
  `CategoryTheory.Adjunction.homEquiv_factorLeftAdjointComparison_app`: the comparison is, by
  definition, the adjoint transpose of the unit of `L' ⊣ R` read through `e`.
* `CategoryTheory.Adjunction.factorLeftAdjointComparison_app`: **the comparison is `L'` of a
  counit**, up to the canonical isomorphism of left adjoints of `T`.

## Implementation notes

The proof is the adjoint transpose and nothing else.  Both sides are maps out of `L` applied to
`T`, so they agree as soon as their transposes under `L ⊣ T` do; the transpose of the left side
is the defining one by construction, and the transpose of the right side is computed by the
naturality of `e`, the naturality of the unit of `L' ⊣ R`, the naturality of the unit of
`L'' ⊣ Q` and the right triangle identity of `L'' ⊣ Q`, in that order.  The only input beyond
formal manipulation is `CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app`, which says that
the canonical isomorphism of two left adjoints of `T` carries one unit to the other.
-/

@[expose] public noncomputable section

open CategoryTheory Category

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

section Transpose

variable {A : Type u₁} [Category.{v₁} A] {E : Type u₃} [Category.{v₃} E]
  {T : A ⥤ E} {L : E ⥤ A}

/-- The adjoint transpose of a natural transformation out of `T ⋙ L`, read at one object. -/
theorem Adjunction.whiskerRight_homEquiv_app (adj : L ⊣ T) {K : A ⥤ A} (β : T ⋙ L ⟶ K)
    (F : A) :
    (((adj.whiskerRight A).homEquiv T K) β).app F =
      adj.homEquiv (T.obj F) (K.obj F) (β.app F) := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp [Adjunction.whiskerRight]

end Transpose

variable {A : Type u₁} [Category.{v₁} A] {D : Type u₂} [Category.{v₂} D] {E : Type u₃}
  [Category.{v₃} E] (R : A ⥤ D) (Q : D ⥤ E) (T : A ⥤ E) (e : R ⋙ Q ≅ T)
  {L : E ⥤ A} {L' : D ⥤ A} {L'' : E ⥤ D}

/-- The component of `CategoryTheory.Adjunction.factorUnit`: the unit of `L' ⊣ R` restricted
along `Q` and read through `e`. -/
theorem Adjunction.factorUnit_app (adj' : L' ⊣ R) (F : A) :
    (Adjunction.factorUnit R Q T e adj').app F =
      e.inv.app F ≫ Q.map (adj'.unit.app (R.obj F)) ≫ e.hom.app (L'.obj (R.obj F)) := by
  simp [Adjunction.factorUnit]

/-- **The comparison of left adjoints attached to a factorization is the adjoint transpose of
the restricted unit**, read at one object. -/
theorem Adjunction.homEquiv_factorLeftAdjointComparison_app (adj : L ⊣ T) (adj' : L' ⊣ R)
    (F : A) :
    adj.homEquiv (T.obj F) ((R ⋙ L').obj F)
        ((Adjunction.factorLeftAdjointComparison R Q T e adj adj').app F) =
      (Adjunction.factorUnit R Q T e adj').app F := by
  have h : ((adj.whiskerRight A).homEquiv T (R ⋙ L'))
      (Adjunction.factorLeftAdjointComparison R Q T e adj adj') =
      Adjunction.factorUnit R Q T e adj' :=
    Equiv.apply_symm_apply _ _
  have h2 := Adjunction.whiskerRight_homEquiv_app adj
    (Adjunction.factorLeftAdjointComparison R Q T e adj adj') F
  rw [← h2, h]

/-- **`L'' ⋙ L'` is a left adjoint of `T`**: it is a left adjoint of `R ⋙ Q`, which `e`
identifies with `T`. -/
def Adjunction.factorComposed (adj' : L' ⊣ R) (adj'' : L'' ⊣ Q) : (L'' ⋙ L') ⊣ T :=
  (adj''.comp adj').ofNatIsoRight e

/-- The unit of `AlgebraicGeometry.Space`'s composite left adjoint, componentwise. -/
theorem Adjunction.factorComposed_unit_app (adj' : L' ⊣ R) (adj'' : L'' ⊣ Q) (Z : E) :
    (Adjunction.factorComposed R Q T e adj' adj'').unit.app Z =
      adj''.unit.app Z ≫ Q.map (adj'.unit.app (L''.obj Z)) ≫
        e.hom.app (L'.obj (L''.obj Z)) := by
  simp [Adjunction.factorComposed, Adjunction.comp_unit_app]

/-- The unit of `L'' ⊣ Q` followed by `Q` of the counit comparison recovers `e.inv`: this is the
right triangle identity of `L'' ⊣ Q` read through the naturality of its unit. -/
theorem Adjunction.unit_comp_map_counit_comparison (adj'' : L'' ⊣ Q) (F : A) :
    adj''.unit.app (T.obj F) ≫
        Q.map (L''.map (e.inv.app F) ≫ adj''.counit.app (R.obj F)) =
      e.inv.app F := by
  have hnat : e.inv.app F ≫ adj''.unit.app (Q.obj (R.obj F)) =
      adj''.unit.app (T.obj F) ≫ Q.map (L''.map (e.inv.app F)) :=
    adj''.unit.naturality (e.inv.app F)
  rw [Functor.map_comp, ← Category.assoc, ← hnat, Category.assoc,
    adj''.right_triangle_components]
  exact Category.comp_id _

/-- **The comparison of left adjoints attached to a factorization is `L'` of a counit.**  Given a
left adjoint `L'' ⊣ Q` of the second factor, the comparison `T ⋙ L ⟶ R ⋙ L'` is the canonical
isomorphism `L ≅ L'' ⋙ L'` of left adjoints of `T`, followed by `L'` applied to the counit of
`L'' ⊣ Q` read through `e`. -/
theorem Adjunction.factorLeftAdjointComparison_app (adj : L ⊣ T) (adj' : L' ⊣ R)
    (adj'' : L'' ⊣ Q) (F : A) :
    (Adjunction.factorLeftAdjointComparison R Q T e adj adj').app F =
      (adj.leftAdjointUniq
          (Adjunction.factorComposed R Q T e adj' adj'')).hom.app (T.obj F) ≫
        L'.map (L''.map (e.inv.app F) ≫ adj''.counit.app (R.obj F)) := by
  apply (adj.homEquiv (T.obj F) ((R ⋙ L').obj F)).injective
  rw [Adjunction.homEquiv_factorLeftAdjointComparison_app, Adjunction.homEquiv_unit,
    Functor.map_comp, ← Category.assoc, Adjunction.unit_leftAdjointUniq_hom_app,
    Adjunction.factorComposed_unit_app, Adjunction.factorUnit_app]
  have hγ := Adjunction.unit_comp_map_counit_comparison R Q T e adj'' F
  have he : e.hom.app (L'.obj (L''.obj (T.obj F))) ≫
        T.map (L'.map (L''.map (e.inv.app F) ≫ adj''.counit.app (R.obj F))) =
      Q.map (R.map (L'.map (L''.map (e.inv.app F) ≫ adj''.counit.app (R.obj F)))) ≫
        e.hom.app (L'.obj (R.obj F)) :=
    (e.hom.naturality (L'.map (L''.map (e.inv.app F) ≫ adj''.counit.app (R.obj F)))).symm
  have hu : (L''.map (e.inv.app F) ≫ adj''.counit.app (R.obj F)) ≫
        adj'.unit.app (R.obj F) =
      adj'.unit.app (L''.obj (T.obj F)) ≫
        R.map (L'.map (L''.map (e.inv.app F) ≫ adj''.counit.app (R.obj F))) :=
    adj'.unit.naturality (L''.map (e.inv.app F) ≫ adj''.counit.app (R.obj F))
  symm
  calc (adj''.unit.app (T.obj F) ≫ Q.map (adj'.unit.app (L''.obj (T.obj F))) ≫
          e.hom.app (L'.obj (L''.obj (T.obj F)))) ≫
        T.map (L'.map (L''.map (e.inv.app F) ≫ adj''.counit.app (R.obj F)))
      = adj''.unit.app (T.obj F) ≫ Q.map (adj'.unit.app (L''.obj (T.obj F))) ≫
          e.hom.app (L'.obj (L''.obj (T.obj F))) ≫
            T.map (L'.map (L''.map (e.inv.app F) ≫
              adj''.counit.app (R.obj F))) := by
        simp only [Category.assoc]
    _ = adj''.unit.app (T.obj F) ≫ Q.map (adj'.unit.app (L''.obj (T.obj F))) ≫
          Q.map (R.map (L'.map (L''.map (e.inv.app F) ≫ adj''.counit.app (R.obj F)))) ≫
            e.hom.app (L'.obj (R.obj F)) := by
        rw [he]
    _ = adj''.unit.app (T.obj F) ≫
          Q.map (adj'.unit.app (L''.obj (T.obj F)) ≫
            R.map (L'.map (L''.map (e.inv.app F) ≫ adj''.counit.app (R.obj F)))) ≫
            e.hom.app (L'.obj (R.obj F)) := by
        rw [Q.map_comp]
        simp only [Category.assoc]
    _ = adj''.unit.app (T.obj F) ≫
          Q.map ((L''.map (e.inv.app F) ≫ adj''.counit.app (R.obj F)) ≫
            adj'.unit.app (R.obj F)) ≫ e.hom.app (L'.obj (R.obj F)) := by
        rw [hu]
    _ = (adj''.unit.app (T.obj F) ≫
          Q.map (L''.map (e.inv.app F) ≫ adj''.counit.app (R.obj F))) ≫
            Q.map (adj'.unit.app (R.obj F)) ≫ e.hom.app (L'.obj (R.obj F)) := by
        rw [Q.map_comp]
        simp only [Category.assoc]
    _ = e.inv.app F ≫ Q.map (adj'.unit.app (R.obj F)) ≫
          e.hom.app (L'.obj (R.obj F)) := by
        rw [hγ]

end CategoryTheory

end
