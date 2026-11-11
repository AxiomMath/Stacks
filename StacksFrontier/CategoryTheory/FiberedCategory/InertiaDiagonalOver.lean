module

public import StacksFrontier.CategoryTheory.FiberedCategory.InertiaDiagonal
public import StacksFrontier.CategoryTheory.FiberedCategory.InertiaSquare
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Diagonal
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverIso
import StacksFrontier.CategoryTheory.RelativeInertia
import StacksCore.Tactic.StacksAttribute

/-!
# The relative inertia as a 2-fibre product over the base (Stacks 034H)

Fix a category `C`, a category `p : S ⥤ C` over `C`, a category `p' : S' ⥤ C` over `C` and a
functor `F : S ⥤ S'` strictly over `C`. Stacks 034H (1) identifies the relative inertia
`I_{S/S'}` (`CategoryTheory.RelativeInertia F`, Stacks 034I) with the 2-fibre product
`S ×_{Δ, S ×_{S'} S, Δ} S` of the diagonal with itself, **in the (2,1)-category of categories
over `C`**. This file proves that statement, with the 2-fibre products of categories over `C`
of Stacks 02XQ (`CategoryTheory.TwoFibreProductOver`, whose comparison isomorphisms are
vertical) and the diagonal `CategoryTheory.TwoFibreProductOver.diagonal`.

## Main results

* `CategoryTheory.RelativeInertia.isEquivalenceOverToDiagonalFibreProductOver`:
  **Stacks 034H (1)**. The comparison 1-morphism `Φ`, `(x, α) ↦ (x, x, (α, id))`, its
  quasi-inverse `Ψ`, `(U, x, y, (ι, κ)) ↦ (x, κ⁻¹ ∘ ι)`, the unit (components `id_x`) and the
  counit (components `(id_x, κ)`) are all over `C` (`CategoryTheory.IsEquivalenceOver`).
* `CategoryTheory.RelativeInertia.isEquivalenceOver_toDiagonalFibreProductOver_and_isFibered`:
  **Stacks 034H**, both parts under the hypotheses of the source (`p` fibred and `F` a
  1-morphism of fibred categories over `C`); part (2) is
  `CategoryTheory.RelativeInertia.isFibered`. The fibredness of `p'` is not needed.

`CategoryTheory.RelativeInertia.diagonalPullbackEquivalence` is the analogous equivalence for the
2-fibre products in `Cat` (`Limits.CategoricalPullback`); it is not the source's statement.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} {S : Type u₂} {S' : Type u₃}
variable [Category.{v₁} C] [Category.{v₂} S] [Category.{v₃} S']

namespace RelativeInertia

variable {F : S ⥤ S'}

/-! ## Part (1) in the (2,1)-category of categories over `C`

The 2-fibre products of Stacks 034H (1) are those of Stacks 02XQ / 0040, in the
(2,1)-category of categories over `C`: `CategoryTheory.TwoFibreProductOver`, whose comparison
isomorphisms are **vertical**. For `F` strictly over `C` (`F ⋙ p' = p`), the diagonal is the
1-morphism `Δ = TwoFibreProductOver.diagonal hF : S ⥤ S ×_{F, S', F} S` over `C`, and the target
of the comparison is the iterated 2-fibre product `S ×_{Δ, S ×_{S'} S, Δ} S` over `C`. An object
of it is `(U, x, y, (ι, κ))` with `x`, `y` over `U` and `(ι, κ) : Δ x ≅ Δ y` an isomorphism of
`S ×_{S'} S` lying over `𝟙 U`; so `ι, κ : x ≅ y` are vertical isomorphisms with `F ι = F κ`. -/

section OverC

variable {p : S ⥤ C} {p' : S' ⥤ C}

attribute [local implicit_reducible] TwoFibreProductOver.diagonal TwoFibreProductOver.fst
  TwoFibreProductOver.structureFunctor RelativeInertia.π

/-- The 2-fibre product `S ×_{Δ, S ×_{S'} S, Δ} S` of the diagonal with itself, in the
(2,1)-category of categories over `C` (Stacks 02XQ), for `F : S ⥤ S'` strictly over `C`. -/
abbrev DiagonalFibreProductOver (hF : F ⋙ p' = p) :=
  TwoFibreProductOver p p (TwoFibreProductOver.structureFunctor p p p' F F)
    (TwoFibreProductOver.diagonal hF) (TwoFibreProductOver.diagonal hF)

/-- The structure functor `S ×_{Δ, S ×_{S'} S, Δ} S ⥤ C`, `(U, x, y, (ι, κ)) ↦ U`. -/
abbrev diagonalFibreProductOverProj (hF : F ⋙ p' = p) : DiagonalFibreProductOver hF ⥤ C :=
  TwoFibreProductOver.structureFunctor p p (TwoFibreProductOver.structureFunctor p p p' F F)
    (TwoFibreProductOver.diagonal hF) (TwoFibreProductOver.diagonal hF)

/-- For `F` strictly over `C`, the inverse `α⁻¹` of the automorphism of an object `(x, α)` of
the relative inertia also projects to the identity of `p x`. -/
theorem struct_map_auto_inv_eq_id (hF : F ⋙ p' = p) (t : RelativeInertia F) :
    p.map t.auto.asIso.inv = 𝟙 (p.obj t.obj) := by
  subst hF
  simp [t.cond_inv]

/-- The automorphism `α` of an object `(x, α)` of the inertia is vertical over `p x`. -/
lemma isHomLift_auto_hom (hF : F ⋙ p' = p) (t : RelativeInertia F) :
    p.IsHomLift (𝟙 (p.obj t.obj)) t.auto.asIso.hom :=
  IsHomLift.of_fac' p _ _ rfl rfl (by rw [struct_map_auto_eq_id p p' hF t]; simp)

/-- The inverse `α⁻¹` of the automorphism of an object `(x, α)` of the inertia is vertical over
`p x`. -/
lemma isHomLift_auto_inv (hF : F ⋙ p' = p) (t : RelativeInertia F) :
    p.IsHomLift (𝟙 (p.obj t.obj)) t.auto.asIso.inv :=
  IsHomLift.of_fac' p _ _ rfl rfl (by rw [struct_map_auto_inv_eq_id hF t]; simp)

/-- The vertical isomorphism `(α, id) : Δ x ≅ Δ x` of `S ×_{S'} S` attached to an object
`(x, α)` of the relative inertia. -/
@[implicit_reducible]
def toDiagonalFibreProductOverObjIso (hF : F ⋙ p' = p) (t : RelativeInertia F) :
    (TwoFibreProductOver.diagonal hF).obj t.obj ≅ (TwoFibreProductOver.diagonal hF).obj t.obj where
  hom :=
    { hbase := 𝟙 (p.obj t.obj)
      a := t.auto.asIso.hom
      b := 𝟙 t.obj
      ha := isHomLift_auto_hom hF t
      hb := IsHomLift.id rfl
      w := by simp [t.cond] }
  inv :=
    { hbase := 𝟙 (p.obj t.obj)
      a := t.auto.asIso.inv
      b := 𝟙 t.obj
      ha := isHomLift_auto_inv hF t
      hb := IsHomLift.id rfl
      w := by simp [t.cond_inv] }
  hom_inv_id := TwoFibreProductOver.Hom.ext' t.auto.asIso.hom_inv_id (Category.comp_id _)
  inv_hom_id := TwoFibreProductOver.Hom.ext' t.auto.asIso.inv_hom_id (Category.comp_id _)

/-- The object `Φ (x, α) = (p x, x, x, (α, id))` of `S ×_{Δ, S ×_{S'} S, Δ} S`. -/
@[implicit_reducible]
def toDiagonalFibreProductOverObj (hF : F ⋙ p' = p) (t : RelativeInertia F) :
    DiagonalFibreProductOver hF where
  base := p.obj t.obj
  x := t.obj
  y := t.obj
  hx := rfl
  hy := rfl
  iso := toDiagonalFibreProductOverObjIso hF t
  vertical := IsHomLift.of_fac' _ _ _ rfl rfl (by
    change 𝟙 (p.obj t.obj) = _
    simp
    rfl)

/-- The comparison 1-morphism `Φ : I_{S/S'} ⥤ S ×_{Δ, S ×_{S'} S, Δ} S` over `C` of
Stacks 034H (1): `(x, α) ↦ (x, x, (α, id))` on objects and `φ ↦ (φ, φ)` on morphisms. -/
@[implicit_reducible]
def toDiagonalFibreProductOver (hF : F ⋙ p' = p) :
    RelativeInertia F ⥤ DiagonalFibreProductOver hF where
  obj t := toDiagonalFibreProductOverObj hF t
  map {s t} f :=
    { hbase := p.map f.hom
      a := f.hom
      b := f.hom
      ha := inferInstanceAs (p.IsHomLift (p.map f.hom) f.hom)
      hb := inferInstanceAs (p.IsHomLift (p.map f.hom) f.hom)
      w := TwoFibreProductOver.Hom.ext' f.comm
        (by change f.hom ≫ 𝟙 t.obj = 𝟙 s.obj ≫ f.hom; simp) }
  map_id _ := TwoFibreProductOver.Hom.ext' rfl rfl
  map_comp _ _ := TwoFibreProductOver.Hom.ext' rfl rfl

/-- The second components of mutually inverse isomorphisms of `S ×_{S'} S` compose to the
identity, in one order. -/
lemma hom_b_comp_inv_b {P Q : TwoFibreProductOver p p p' F F} (e : P ≅ Q) :
    e.hom.b ≫ e.inv.b = 𝟙 P.y := by
  rw [← TwoFibreProductOver.comp_b, e.hom_inv_id, TwoFibreProductOver.id_b]

/-- The second components of mutually inverse isomorphisms of `S ×_{S'} S` compose to the
identity, in the other order. -/
lemma inv_b_comp_hom_b {P Q : TwoFibreProductOver p p p' F F} (e : P ≅ Q) :
    e.inv.b ≫ e.hom.b = 𝟙 Q.y := by
  rw [← TwoFibreProductOver.comp_b, e.inv_hom_id, TwoFibreProductOver.id_b]

/-- The object `Ψ (U, x, y, (ι, κ)) = (x, κ⁻¹ ∘ ι)` of the relative inertia. Its automorphism
satisfies `F (κ⁻¹ ∘ ι) = id` because `F ι = F κ`. -/
@[implicit_reducible]
def fromDiagonalFibreProductOverObj (hF : F ⋙ p' = p) (P : DiagonalFibreProductOver hF) :
    RelativeInertia F where
  obj := P.x
  auto := .of
    { hom := P.iso.hom.a ≫ P.iso.inv.b
      inv := P.iso.hom.b ≫ P.iso.inv.a
      hom_inv_id := by
        rw [Category.assoc, ← Category.assoc P.iso.inv.b, inv_b_comp_hom_b, Category.id_comp,
          ← TwoFibreProductOver.comp_a, P.iso.hom_inv_id, TwoFibreProductOver.id_a]
        rfl
      inv_hom_id := by
        rw [Category.assoc, ← Category.assoc P.iso.inv.a, ← TwoFibreProductOver.comp_a,
          P.iso.inv_hom_id, TwoFibreProductOver.id_a, Category.id_comp, hom_b_comp_inv_b]
        rfl }
  cond := by
    change F.map (P.iso.hom.a ≫ P.iso.inv.b) = _
    rw [F.map_comp, TwoFibreProductOver.map_eq_of_hom_diagonal hF P.iso.hom, ← F.map_comp,
      hom_b_comp_inv_b, F.map_id]
    rfl

/-- The quasi-inverse `Ψ : S ×_{Δ, S ×_{S'} S, Δ} S ⥤ I_{S/S'}` of Stacks 034H (1):
`(U, x, y, (ι, κ)) ↦ (x, κ⁻¹ ∘ ι)` on objects and `(φ, φ') ↦ φ` on morphisms. -/
@[implicit_reducible]
def fromDiagonalFibreProductOver (hF : F ⋙ p' = p) :
    DiagonalFibreProductOver hF ⥤ RelativeInertia F where
  obj P := fromDiagonalFibreProductOverObj hF P
  map {P Q} f :=
    { hom := f.a
      comm := by
        have hwa : f.a ≫ Q.iso.hom.a = P.iso.hom.a ≫ f.b := congrArg TwoFibreProductOver.Hom.a f.w
        have hwb : f.a ≫ Q.iso.hom.b = P.iso.hom.b ≫ f.b := congrArg TwoFibreProductOver.Hom.b f.w
        have hb' : P.iso.inv.b ≫ f.a = f.b ≫ Q.iso.inv.b := by
          calc P.iso.inv.b ≫ f.a = P.iso.inv.b ≫ (f.a ≫ Q.iso.hom.b) ≫ Q.iso.inv.b := by
                rw [Category.assoc, hom_b_comp_inv_b]
                exact congrArg (P.iso.inv.b ≫ ·) (Category.comp_id f.a).symm
            _ = (P.iso.inv.b ≫ P.iso.hom.b) ≫ f.b ≫ Q.iso.inv.b := by
                rw [hwb]; simp only [Category.assoc]
            _ = f.b ≫ Q.iso.inv.b := by rw [inv_b_comp_hom_b, Category.id_comp]
        change f.a ≫ Q.iso.hom.a ≫ Q.iso.inv.b = (P.iso.hom.a ≫ P.iso.inv.b) ≫ f.a
        rw [← Category.assoc, hwa, Category.assoc, Category.assoc, hb'] }
  map_id _ := RelativeInertiaHom.ext rfl
  map_comp _ _ := RelativeInertiaHom.ext rfl

/-- The unit `𝟭 ≅ Φ ⋙ Ψ`: `Ψ (Φ (x, α)) = (x, α ∘ id)`, and the component is `id_x`. -/
def diagonalFibreProductOverUnitIso (hF : F ⋙ p' = p) :
    𝟭 (RelativeInertia F) ≅ toDiagonalFibreProductOver hF ⋙ fromDiagonalFibreProductOver hF :=
  NatIso.ofComponents
    (fun t =>
      { hom := ⟨𝟙 t.obj, by
          change 𝟙 t.obj ≫ t.auto.asIso.hom ≫ 𝟙 t.obj = t.auto.asIso.hom ≫ 𝟙 t.obj; simp⟩
        inv := ⟨𝟙 t.obj, by
          change 𝟙 t.obj ≫ t.auto.asIso.hom = (t.auto.asIso.hom ≫ 𝟙 t.obj) ≫ 𝟙 t.obj; simp⟩
        hom_inv_id := RelativeInertiaHom.ext (Category.comp_id _)
        inv_hom_id := RelativeInertiaHom.ext (Category.comp_id _) })
    (fun {s t} f => RelativeInertiaHom.ext (by
      change f.hom ≫ 𝟙 t.obj = 𝟙 s.obj ≫ f.hom; simp))

/-- The component at `(U, x, y, (ι, κ))` of the counit `Ψ ⋙ Φ ⟶ 𝟭`: the morphism
`(id_x, κ) : (p x, x, x, (κ⁻¹ ∘ ι, id)) ⟶ (U, x, y, (ι, κ))`, over the identification
`p x = U`. -/
def diagonalFibreProductOverCounitHom (hF : F ⋙ p' = p) (P : DiagonalFibreProductOver hF) :
    toDiagonalFibreProductOverObj hF (fromDiagonalFibreProductOverObj hF P) ⟶ P where
  hbase := eqToHom P.hx
  a := 𝟙 P.x
  b := P.iso.hom.b
  ha := IsHomLift.of_fac' p _ _ rfl P.hx (by
    simp only [Category.id_comp, eqToHom_trans, eqToHom_refl]
    exact p.map_id _)
  hb := by
    have : p.IsHomLift (𝟙 P.base) P.iso.hom.b :=
      TwoFibreProductOver.isHomLift_b P.iso.hom (𝟙 P.base) P.vertical
    exact IsHomLift.of_fac' p _ _ rfl P.hy (by rw [IsHomLift.fac' p (𝟙 P.base) P.iso.hom.b]; simp)
  w := TwoFibreProductOver.Hom.ext'
    (by
      change 𝟙 P.x ≫ P.iso.hom.a = (P.iso.hom.a ≫ P.iso.inv.b) ≫ P.iso.hom.b
      rw [Category.assoc, inv_b_comp_hom_b, Category.id_comp]
      exact (Category.comp_id _).symm)
    (by change 𝟙 P.x ≫ P.iso.hom.b = 𝟙 P.x ≫ P.iso.hom.b; rfl)

/-- The component `(id_x, κ)` of the counit is an isomorphism. -/
lemma isIso_diagonalFibreProductOverCounitHom (hF : F ⋙ p' = p) (P : DiagonalFibreProductOver hF) :
    IsIso (diagonalFibreProductOverCounitHom hF P) := by
  have : IsIso (diagonalFibreProductOverCounitHom hF P).b :=
    ⟨P.iso.inv.b, hom_b_comp_inv_b P.iso, inv_b_comp_hom_b P.iso⟩
  have : IsIso (diagonalFibreProductOverCounitHom hF P).a :=
    inferInstanceAs (IsIso (𝟙 P.x))
  have : IsIso (diagonalFibreProductOverCounitHom hF P).hbase :=
    inferInstanceAs (IsIso (eqToHom P.hx))
  exact TwoFibreProductOver.isIso_of_components _

/-- The counit `Ψ ⋙ Φ ≅ 𝟭`, with component `(id_x, κ)` at `(U, x, y, (ι, κ))`. -/
noncomputable def diagonalFibreProductOverCounitIso (hF : F ⋙ p' = p) :
    fromDiagonalFibreProductOver hF ⋙ toDiagonalFibreProductOver hF ≅
      𝟭 (DiagonalFibreProductOver hF) :=
  NatIso.ofComponents
    (fun P =>
      haveI := isIso_diagonalFibreProductOverCounitHom hF P
      asIso (diagonalFibreProductOverCounitHom hF P))
    (fun {P Q} f => TwoFibreProductOver.Hom.ext'
      (by change f.a ≫ 𝟙 Q.x = 𝟙 P.x ≫ f.a; simp)
      (by
        change f.a ≫ Q.iso.hom.b = P.iso.hom.b ≫ f.b
        exact congrArg TwoFibreProductOver.Hom.b f.w))

/-- **Stacks 034H (1), the equivalence over `C`.** For `F : S ⥤ S'` strictly over `C`, the
comparison 1-morphism `Φ : I_{S/S'} ⥤ S ×_{Δ, S ×_{S'} S, Δ} S`, `(x, α) ↦ (x, x, (α, id))`, is
an equivalence in the (2,1)-category of categories over `C`: `Φ` and its quasi-inverse `Ψ`,
`(U, x, y, (ι, κ)) ↦ (x, κ⁻¹ ∘ ι)`, are functors over `C`, and every component of the unit
(`id_x`) and of the counit (`(id_x, κ)`) lies over an identity of `C`. The 2-fibre products are
those of categories over `C` (Stacks 02XQ, `CategoryTheory.TwoFibreProductOver`), with vertical
comparison isomorphisms. -/
@[stacks 034H "(1)"]
noncomputable def isEquivalenceOverToDiagonalFibreProductOver (hF : F ⋙ p' = p) :
    IsEquivalenceOver (RelativeInertia.π F ⋙ p) (diagonalFibreProductOverProj hF)
      (toDiagonalFibreProductOver hF) where
  inverse := fromDiagonalFibreProductOver hF
  unitIso := diagonalFibreProductOverUnitIso hF
  counitIso := diagonalFibreProductOverCounitIso hF
  functor_unitIso_comp _ := TwoFibreProductOver.Hom.ext' (Category.id_comp _) (Category.id_comp _)
  functor_over := CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ f => by
    change p.map f.hom = _
    simp)
  inverse_over := CategoryTheory.Functor.ext (fun P => P.hx) (fun P Q f => by
    have := f.ha
    exact IsHomLift.fac' p f.hbase f.a)
  unit_over t := by
    change p.map (𝟙 t.obj) = _
    simp
  counit_over P := by
    change (diagonalFibreProductOverCounitHom hF P).hbase = _
    rfl

/-- **Stacks 034H.** Let `p : S ⥤ C` be a fibred category, let `p' : S' ⥤ C` be a category over
`C` and let `F : S ⥤ S'` be a 1-morphism of fibred categories over `C`. Then
1. the comparison 1-morphism `Φ : I_{S/S'} ⥤ S ×_{Δ, S ×_{S'} S, Δ} S` is an equivalence in the
   (2,1)-category of categories over `C`, the 2-fibre products being those of categories over
   `C` (`isEquivalenceOverToDiagonalFibreProductOver`), and
2. `I_{S/S'}`, with structure functor `(x, α) ↦ p x`, is a fibred category over `C`
   (`CategoryTheory.RelativeInertia.isFibered`).

The source also assumes `p'` fibred; neither part uses it. -/
@[stacks 034H]
theorem isEquivalenceOver_toDiagonalFibreProductOver_and_isFibered (hp : p.IsFibered)
    (hF : p.IsFibredOneMorphism p' F) :
    Nonempty (IsEquivalenceOver (RelativeInertia.π F ⋙ p)
      (diagonalFibreProductOverProj hF.comp_eq) (toDiagonalFibreProductOver hF.comp_eq)) ∧
      (RelativeInertia.π F ⋙ p).IsFibered :=
  ⟨⟨isEquivalenceOverToDiagonalFibreProductOver hF.comp_eq⟩,
    RelativeInertia.isFibered F p p' hp hF⟩

end OverC

end RelativeInertia

end CategoryTheory
