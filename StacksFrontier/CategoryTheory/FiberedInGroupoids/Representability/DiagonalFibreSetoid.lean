module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.DiagonalFibre

/-!
# The fibre of the diagonal is fibred in setoids

Let `p : 𝒳 ⥤ 𝒞` be fibred in groupoids, let `𝒯` be a category over `𝒞` and let
`Y : 𝒯 ⥤ 𝒳 ×_𝒞 𝒳` be a 1-morphism over `𝒞`, with components `Y₁` and `Y₂`. The first projection
of the 2-fibre product `𝒯 ×_{Y, 𝒳 ×_𝒞 𝒳, Δ} 𝒳 ⟶ 𝒯` is equivalent to the category of elements of
the presheaf of vertical morphisms `Y₁ ⟶ Y₂`
(`CategoryTheory.TwoFibreProductOver.DiagonalFibre.equivalenceOver`). This file records two
consequences of this description for the 2-fibre product as a category over `𝒯`.

The first projection is faithful: a morphism of the 2-fibre product is determined by its
component in `𝒯`. And a morphism `h : A.x ⟶ B.x` of `𝒯` lifts to a morphism `A ⟶ B` exactly when
the vertical morphisms `sectOf A` and `sectOf B` named by `A` and `B` are compatible along `h`.

## Main results

* `CategoryTheory.TwoFibreProductOver.DiagonalFibre.faithful_fst`: the first projection is
  faithful, so the 2-fibre product is fibred in setoids over `𝒯`.
* `CategoryTheory.TwoFibreProductOver.DiagonalFibre.exists_hom_of_sectOf`: a morphism of `𝒯`
  along which the two named vertical morphisms are compatible lifts to the 2-fibre product.
* `CategoryTheory.TwoFibreProductOver.DiagonalFibre.exists_hom_iff_sectOf`: a morphism of `𝒯`
  lifts to the 2-fibre product if and only if the two named vertical morphisms are compatible
  along it.
-/

@[expose] public section

open CategoryTheory

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory.TwoFibreProductOver.DiagonalFibre

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {X : Type u₃} [Category.{v₃} X]
  {𝒯 : Type u₂} [Category.{v₂} 𝒯]
variable {p : X ⥤ 𝒞} {p𝒯 : 𝒯 ⥤ 𝒞} {Y : 𝒯 ⥤ Prod' p}

attribute [local implicit_reducible] _root_.CategoryTheory.TwoFibreProductOver.fst
  _root_.CategoryTheory.TwoFibreProductOver.snd
  _root_.CategoryTheory.TwoFibreProductOver.diagonal

/-- **The fibre of the diagonal is fibred in setoids.** The first projection of
`𝒯 ×_{Y, 𝒳 ×_𝒞 𝒳, Δ} 𝒳` is faithful: the comparison square of a morphism determines its
component in `𝒳` from its component in `𝒯`. -/
theorem faithful_fst : (fst p𝒯 p (ProdP p) Y (Diag p)).Faithful where
  map_injective {A B} u u' h := by
    change u.a = u'.a at h
    have hw : A.iso.hom ≫ (Diag p).map u.b = A.iso.hom ≫ (Diag p).map u'.b := by
      rw [← u.w, ← u'.w, h]
    have hb : (Diag p).map u.b = (Diag p).map u'.b := (cancel_epi _).mp hw
    exact Hom.ext' h (by simpa using congrArg Hom.a hb)

variable (hp : p.IsFiberedInGroupoids) (hY : Y ⋙ ProdP p = p𝒯)

include hp hY in
/-- **Morphisms of the fibre of the diagonal.** A morphism `h : A.x ⟶ B.x` of `𝒯` along which the
vertical morphisms named by `A` and `B` are compatible, `sectOf A ≫ Y₂ h = Y₁ h ≫ sectOf B`, is
the `𝒯`-component of a morphism `A ⟶ B` of the 2-fibre product. -/
theorem exists_hom_of_sectOf {A B : TwoFibreProductOver p𝒯 p (ProdP p) Y (Diag p)}
    (h : A.x ⟶ B.x) (hh : sectOf A ≫ (Y₂' Y).map h = (Y₁' Y).map h ≫ sectOf B) :
    ∃ u : A ⟶ B, u.a = h := by
  let e : (toElements hp hY).obj A ⟶ (toElements hp hY).obj B :=
    ⟨h, Discrete.eqToHom
      (VertHom.restrict_uniq hp (h1' hY) (h2' hY) h ⟨sectOf B, isHomLift_sectOf hY B⟩
        ⟨sectOf A, isHomLift_sectOf hY A⟩ hh)⟩
  refine ⟨(unitIso hp hY).hom.app A ≫ (ofElements hp hY).map e ≫ (unitIso hp hY).inv.app B,
    ?_⟩
  show 𝟙 A.x ≫ h ≫ 𝟙 B.x = h
  rw [Category.id_comp, Category.comp_id]

include hp hY in
/-- **Morphisms of the fibre of the diagonal, characterized.** A morphism `h : A.x ⟶ B.x` of `𝒯`
lifts to a morphism `A ⟶ B` of the 2-fibre product if and only if the vertical morphisms named by
`A` and `B` are compatible along `h`. -/
theorem exists_hom_iff_sectOf {A B : TwoFibreProductOver p𝒯 p (ProdP p) Y (Diag p)}
    (h : A.x ⟶ B.x) :
    (∃ u : A ⟶ B, u.a = h) ↔ sectOf A ≫ (Y₂' Y).map h = (Y₁' Y).map h ≫ sectOf B := by
  refine ⟨?_, exists_hom_of_sectOf hp hY h⟩
  rintro ⟨u, rfl⟩
  exact sectOf_naturality u

end CategoryTheory.TwoFibreProductOver.DiagonalFibre

end
