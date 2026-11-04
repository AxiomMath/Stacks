module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Diagonal

/-!
# Objects of a 2-fibre product whose comparison isomorphism descends

Fix a base category `𝒞`, categories fibred in groupoids `p𝒮 : 𝒮 ⥤ 𝒞`, `p𝒮' : 𝒮' ⥤ 𝒞` and a
1-morphism `G : 𝒮 ⥤ 𝒮'` over `𝒞`. Say that the comparison isomorphism of an object
`P = (x, y, φ)` of `𝒮 ×_{G, 𝒮', G} 𝒮` *descends* when `φ = G β` for some `β : x ⟶ y`. This is
the condition that `P` lies in the essential image of the diagonal `Δ_G`
(`CategoryTheory.TwoFibreProductOver.essImage_diagonal` and
`CategoryTheory.TwoFibreProductOver.exists_map_eq_iso_of_iso_diagonal`), so it only depends on
the isomorphism class of `P`; the point of this file is the stronger statement that it is
inherited along an *arbitrary* morphism `P ⟶ Q`, not just along an isomorphism.

## Main results

* `CategoryTheory.TwoFibreProductOver.exists_map_eq_iso_of_hom_to_diagonal`: a morphism from `P`
  to an object of the form `Δ_G z` makes the comparison isomorphism of `P` descend.
* `CategoryTheory.TwoFibreProductOver.exists_map_eq_iso_of_hom`: descending is inherited along
  any morphism `P ⟶ Q`.
* `CategoryTheory.TwoFibreProductOver.isHomLift_id_of_map_eq_iso`: the morphism `β` the
  comparison isomorphism descends to is vertical.

## Implementation notes

A morphism `u : P ⟶ Δ_G z` has two components `u.a : P.x ⟶ z` and `u.b : P.y ⟶ z` over the same
morphism `u.hbase` of `𝒞`, related by `G u.a = φ ≫ G u.b`. In a category fibred in groupoids
every morphism is strongly cartesian, so `u.b` has the universal property which fills in a
*vertical* `β : P.x ⟶ P.y` with `β ≫ u.b = u.a`; and then `G β` and `φ` are two vertical
morphisms with the same composite with the strongly cartesian `G u.b`, hence equal.

That a morphism `u : P ⟶ Q` into an object whose comparison isomorphism descends may be replaced
by one into a diagonal object is the content of
`CategoryTheory.TwoFibreProductOver.isoDiagonalOfMapEqIso`: the comparison morphism
`CategoryTheory.TwoFibreProductOver.homDiagonal` out of `Δ_G Q.x` has invertible components —
its middle one is an identity and its other one lies over the isomorphism `eqToHom Q.hx` — so it
is invertible, and `u` composed with its inverse lands in a diagonal object.
-/

@[expose] public section

namespace CategoryTheory.TwoFibreProductOver

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]
variable {𝒮 : Type u₂} [Category.{v₂} 𝒮]
variable {𝒮' : Type u₃} [Category.{v₃} 𝒮']
variable {p𝒮 : 𝒮 ⥤ 𝒞} {p𝒮' : 𝒮' ⥤ 𝒞} {G : 𝒮 ⥤ 𝒮'}

attribute [local instance_reducible] diagonal

/-- A morphism `β` whose image under `G` is the comparison isomorphism of an object `P` of the
2-fibre product is vertical over the base of `P`.

This is `CategoryTheory.TwoFibreProductOver.isHomLift_of_map_eq_iso` with the canonical
`eqToHom` replaced by the identity of `P.base`. -/
lemma isHomLift_id_of_map_eq_iso (hG : G ⋙ p𝒮' = p𝒮)
    (P : TwoFibreProductOver p𝒮 p𝒮 p𝒮' G G) (β : P.x ⟶ P.y) (hβ : G.map β = P.iso.hom) :
    p𝒮.IsHomLift (𝟙 P.base) β := by
  have _ := isHomLift_of_map_eq_iso hG P β hβ
  refine IsHomLift.of_fac' p𝒮 (𝟙 P.base) β P.hx P.hy ?_
  rw [IsHomLift.fac' p𝒮 (eqToHom P.hx) β]
  simp

/-- A morphism `β` whose image under `G` is the comparison isomorphism of an object of the
2-fibre product is invertible: it lies over the isomorphism `eqToHom P.hx`, and in a category
fibred in groupoids a morphism over an isomorphism is an isomorphism. -/
lemma isIso_of_map_eq_iso (h𝒮 : p𝒮.IsFiberedInGroupoids) (hG : G ⋙ p𝒮' = p𝒮)
    (P : TwoFibreProductOver p𝒮 p𝒮 p𝒮' G G) (β : P.x ⟶ P.y) (hβ : G.map β = P.iso.hom) :
    IsIso β := by
  have _ := isHomLift_of_map_eq_iso hG P β hβ
  have _ := h𝒮.isStronglyCartesian_homLift (eqToHom P.hx) β
  exact Functor.IsStronglyCartesian.isIso_of_base_isIso p𝒮 (eqToHom P.hx) β

/-- An object of the 2-fibre product whose comparison isomorphism descends is isomorphic to a
diagonal object, namely to `Δ_G P.x`. -/
noncomputable def isoDiagonalOfMapEqIso (h𝒮 : p𝒮.IsFiberedInGroupoids) (hG : G ⋙ p𝒮' = p𝒮)
    (P : TwoFibreProductOver p𝒮 p𝒮 p𝒮' G G) (β : P.x ⟶ P.y) (hβ : G.map β = P.iso.hom) :
    (diagonal hG).obj P.x ≅ P := by
  have _ := isIso_of_map_eq_iso h𝒮 hG P β hβ
  have _ : IsIso (homDiagonal hG P β hβ).hbase := by rw [homDiagonal_hbase]; infer_instance
  have _ : IsIso (homDiagonal hG P β hβ).a := by rw [homDiagonal_a]; infer_instance
  have _ : IsIso (homDiagonal hG P β hβ).b := by rw [homDiagonal_b]; infer_instance
  have _ := isIso_of_components (homDiagonal hG P β hβ)
  exact asIso (homDiagonal hG P β hβ)

/-- **A morphism to a diagonal object makes the comparison isomorphism descend.** If
`u : P ⟶ Δ_G z` is any morphism of the 2-fibre product then the comparison isomorphism of `P` is
`G β` for some `β : P.x ⟶ P.y`.

The second component `u.b` of `u` is strongly cartesian, because `p𝒮` is fibred in groupoids, so
it fills in a vertical `β` with `β ≫ u.b = u.a`; and `G u.b` is strongly cartesian in `𝒮'` for
the same reason, so the equality `G β ≫ G u.b = G u.a = P.iso.hom ≫ G u.b` of two vertical
morphisms may be cancelled. -/
lemma exists_map_eq_iso_of_hom_to_diagonal (h𝒮 : p𝒮.IsFiberedInGroupoids)
    (h𝒮' : p𝒮'.IsFiberedInGroupoids) (hG : G ⋙ p𝒮' = p𝒮)
    {P : TwoFibreProductOver p𝒮 p𝒮 p𝒮' G G} {z : 𝒮} (u : P ⟶ (diagonal hG).obj z) :
    ∃ β : P.x ⟶ P.y, G.map β = P.iso.hom := by
  have _ : p𝒮.IsHomLift u.hbase u.a := u.ha
  have _ : p𝒮.IsHomLift u.hbase u.b := u.hb
  have _ : p𝒮.IsStronglyCartesian u.hbase u.b := h𝒮.isStronglyCartesian_homLift _ _
  -- The vertical fill-in of `u.a` against `u.b`.
  set β := Functor.IsStronglyCartesian.map p𝒮 u.hbase u.b
    (Category.id_comp u.hbase).symm u.a
  have hfac : β ≫ u.b = u.a :=
    Functor.IsStronglyCartesian.fac p𝒮 u.hbase u.b (Category.id_comp u.hbase).symm u.a
  have _ : p𝒮.IsHomLift (𝟙 P.base) β :=
    Functor.IsStronglyCartesian.map_isHomLift p𝒮 u.hbase u.b
      (Category.id_comp u.hbase).symm u.a
  refine ⟨β, ?_⟩
  -- Cancel the strongly cartesian `G u.b`.
  have _ : p𝒮'.IsHomLift u.hbase (G.map u.b) := Functor.isHomLift_map_of_comp_eq hG u.hbase u.b
  have _ : p𝒮'.IsStronglyCartesian u.hbase (G.map u.b) := h𝒮'.isStronglyCartesian_homLift _ _
  have _ : p𝒮'.IsHomLift (𝟙 P.base) (G.map β) :=
    Functor.isHomLift_map_of_comp_eq hG (𝟙 P.base) β
  have _ : p𝒮'.IsHomLift (𝟙 P.base) P.iso.hom := P.vertical
  refine Functor.IsStronglyCartesian.ext p𝒮' u.hbase (G.map u.b) (𝟙 P.base) ?_
  rw [← G.map_comp, hfac]
  simpa using u.w

/-- **Descending the comparison isomorphism is inherited along any morphism.** If `u : P ⟶ Q` is
a morphism of the 2-fibre product and the comparison isomorphism of `Q` descends, then so does
that of `P`: the hypothesis identifies `Q` with a diagonal object, and
`CategoryTheory.TwoFibreProductOver.exists_map_eq_iso_of_hom_to_diagonal` applies to the
composite. -/
lemma exists_map_eq_iso_of_hom (h𝒮 : p𝒮.IsFiberedInGroupoids)
    (h𝒮' : p𝒮'.IsFiberedInGroupoids) (hG : G ⋙ p𝒮' = p𝒮)
    {P Q : TwoFibreProductOver p𝒮 p𝒮 p𝒮' G G} (u : P ⟶ Q)
    (hQ : ∃ γ : Q.x ⟶ Q.y, G.map γ = Q.iso.hom) :
    ∃ β : P.x ⟶ P.y, G.map β = P.iso.hom := by
  obtain ⟨γ, hγ⟩ := hQ
  exact exists_map_eq_iso_of_hom_to_diagonal h𝒮 h𝒮' hG
    (u ≫ (isoDiagonalOfMapEqIso h𝒮 hG Q γ hγ).inv)

end CategoryTheory.TwoFibreProductOver

end
