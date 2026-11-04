module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.RelativeDiagonalFibre

/-!
# The fibre of the relative diagonal over a base fibred in sets

Fix a base category `𝒞`, categories `p : X ⥤ 𝒞` and `q : 𝒴 ⥤ 𝒞` over `𝒞`, and a 1-morphism
`F : X ⥤ 𝒴` strictly over `𝒞`. For a point `Y` of the 2-fibre product `X ×_𝒴 X` over a category
`𝒯` over `𝒞`, the fibre of the relative diagonal `Δ_F : X ⟶ X ×_𝒴 X` along `Y` is the category
of elements of `relVertHomPresheaf`: its sections over `a` are the vertical morphisms
`m : Y₁ a ⟶ Y₂ a` with `F m` equal to the comparison isomorphism `α a` of `Y` (Stacks 04XT).

When `q` is faithful — for instance when `𝒴` is the category fibred in sets `𝒮_Y` attached to an
algebraic space `Y` — two morphisms of `𝒴` lying over the same identity coincide, so the condition
`F m = α a` holds for every vertical `m`. The fibre of `Δ_F` along `Y` is then the presheaf of
*all* vertical morphisms `Y₁ ⟶ Y₂`, which is the fibre of the absolute diagonal of `X` along the
pair `(Y₁, Y₂)`. This is the step of the proof of Stacks 0DLY which reduces the diagonal of
`Coh_{X/B}` over `B` to the isomorphism sheaves `Isom(x, y)` of pairs of objects over a common
point of `B`.

## Main results

* `CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.map_eq_iso_hom_of_faithful`: over a
  faithful `q`, every vertical morphism satisfies the fibre condition.
* `CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.relVertHomPresheafIsoOfFaithful`:
  over a faithful `q`, `relVertHomPresheaf` is the presheaf of vertical morphisms.

## References

* [Stacks Project, Tag 04XT](https://stacks.math.columbia.edu/tag/04XT)
* [Stacks Project, Tag 0DLY](https://stacks.math.columbia.edu/tag/0DLY)
-/

@[expose] public section

open CategoryTheory

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

namespace CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre

open TwoFibreProductOver.DiagonalFibre

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {X : Type u₃} [Category.{v₃} X]
  {𝒯 : Type u₂} [Category.{v₂} 𝒯] {𝒴 : Type u₄} [Category.{v₄} 𝒴]
  {p : X ⥤ 𝒞} {p𝒯 : 𝒯 ⥤ 𝒞} {q : 𝒴 ⥤ 𝒞} {F : X ⥤ 𝒴}
  {Y : 𝒯 ⥤ RelProd p q F}

/-- **Over a faithful base, the fibre condition is automatic.** If `q` is faithful, then every
vertical morphism `m : Y₁ a ⟶ Y₂ a` of `X` has image under `F` the comparison isomorphism of
`Y` at `a`: both lie over the identity of `p𝒯 a`, so `q` identifies them. -/
lemma map_eq_iso_hom_of_faithful [q.Faithful] (hY : Y ⋙ RelProdP p q F = p𝒯)
    (hF : F ⋙ q = p) {a : 𝒯} (m : VertHom p p𝒯 (Y₁' Y) (Y₂' Y) a) :
    F.map m.1 = (Y.obj a).iso.hom := by
  have h₁ : q.IsHomLift (𝟙 (p𝒯.obj a)) (F.map m.1) := (VertHom.pushforward hF m).2
  have h₂ := isHomLift_vertical_iso hY a
  exact q.map_injective ((IsHomLift.fac' q (𝟙 (p𝒯.obj a)) (F.map m.1)).trans
    (IsHomLift.fac' q (𝟙 (p𝒯.obj a)) (Y.obj a).iso.hom).symm)

/-- **Over a faithful base, the fibre of the relative diagonal is the presheaf of vertical
morphisms.** If `q` is faithful, the presheaf `relVertHomPresheaf` of vertical morphisms
`Y₁ ⟶ Y₂` lying over the comparison isomorphism of `Y` is the presheaf of all vertical morphisms
`Y₁ ⟶ Y₂`, the fibre of the absolute diagonal of `X` along the pair of components of `Y`. -/
noncomputable def relVertHomPresheafIsoOfFaithful [q.Faithful]
    (hq : q.IsFiberedInGroupoids) (hp : p.IsFiberedInGroupoids)
    (hY : Y ⋙ RelProdP p q F = p𝒯) (hF : F ⋙ q = p) :
    relVertHomPresheaf hq hp hY hF ≅ VertHom.presheaf hp (h1' hY) (h2' hY) :=
  NatIso.ofComponents
    (fun _ => Equiv.toIso
      { toFun := fun m => m.1
        invFun := fun m => ⟨m, map_eq_iso_hom_of_faithful hY hF m⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl })
    (fun _ => rfl)

end CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre

end
