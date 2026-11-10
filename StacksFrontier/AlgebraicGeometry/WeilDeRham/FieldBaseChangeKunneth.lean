module

public import StacksFrontier.AlgebraicGeometry.WeilDeRham.FieldBaseChangeLinear

/-!
# The axioms (A1) and (A5) descend along a field extension (Lemma 0FVT)

In the situation of Lemma 0FVT of the Stacks Project — data (D0), (D1), (D2') `𝔇` over `k`, `F`
and `𝔇'` over `k'`, `F'`, compared by `B : Stacks.WeilDeRham.FieldBaseChangeData 𝔇 𝔇'` — the
proof of the lemma deduces (A1) and (A5) for `𝔇` from (A1) and (A5) for `𝔇'` "by the functorial
nature of the isomorphisms `H^*(X) ⊗_F F' → (H')^*(X_{k'})`" and linear algebra: an `F`-linear map
is an isomorphism if and only if its base change to `F'` is.

The geometric input is that base change along `Spec(k') → Spec(k)` preserves the relevant
diagrams: the empty scheme, binary coproducts (the category of schemes is extensive), the point
`Spec(k)` (whose base change is `Spec(k')`), and fibre products over `Spec(k)` (pasting of
cartesian squares).

## Main results

* `Stacks.WeilDeRham.isPullback_fieldBaseChange_of_isPullback`: the base change of a fibre product
  of `X` and `Y` over `Spec(k)` is a fibre product of `X_{k'}` and `Y_{k'}` over `Spec(k')`.
* `Stacks.WeilDeRham.FieldBaseChangeData.kunnethMap_fieldBaseChange`: the Künneth maps
  of (A5) for `𝔇` and `𝔇'` correspond under the comparison isomorphisms.

## References

* [Stacks Project, Tag 0FVT](https://stacks.math.columbia.edu/tag/0FVT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Stacks.WeilCohomology

universe u w w'

namespace Stacks.WeilDeRham

open Stacks.WeilCohomology.SmoothProjectiveScheme

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k']

/-! ### Base change of diagrams -/

/-- **The base change of a fibre product over `Spec(k)` is a fibre product over `Spec(k')`.** -/
theorem isPullback_fieldBaseChange_of_isPullback
    {X Y P : (SmoothProjectiveScheme k).FullSubcategory} {p : P ⟶ X} {q : P ⟶ Y}
    (hP : IsPullback ((toScheme k).map p) ((toScheme k).map q) X.obj.hom Y.obj.hom) :
    IsPullback ((toScheme k').map ((fieldBaseChange k k').map p))
      ((toScheme k').map ((fieldBaseChange k k').map q)) ((fieldBaseChange k k').obj X).obj.hom
      ((fieldBaseChange k k').obj Y).obj.hom := by
  have hs := IsPullback.paste_horiz (isPullback_fieldBaseChange_map (k' := k') q).flip hP
  rw [← fieldBaseChange_map_comp_proj, fieldBaseChangeProj_comp_hom] at hs
  exact IsPullback.of_right hs
    ((w ((fieldBaseChange k k').map p)).trans (w ((fieldBaseChange k k').map q)).symm)
    (isPullback_fieldBaseChangeProj X)

/-- The projection of `Spec(k)_{k'}` to `Spec(k')`, as a morphism of smooth projective schemes over
`k'`. -/
def pointFieldBaseChangeHom : (fieldBaseChange k k').obj (point k) ⟶ point k' :=
  homMk (pullback.snd (𝟙 _) (specStructure k k')) (Category.comp_id _)

/-- The structure morphism `Spec(k) ⟶ Spec(k)` of the point is an isomorphism. -/
instance isIso_point_hom : IsIso (point k).obj.hom :=
  inferInstanceAs (IsIso (𝟙 (Spec (.of k))))

/-- `Spec(k)_{k'} ⟶ Spec(k')` is an isomorphism of smooth projective schemes over `k'`. -/
instance isIso_pointFieldBaseChangeHom : IsIso (pointFieldBaseChangeHom (k := k) (k' := k')) := by
  have : IsIso ((toScheme k').map (pointFieldBaseChangeHom (k := k) (k' := k'))) :=
    inferInstanceAs (IsIso (pullback.snd (point k).obj.hom (specStructure k k')))
  exact isIso_of_reflects_iso _ (toScheme k')

/-! ### Descent of (A1) and (A5) -/

variable {F : Type w} [Field F] {F' : Type w'} [Field F'] [Algebra F F']
  {𝔇 : FirstChernClassData k F} {𝔇' : FirstChernClassData k' F'}

namespace FieldBaseChangeData

variable (B : FieldBaseChangeData 𝔇 𝔇')

/-- The comparison map `B.cohHom X` is multiplicative. -/
theorem cohHom_mul (X : (SmoothProjectiveScheme k).FullSubcategory) (a b : 𝔇.H X) :
    B.cohHom X (a * b) = B.cohHom X a * B.cohHom X b :=
  map_mul _ _ _

/-- **The Künneth maps correspond**: the base change of the Künneth map of (A5) for `𝔇` is the
Künneth map for `𝔇'` on the base-changed fibre product, read through the comparison isomorphisms
and `F' ⊗_F (V ⊗_F W) ≅ (F' ⊗_F V) ⊗_{F'} (F' ⊗_F W)`. -/
theorem kunnethMap_fieldBaseChange {X Y P : (SmoothProjectiveScheme k).FullSubcategory}
    (p : P ⟶ X) (q : P ⟶ Y) (v : 𝔇.H X ⊗[F] 𝔇.H Y) :
    TensorProduct.lift ((LinearMap.mul F' (𝔇'.H ((fieldBaseChange k k').obj P))).compl₁₂
        (𝔇'.pull ((fieldBaseChange k k').map p)).toLinearMap
        (𝔇'.pull ((fieldBaseChange k k').map q)).toLinearMap)
      ((TensorProduct.congr (B.cohEquiv X).toLinearEquiv (B.cohEquiv Y).toLinearEquiv)
        (AlgebraTensorModule.distribBaseChange F F' (𝔇.H X) (𝔇.H Y) (1 ⊗ₜ v))) =
    B.cohEquiv P (1 ⊗ₜ TensorProduct.lift ((LinearMap.mul F (𝔇.H P)).compl₁₂
      (𝔇.pull p).toLinearMap (𝔇.pull q).toLinearMap) v) := by
  induction v using TensorProduct.inductionOn with
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | tmul a b =>
    rw [AlgebraTensorModule.distribBaseChange_tmul]
    simp only [TensorProduct.congr_tmul, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply,
      AlgEquiv.toLinearEquiv_apply, AlgHom.toLinearMap_apply, LinearMap.mul_apply']
    rw [← cohHom_apply, ← cohHom_apply, ← cohHom_apply, ← B.cohHom_pull, ← B.cohHom_pull,
      ← cohHom_mul]

end FieldBaseChangeData

end Stacks.WeilDeRham

end
