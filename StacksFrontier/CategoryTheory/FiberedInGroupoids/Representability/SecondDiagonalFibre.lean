module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.RelativeDiagonalFibre
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.SecondDiagonal

/-!
# The fibre of the second diagonal is the locus where an automorphism is the identity

Fix a base category `𝒞`, categories `p𝒮 : 𝒮 ⥤ 𝒞` and `p𝒮' : 𝒮' ⥤ 𝒞` over `𝒞` and a 1-morphism
`G : 𝒮 ⥤ 𝒮'` over `𝒞`. Write `Δ_G : 𝒮 ⥤ 𝒮 ×_{𝒮'} 𝒮` for the diagonal of `G` and

`Δ_{Δ_G} : 𝒮 ⥤ 𝒮 ×_{Δ_G, 𝒮 ×_{𝒮'} 𝒮, Δ_G} 𝒮`

for the second diagonal. `CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre` computes the
2-fibre product of a point `Y : 𝒯 ⥤ 𝒮 ×_{𝒮'} 𝒮` with a relative diagonal as the category of
elements of the presheaf of vertical morphisms lying over the comparison isomorphism of `Y`.
This file evaluates that presheaf for the second diagonal, i.e. for the relative diagonal of
`Δ_G` itself.

An object `T` of the target `𝒮 ×_{Δ_G, 𝒮 ×_{𝒮'} 𝒮, Δ_G} 𝒮` of the second diagonal carries a
comparison isomorphism `φ : Δ_G T.x ≅ Δ_G T.y` with two components `φ₁`, `φ₂ : T.x ≅ T.y`
(`CategoryTheory.TwoFibreProductOver.isoFst` and `.isoSnd`), and the automorphism
`φ₁ ∘ φ₂⁻¹` of `T.x` it names is
`CategoryTheory.TwoFibreProductOver.diagonalAut` — under the identification of that target with
the relative inertia, the automorphism component of `T`. For a point `Y : 𝒯 ⥤ 𝒮 ×_{Δ_G} 𝒮` the
presheaf of the relative diagonal has at most one section over any object `a` of `𝒯`, namely
`φ₁`, and it has one exactly when the automorphism of `Y a` is the identity.

So the presheaf is a subobject of the terminal presheaf, cut out by the condition
"`diagonalAut (Y a) = 𝟙`". Together with the relative diagonal criterion this is the sentence
with which the proof of **Stacks 07WG** reads condition (1): given a scheme `V`, an object `x` of
`𝒳` over `V` and a morphism `α : x ⟶ x` of `𝒳_V`, condition (1) says that the condition
`α = 𝟙 x` defines an algebraic space over `V`.

## Main results

* `CategoryTheory.TwoFibreProductOver.SecondDiagonalFibre.map_isoFst_hom`: the first component of
  the comparison isomorphism of an object of the second 2-fibre product lies over the canonical
  identification of the bases, the companion of
  `CategoryTheory.TwoFibreProductOver.map_isoSnd_hom`.
* `CategoryTheory.TwoFibreProductOver.SecondDiagonalFibre.val_eq_isoFst_hom` and
  `.val_eq_isoSnd_hom`: a section of the presheaf of the second diagonal is both components of
  the comparison isomorphism, so the two components agree.
* `CategoryTheory.TwoFibreProductOver.SecondDiagonalFibre.subsingleton_relVertHom`: the presheaf
  has at most one section over each object.
* `CategoryTheory.TwoFibreProductOver.SecondDiagonalFibre.nonempty_relVertHom_iff`: it has a
  section over `a` exactly when the automorphism attached to `Y a` is the identity.

## Implementation notes

The condition is stated as `(diagonalAut hG (Y.obj a)).asIso.hom = 𝟙 _` rather than as an equality of
isomorphisms, because that is the form in which a consumer meets it: the automorphism arrives as
the automorphism component of an object of the relative inertia, and the predicate it has to
test is an equation between morphisms.

Nothing here assumes `p𝒮` fibred in groupoids: the single possible section is the first
component of a comparison isomorphism, which is given, so no fill-in has to be produced. The
hypothesis that `Y` is a 1-morphism over `𝒞` is needed only to know which identity of `𝒞` the
section is vertical over.

## References

* [Stacks Project, Tag 07WG](https://stacks.math.columbia.edu/tag/07WG)
* [Stacks Project, Tag 04XT](https://stacks.math.columbia.edu/tag/04XT)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.TwoFibreProductOver

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒯 : Type u₂} [Category.{v₂} 𝒯]
  {𝒮 : Type u₃} [Category.{v₃} 𝒮] {𝒮' : Type u₄} [Category.{v₄} 𝒮']
  {p𝒮 : 𝒮 ⥤ 𝒞} {p𝒮' : 𝒮' ⥤ 𝒞} {G : 𝒮 ⥤ 𝒮'} {p𝒯 : 𝒯 ⥤ 𝒞}

attribute [local instance_reducible] diagonal

-- The two components `Y₁' Y`, `Y₂' Y` of a point of the second 2-fibre product are `Y ⋙ fst`
-- and `Y ⋙ snd`, so `(Y₁' Y).obj a` is `(Y.obj a).x` only after `fst` is unfolded. Implicit
-- arguments are checked at `implicit` transparency, which unfolds only `[reducible]`,
-- `[instance_reducible]` and `[implicit_reducible]` definitions, and these two are plain `def`s;
-- without this the construction below is rejected as not type-correct even though both spellings
-- print identically. `Functor.comp` already carries the attribute upstream.
attribute [local implicit_reducible] fst snd

namespace SecondDiagonalFibre

/-- The first component of the comparison isomorphism of an object of the second 2-fibre product
lies over the canonical identification of the bases of its two components. This is the companion
of `CategoryTheory.TwoFibreProductOver.map_isoSnd_hom`. -/
lemma map_isoFst_hom (hG : G ⋙ p𝒮' = p𝒮) (T : DiagonalFibreProduct hG) :
    p𝒮.map (isoFst hG T).hom = eqToHom T.hx ≫ eqToHom T.hy.symm := by
  have := T.iso.hom.ha
  rw [isoFst_hom, IsHomLift.fac' p𝒮 T.iso.hom.hbase T.iso.hom.a]
  simp only [iso_hom_hbase hG T, eqToHom_trans]

section

variable (hG : G ⋙ p𝒮' = p𝒮) (Y : 𝒯 ⥤ DiagonalFibreProduct hG) (a : 𝒯)

/-- A section over `a` of the presheaf attached to the second diagonal is the first component of
the comparison isomorphism of `Y a`. -/
lemma val_eq_isoFst_hom (m : RelativeDiagonalFibre.RelVertHom p𝒯 Y a) :
    m.1.1 = (isoFst hG (Y.obj a)).hom := by
  simpa only [diagonal_map_a, isoFst_hom] using congrArg Hom.a m.2

/-- A section over `a` of the presheaf attached to the second diagonal is also the second
component of the comparison isomorphism of `Y a`. -/
lemma val_eq_isoSnd_hom (m : RelativeDiagonalFibre.RelVertHom p𝒯 Y a) :
    m.1.1 = (isoSnd hG (Y.obj a)).hom := by
  simpa only [diagonal_map_b, isoSnd_hom] using congrArg Hom.b m.2

/-- The presheaf attached to the second diagonal has at most one section over each object: a
section is forced to be the first component of the comparison isomorphism. -/
lemma subsingleton_relVertHom :
    Subsingleton (RelativeDiagonalFibre.RelVertHom p𝒯 Y a) :=
  ⟨fun m n => RelativeDiagonalFibre.RelVertHom.ext
    ((val_eq_isoFst_hom hG Y a m).trans (val_eq_isoFst_hom hG Y a n).symm)⟩

/-- **The fibre of the second diagonal is the locus where the automorphism is the identity.** The
presheaf attached to the second diagonal has a section over `a` exactly when the automorphism
`φ₁ ∘ φ₂⁻¹` of `(Y a).x` named by the comparison isomorphism of `Y a` is the identity. Under the
identification of the target of the second diagonal with the relative inertia, this is the
condition that the automorphism component of `Y a` is trivial. -/
theorem nonempty_relVertHom_iff
    (hY : Y ⋙ RelativeDiagonalFibre.RelProdP p𝒮 (structureFunctor p𝒮 p𝒮 p𝒮' G G)
      (diagonal hG) = p𝒯) :
    Nonempty (RelativeDiagonalFibre.RelVertHom p𝒯 Y a) ↔
      (diagonalAut hG (Y.obj a)).asIso.hom = 𝟙 (Y.obj a).x := by
  constructor
  · rintro ⟨m⟩
    rw [diagonalAut_hom, ← val_eq_isoFst_hom hG Y a m, val_eq_isoSnd_hom hG Y a m]
    exact (isoSnd hG (Y.obj a)).hom_inv_id
  · intro h
    rw [diagonalAut_hom, Iso.comp_inv_eq_id] at h
    have hbase := RelativeDiagonalFibre.base_eq_of_obj hY a
    refine ⟨⟨⟨(isoFst hG (Y.obj a)).hom, ?_⟩, ?_⟩⟩
    · refine IsHomLift.of_fac' p𝒮 _ _ ((Y.obj a).hx.trans hbase)
        ((Y.obj a).hy.trans hbase) ?_
      rw [map_isoFst_hom hG (Y.obj a)]
      simp
    · exact Hom.ext' (by simpa only [diagonal_map_a] using isoFst_hom hG (Y.obj a))
        (by simpa only [diagonal_map_b, isoSnd_hom] using h)

end

end SecondDiagonalFibre

end CategoryTheory.TwoFibreProductOver

end
