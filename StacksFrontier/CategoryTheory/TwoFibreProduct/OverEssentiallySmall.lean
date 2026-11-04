module

public import Mathlib.CategoryTheory.EssentiallySmall
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverComp
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFirstFactor
public import StacksFrontier.CategoryTheory.TwoFibreProductOver

/-!
# Essential smallness of the 2-fibre product over a base

Fix a base category `𝒞`, categories `𝒳`, `𝒴`, `𝒮` over `𝒞` with structure functors `p𝒳`,
`p𝒴`, `p𝒮`, and 1-morphisms `F : 𝒳 ⥤ 𝒮`, `G : 𝒴 ⥤ 𝒮` over `𝒞`. An object of the 2-fibre product
`𝒳 ×_𝒮 𝒴` of Stacks 0040 is a quadruple `(U, x, y, φ)` with `x`, `y` lying over `U` and
`φ : F x ≅ G y` vertical, and a morphism is a pair of morphisms of `𝒳` and `𝒴` over a common
morphism of `𝒞` compatible with the comparison isomorphisms.

If `𝒳` and `𝒴` are essentially small and the hom-sets of `𝒮` are small, then `𝒳 ×_𝒮 𝒴` is
essentially small. An object `(U, x, y, φ)` is determined up to isomorphism by the isomorphism
classes of `x` and `y` together with the morphism `F x₀ ⟶ G y₀` that `φ` becomes once `x` and `y`
are replaced by chosen representatives `x₀`, `y₀`: the isomorphisms `x₀ ≅ x` and `y₀ ≅ y` need
not lie over a common morphism of `𝒞`, but the comparison of the two images in `𝒞` that the
transported `φ` carries forces the two base morphisms to agree.

## Main results

* `CategoryTheory.TwoFibreProductOver.essentiallySmall`: the 2-fibre product of essentially
  small categories over a category with small hom-sets is essentially small.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
-/

@[expose] public section

open CategoryTheory

universe w u₀ w₀ v₁ w₁ v₂ w₂ v₃ w₃

namespace CategoryTheory.TwoFibreProductOver

variable {𝒞 : Type u₀} [Category.{w₀} 𝒞]
  {𝒳 : Type v₁} [Category.{w₁} 𝒳] {𝒴 : Type v₂} [Category.{w₂} 𝒴]
  {𝒮 : Type v₃} [Category.{w₃} 𝒮]
  {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒮 : 𝒮 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒮} {G : 𝒴 ⥤ 𝒮}

/-! ### Essential smallness -/

/-- The invariant of an object `(U, x, y, φ)` of the 2-fibre product used to bound its
isomorphism classes: the isomorphism classes of `x` and of `y`, together with `φ` transported to
the chosen representatives of these classes. -/
noncomputable def skeletonCode (P : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G) :
    Σ (a : Skeleton 𝒳) (b : Skeleton 𝒴),
      F.obj ((fromSkeleton 𝒳).obj a) ⟶ G.obj ((fromSkeleton 𝒴).obj b) :=
  ⟨toSkeleton P.x, toSkeleton P.y,
    F.map (fromSkeletonToSkeletonIso P.x).hom ≫ P.iso.hom ≫
      G.map (fromSkeletonToSkeletonIso P.y).inv⟩

/-- Equality of two values of the invariant type, unpacked: the two isomorphism classes agree,
and the two morphisms agree up to the resulting identifications. -/
lemma exists_eq_of_sigma_eq {a a' : Skeleton 𝒳} {b b' : Skeleton 𝒴}
    {φ : F.obj ((fromSkeleton 𝒳).obj a) ⟶ G.obj ((fromSkeleton 𝒴).obj b)}
    {φ' : F.obj ((fromSkeleton 𝒳).obj a') ⟶ G.obj ((fromSkeleton 𝒴).obj b')}
    (h : (⟨a, b, φ⟩ : Σ (a : Skeleton 𝒳) (b : Skeleton 𝒴),
      F.obj ((fromSkeleton 𝒳).obj a) ⟶ G.obj ((fromSkeleton 𝒴).obj b)) = ⟨a', b', φ'⟩) :
    ∃ (ha : a = a') (hb : b = b'),
      φ ≫ G.map (eqToHom (by rw [hb])) = F.map (eqToHom (by rw [ha])) ≫ φ' := by
  obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp h
  obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp (eq_of_heq h)
  cases eq_of_heq h
  exact ⟨rfl, rfl, by simp⟩

/-- Two objects with the same invariant have isomorphic components, by isomorphisms compatible
with the two comparison isomorphisms. -/
lemma exists_iso_of_skeletonCode_eq {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G}
    (h : skeletonCode P = skeletonCode Q) :
    ∃ (a : P.x ≅ Q.x) (b : P.y ≅ Q.y), F.map a.hom ≫ Q.iso.hom = P.iso.hom ≫ G.map b.hom := by
  obtain ⟨ha, hb, hφ⟩ := exists_eq_of_sigma_eq h
  refine ⟨(fromSkeletonToSkeletonIso P.x).symm ≪≫ eqToIso (by rw [ha]) ≪≫
      fromSkeletonToSkeletonIso Q.x,
    (fromSkeletonToSkeletonIso P.y).symm ≪≫ eqToIso (by rw [hb]) ≪≫
      fromSkeletonToSkeletonIso Q.y, ?_⟩
  simp only [Category.assoc] at hφ
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, Functor.map_comp, Category.assoc]
  rw [← cancel_epi (F.map (fromSkeletonToSkeletonIso P.x).hom),
    ← cancel_mono (G.map (fromSkeletonToSkeletonIso Q.y).inv)]
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id, Category.comp_id]
  simp only [Functor.map_comp, Iso.map_hom_inv_id_assoc]
  exact hφ.symm

variable (hF : F ⋙ p𝒮 = p𝒳) (hG : G ⋙ p𝒮 = p𝒴)
include hF hG

/-- A pair of morphisms of the two factors compatible with the comparison isomorphisms lies over
a common morphism of the base, because the comparison isomorphisms are vertical. -/
lemma base_eq_of_comm {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (a : P.x ⟶ Q.x)
    (b : P.y ⟶ Q.y) (w : F.map a ≫ Q.iso.hom = P.iso.hom ≫ G.map b) :
    eqToHom P.hy.symm ≫ p𝒴.map b ≫ eqToHom Q.hy =
      eqToHom P.hx.symm ≫ p𝒳.map a ≫ eqToHom Q.hx := by
  have h := congrArg p𝒮.map w
  simp only [Functor.map_comp] at h
  have hP := P.vertical
  have hQ := Q.vertical
  rw [IsHomLift.fac' p𝒮 (𝟙 P.base) P.iso.hom, IsHomLift.fac' p𝒮 (𝟙 Q.base) Q.iso.hom] at h
  have hFa := Functor.congr_hom hF a
  have hGb := Functor.congr_hom hG b
  simp only [Functor.comp_map] at hFa hGb
  rw [hFa, hGb] at h
  simp only [Category.id_comp, Category.assoc, eqToHom_trans, eqToHom_trans_assoc] at h
  rw [eqToHom_comp_iff, comp_eqToHom_iff] at h
  rw [h]
  simp

/-- Two objects of the 2-fibre product with the same invariant are isomorphic. -/
lemma nonempty_iso_of_skeletonCode_eq {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G}
    (h : skeletonCode P = skeletonCode Q) : Nonempty (P ≅ Q) := by
  obtain ⟨a, b, w⟩ := exists_iso_of_skeletonCode_eq h
  have w' : F.map a.inv ≫ P.iso.hom = Q.iso.hom ≫ G.map b.inv := by
    rw [← cancel_epi (F.map a.hom), ← cancel_mono (G.map b.hom)]
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id,
      Category.comp_id]
    rw [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id, Functor.map_id, Category.id_comp, w]
  exact ⟨{ hom := Hom.mk' a.hom b.hom (base_eq_of_comm hF hG _ _ w) w
           inv := Hom.mk' a.inv b.inv (base_eq_of_comm hF hG _ _ w') w'
           hom_inv_id := Hom.ext' (by simp) (by simp)
           inv_hom_id := Hom.ext' (by simp) (by simp) }⟩

/-- **The 2-fibre product of essentially small categories is essentially small.** If `𝒳` and
`𝒴` are essentially small and the hom-sets of `𝒮` are small, then `𝒳 ×_𝒮 𝒴` is essentially
small: its hom-sets inject into products of hom-sets of `𝒳` and `𝒴`, and its isomorphism
classes inject into the small type of invariants `skeletonCode`. -/
theorem essentiallySmall [EssentiallySmall.{w} 𝒳] [EssentiallySmall.{w} 𝒴]
    [LocallySmall.{w} 𝒮] : EssentiallySmall.{w} (TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G) := by
  have : LocallySmall.{w} (TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G) := ⟨fun P Q =>
    small_of_injective (f := fun φ : P ⟶ Q => (φ.a, φ.b))
      (fun φ ψ h => Hom.ext' (Prod.ext_iff.1 h).1 (Prod.ext_iff.1 h).2)⟩
  refine (essentiallySmall_iff _).2 ⟨?_, inferInstance⟩
  refine small_of_injective (f := fun s => skeletonCode ((fromSkeleton _).obj s)) (fun s t h => ?_)
  obtain ⟨e⟩ := nonempty_iso_of_skeletonCode_eq hF hG h
  rw [← toSkeleton_fromSkeleton_obj s, ← toSkeleton_fromSkeleton_obj t]
  exact congr_toSkeleton_of_iso e

/-! ### Exchanging the two factors, as an equivalence over the base -/

variable (p𝒳 p𝒴 p𝒮 F G) in
omit hF hG in
/-- **Exchanging the two factors of the 2-fibre product is an equivalence over the base**: the
functor `CategoryTheory.TwoFibreProductOver.swap` is strictly over `𝒞`, it is its own inverse on
the nose, and the unit and counit are identities. -/
def swapEquivalenceOver :
    StacksRepresentableCFG.EquivalenceOver (structureFunctor p𝒳 p𝒴 p𝒮 F G)
      (structureFunctor p𝒴 p𝒳 p𝒮 G F) where
  hom := ⟨swap p𝒳 p𝒴 p𝒮 F G, swap_comp_structureFunctor p𝒳 p𝒴 p𝒮 F G⟩
  inv := ⟨swap p𝒴 p𝒳 p𝒮 G F, swap_comp_structureFunctor p𝒴 p𝒳 p𝒮 G F⟩
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  unit_over := by ext; rw [eqToHom_app]; exact (eqToHom_refl _ _).symm
  counit_over := by ext; rw [eqToHom_app]; exact (eqToHom_refl _ _).symm

end CategoryTheory.TwoFibreProductOver

end
