module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.DiagonalDescendingIso
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.RelativeDiagonalFibre
public import StacksFrontier.CategoryTheory.Sites.Stack.SlicePointIsomPresheaf

/-!
# Sections of the presheaf of relative vertical morphisms

Let `p : X ⥤ 𝒞` and `q : 𝒴 ⥤ 𝒞` be fibred in groupoids, let `F : X ⥤ 𝒴` be a 1-morphism over
`𝒞` and let `Y : 𝒯 ⥤ X ×_{F, 𝒴, F} X` be a 1-morphism over `𝒞`. A section of
`CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.relVertHomPresheaf` over `a : 𝒯` is a
vertical morphism between the two components of `Y a` whose image under `F` is the comparison
isomorphism of `Y a` — that is, exactly a witness that the comparison isomorphism of `Y a`
descends in the sense of
`StacksFrontier/CategoryTheory/FiberedInGroupoids/DiagonalDescendingIso.lean`. This file records
that dictionary and uses it to produce sections.

## Main results

* `CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.nonempty_relVertHom_iff`: the
  dictionary — a section over `a` exists exactly when the comparison isomorphism of `Y a`
  descends.
* `CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.exists_nonempty_relVertHom_of_hom`:
  for `Y` a scheme-valued point over `U` in the slice setting `𝒞 = 𝒟/Z`, `𝒯 = 𝒟/U.left`, any
  object `A` of the 2-fibre product with a morphism into the value of `Y` at the terminal object
  and with descending comparison isomorphism produces an object `a` of the slice, with the same
  underlying object as the base of `A`, over which `relVertHomPresheaf` has a section.

## Implementation notes

The second result is what turns a *point* of `X ×_{F, 𝒴, F} X` lying in the image of the
diagonal into a section of `relVertHomPresheaf`: a morphism `c : A ⟶ Y ⊤` has a base morphism
`A.base ⟶ U`, whose underlying morphism of `𝒟` is an object `a` of `𝒟/U.left`, and `c` then lies
over the structure morphism of `a` (`CategoryTheory.Functor.structHom`). Both `c` and
`Y (a ⟶ ⊤)` are therefore strongly cartesian lifts of that structure morphism with the same
target — every morphism is strongly cartesian, the 2-fibre product being fibred in groupoids —
so `CategoryTheory.Functor.IsStronglyCartesian.domainIsoOfBaseIso` identifies `A` with `Y a`,
and descending is invariant under that identification.
-/

@[expose] public section

open CategoryTheory Opposite

namespace CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

section Dictionary

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {X : Type u₃} [Category.{v₃} X]
  {𝒯 : Type u₂} [Category.{v₂} 𝒯] {𝒴 : Type u₄} [Category.{v₄} 𝒴]
  {p : X ⥤ 𝒞} {p𝒯 : 𝒯 ⥤ 𝒞} {q : 𝒴 ⥤ 𝒞} {F : X ⥤ 𝒴} {Y : 𝒯 ⥤ RelProd p q F}

/-- **A section of `relVertHomPresheaf` over `a` is a witness that the comparison isomorphism of
`Y a` descends.** The verticality demanded of a section is automatic, by
`CategoryTheory.TwoFibreProductOver.isHomLift_id_of_map_eq_iso`. -/
lemma nonempty_relVertHom_iff
    (hY : Y ⋙ RelProdP p q F = p𝒯) (hF : F ⋙ q = p) (a : 𝒯) :
    Nonempty (RelVertHom p𝒯 Y a) ↔
      ∃ β : (Y.obj a).x ⟶ (Y.obj a).y, F.map β = (Y.obj a).iso.hom := by
  refine ⟨fun ⟨m⟩ ↦ ⟨m.1.1, m.2⟩, fun ⟨β, hβ⟩ ↦ ?_⟩
  have h := isHomLift_id_of_map_eq_iso hF (Y.obj a) β hβ
  rw [base_eq_of_obj hY a] at h
  exact ⟨⟨⟨β, h⟩, hβ⟩⟩

end Dictionary

section Slice

variable {𝒟 : Type u₁} [Category.{v₁} 𝒟] {Z : 𝒟} {X : Type u₃} [Category.{v₃} X]
  {𝒴 : Type u₄} [Category.{v₄} 𝒴]
  {p : X ⥤ Over Z} {q : 𝒴 ⥤ Over Z} {F : X ⥤ 𝒴}
  {U : Over Z} {Y : Over U.left ⥤ RelProd p q F}

/-- **An object with a morphism into the value of `Y` at the terminal object, and with descending
comparison isomorphism, gives a section of `relVertHomPresheaf`.** Here `a`, the base morphism
`f'` of the morphism read into `U` and its factorisation through the structure morphism of `a`
are given; see
`CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.exists_nonempty_relVertHom_of_hom` for
the form in which they are produced from the morphism alone. -/
lemma nonempty_relVertHom_of_isHomLift (hp : p.IsFiberedInGroupoids)
    (hq : q.IsFiberedInGroupoids) (hY : Y ⋙ RelProdP p q F = Over.map U.hom) (hF : F ⋙ q = p)
    (a : Over U.left) (A : RelProd p q F) (c : A ⟶ Y.obj (Over.mk (𝟙 U.left)))
    (g : A.base ≅ (Over.map U.hom).obj a) (f' : A.base ⟶ U)
    (hf' : (RelProdP p q F).IsHomLift f' c) (hg : f' = g.hom ≫ Functor.structHom U a)
    (hA : ∃ β : A.x ⟶ A.y, F.map β = A.iso.hom) :
    Nonempty (RelVertHom (Over.map U.hom) Y a) := by
  have hRP : (RelProdP p q F).IsFiberedInGroupoids :=
    TwoFibreProductOver.isFiberedInGroupoids p p q F F hp hp hq hF hF
  have _ : (RelProdP p q F).IsHomLift (Functor.structHom U a)
      (Y.map (Functor.toMkId U a)) :=
    Functor.isHomLift_map_toMkId (RelProdP p q F) U Y hY a
  have _ : (RelProdP p q F).IsStronglyCartesian f' c :=
    hRP.isStronglyCartesian_homLift _ _
  have _ : (RelProdP p q F).IsStronglyCartesian (Functor.structHom U a)
      (Y.map (Functor.toMkId U a)) :=
    hRP.isStronglyCartesian_homLift _ _
  exact (nonempty_relVertHom_iff hY hF a).mpr (exists_map_eq_iso_of_hom hp hq hF
    (Functor.IsStronglyCartesian.domainIsoOfBaseIso (RelProdP p q F) (g := g) hg
      (Y.map (Functor.toMkId U a)) c).inv hA)

/-- **An object with a morphism into the value of `Y` at the terminal object, and with descending
comparison isomorphism, lies over an object of the slice over which `relVertHomPresheaf` has a
section.** The object of the slice is the base morphism of the morphism, read as a morphism of
`𝒟` into `U.left`; its underlying object of `𝒟` is that of the base of `A`. -/
lemma exists_nonempty_relVertHom_of_hom (hp : p.IsFiberedInGroupoids)
    (hq : q.IsFiberedInGroupoids) (hY : Y ⋙ RelProdP p q F = Over.map U.hom) (hF : F ⋙ q = p)
    (A : RelProd p q F) (c : A ⟶ Y.obj (Over.mk (𝟙 U.left)))
    (hA : ∃ β : A.x ⟶ A.y, F.map β = A.iso.hom) :
    ∃ a : Over U.left, a.left = A.base.left ∧
      Nonempty (RelVertHom (Over.map U.hom) Y a) := by
  have hbaseT : (Y.obj (Over.mk (𝟙 U.left))).base = U :=
    (base_eq_of_obj hY (Over.mk (𝟙 U.left))).trans (Functor.overMap_obj_mkId U)
  -- The base morphism of `c`, read as a morphism into `U`, and the object of the slice it is.
  set cb : A.base ⟶ U := c.hbase ≫ eqToHom hbaseT with hcb
  set a : Over U.left := Over.mk cb.left
  -- The base of `A` is the image of `a`, by an isomorphism which is the identity underneath.
  set ι : A.base ≅ (Over.map U.hom).obj a :=
    Over.isoMk (Iso.refl A.base.left) (by
      change (Iso.refl A.base.left).hom ≫ cb.left ≫ U.hom = A.base.hom
      rw [Iso.refl_hom, Category.id_comp]
      exact Over.w cb) with hι
  have hcb0 : (RelProdP p q F).IsHomLift cb c := by
    rw [hcb, IsHomLift.lift_comp_eqToHom_iff,
      show c.hbase = (RelProdP p q F).map c from rfl]
    refine IsHomLift.of_fac' (RelProdP p q F) ((RelProdP p q F).map c) c rfl rfl ?_
    simp only [eqToHom_refl, Category.id_comp]
    exact (Category.comp_id _).symm
  have hfac : cb = ι.hom ≫ Functor.structHom U a := by
    apply Over.OverMorphism.ext
    simp only [hι, Over.comp_left, Over.isoMk_hom_left, Iso.refl_hom, Category.id_comp,
      Functor.structHom, Over.homMk_left]
    rfl
  exact ⟨a, rfl, nonempty_relVertHom_of_isHomLift hp hq hY hF a A c ι cb hcb0 hfac hA⟩

end Slice

end CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre

end
