module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Diagonal
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality
public import StacksFrontier.CategoryTheory.TwoFibreProductOverRelocalize
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The 2-fibre product is unchanged by changing its target along a fully faithful 1-morphism

`CategoryTheory.TwoFibreProductOver.mapBase` postcomposes both legs of a 2-fibre product over
`𝒞` with a 1-morphism `b : ℬ ⥤ 𝒟` over `𝒞`. When `b` is full and faithful this comparison is an
*isomorphism of categories*, whose inverse replaces the comparison isomorphism `b φ` of an object
by its preimage `φ`.

Together with `CategoryTheory.TwoFibreProductOver.relocalizeBase`, the same statement for a change
of the *base* along `CategoryTheory.Over.map g`, this identifies the self-product of a category
over `T/Y` along its structure morphism with the self-product of the same category viewed over
`T/Y'`, compatibly with the structure functor and with the diagonal: the self-product of the
relative diagonal is unchanged by relocalizing the base.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.unmapBase`: the inverse of
  `CategoryTheory.TwoFibreProductOver.mapBase` for a full and faithful `b`.
* `CategoryTheory.TwoFibreProductOver.mapBaseFstEquivalenceOver` and
  `CategoryTheory.TwoFibreProductOver.unmapBaseFstEquivalenceOver`: the comparison read as an
  equivalence *over the first factor*, in each direction.
* `CategoryTheory.TwoFibreProductOver.structureFibreEquivalenceOver`: the comparison of the two
  self-products of a category over `T/Y` along its structure morphism, before and after
  relocalizing the base.

## Main results

* `CategoryTheory.TwoFibreProductOver.mapBase_comp_unmapBase` and
  `CategoryTheory.TwoFibreProductOver.unmapBase_comp_mapBase`: the two comparison functors are
  inverse to each other on the nose.
* `CategoryTheory.TwoFibreProductOver.structureFibreEquivalenceOver_comp_diagonal`: the
  comparison carries the diagonal to the diagonal, *strictly*.
* `CategoryTheory.TwoFibreProductOver.representedFibre_structure_changeBase`: a representing
  object for the fibre of the relative diagonal over a point of the base survives the
  relocalization, together with its structure morphism.

## References

* [Stacks Project, Tag 04X5](https://stacks.math.columbia.edu/tag/04X5)
* [Stacks Project, Tag 050G](https://stacks.math.columbia.edu/tag/050G)
-/

@[expose] public section

namespace CategoryTheory

universe vC vT vA vB vD uC uT uA uB uD

/-- The backward functor of the iterated-slice equivalence is an equivalence. -/
@[sga "3 I 1.3" "partial", sga "4 IV 5.5" "more general"]
instance Over.isEquivalence_iteratedSliceBackward {T : Type uC} [Category.{vC} T] {Y : T}
    (f : Over Y) : (Over.iteratedSliceBackward f).IsEquivalence :=
  (Over.iteratedSliceEquiv f).symm.isEquivalence_functor

namespace TwoFibreProductOver

section Retarget

variable {𝒞 : Type uC} [Category.{vC} 𝒞] {T : Type uT} [Category.{vT} T]
  {𝒜 : Type uA} [Category.{vA} 𝒜] {ℬ : Type uB} [Category.{vB} ℬ]
  {𝒟 : Type uD} [Category.{vD} 𝒟]
  {pT : T ⥤ 𝒞} {p𝒜 : 𝒜 ⥤ 𝒞} {pℬ : ℬ ⥤ 𝒞} {p𝒟 : 𝒟 ⥤ 𝒞}
  {G : T ⥤ ℬ} {F : 𝒜 ⥤ ℬ} {b : ℬ ⥤ 𝒟}

/-- **Changing the target of a 2-fibre product along a fully faithful 1-morphism over `𝒞` does
not change it, backward direction.** An object `(U, t, x, ψ : b (G t) ≅ b (F x))` of
`T ×_𝒟 𝒜` taken along the composed legs is the object `(U, t, x, b⁻¹ ψ)` of `T ×_ℬ 𝒜`. -/
noncomputable def unmapBase (hb : b ⋙ p𝒟 = pℬ) [b.Full] [b.Faithful] :
    TwoFibreProductOver pT p𝒜 p𝒟 (G ⋙ b) (F ⋙ b) ⥤ TwoFibreProductOver pT p𝒜 pℬ G F where
  obj Q :=
    { base := Q.base, x := Q.x, y := Q.y, hx := Q.hx, hy := Q.hy
      iso := b.preimageIso Q.iso
      vertical := by
        refine (Functor.isHomLift_map_iff_of_comp_eq pℬ p𝒟 b hb (𝟙 Q.base)
          (b.preimageIso Q.iso).hom).1 ?_
        rw [show b.map (b.preimageIso Q.iso).hom = Q.iso.hom from b.map_preimage _]
        exact Q.vertical }
  map {P Q} f :=
    { hbase := f.hbase, a := f.a, b := f.b, ha := f.ha, hb := f.hb
      w := by
        apply b.map_injective
        simp only [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
        simpa only [Functor.comp_map] using f.w }
  map_id _ := Hom.ext' rfl rfl
  map_comp _ _ := Hom.ext' rfl rfl

/-- The backward comparison functor is strictly over the first projection. -/
lemma unmapBase_comp_fst (hb : b ⋙ p𝒟 = pℬ) [b.Full] [b.Faithful] :
    unmapBase (pT := pT) (p𝒜 := p𝒜) (G := G) (F := F) hb ⋙ fst pT p𝒜 pℬ G F =
      fst pT p𝒜 p𝒟 (G ⋙ b) (F ⋙ b) := rfl

/-- Changing the target back does not change the first component of an object. -/
@[simp] lemma unmapBase_obj_x (hb : b ⋙ p𝒟 = pℬ) [b.Full] [b.Faithful]
    (Q : TwoFibreProductOver pT p𝒜 p𝒟 (G ⋙ b) (F ⋙ b)) :
    ((unmapBase (pT := pT) (p𝒜 := p𝒜) (G := G) (F := F) hb).obj Q).x = Q.x := rfl

/-- Changing the target back does not change the second component of an object. -/
@[simp] lemma unmapBase_obj_y (hb : b ⋙ p𝒟 = pℬ) [b.Full] [b.Faithful]
    (Q : TwoFibreProductOver pT p𝒜 p𝒟 (G ⋙ b) (F ⋙ b)) :
    ((unmapBase (pT := pT) (p𝒜 := p𝒜) (G := G) (F := F) hb).obj Q).y = Q.y := rfl

/-- Changing the target back does not change the first component of a morphism. -/
lemma unmapBase_map_a (hb : b ⋙ p𝒟 = pℬ) [b.Full] [b.Faithful]
    {Q Q' : TwoFibreProductOver pT p𝒜 p𝒟 (G ⋙ b) (F ⋙ b)} (f : Q ⟶ Q') :
    ((unmapBase (pT := pT) (p𝒜 := p𝒜) (G := G) (F := F) hb).map f).a = f.a := rfl

/-- Changing the target back does not change the second component of a morphism. -/
lemma unmapBase_map_b (hb : b ⋙ p𝒟 = pℬ) [b.Full] [b.Faithful]
    {Q Q' : TwoFibreProductOver pT p𝒜 p𝒟 (G ⋙ b) (F ⋙ b)} (f : Q ⟶ Q') :
    ((unmapBase (pT := pT) (p𝒜 := p𝒜) (G := G) (F := F) hb).map f).b = f.b := rfl

/-- Changing the target does not change the first component of an object. -/
@[simp] lemma mapBase_obj_x (hb : b ⋙ p𝒟 = pℬ) (P : TwoFibreProductOver pT p𝒜 pℬ G F) :
    ((mapBase (pT := pT) (p𝒜 := p𝒜) G F b hb).obj P).x = P.x := rfl

/-- Changing the target does not change the second component of an object. -/
@[simp] lemma mapBase_obj_y (hb : b ⋙ p𝒟 = pℬ) (P : TwoFibreProductOver pT p𝒜 pℬ G F) :
    ((mapBase (pT := pT) (p𝒜 := p𝒜) G F b hb).obj P).y = P.y := rfl

/-- Changing the target does not change the first component of a morphism. -/
lemma mapBase_map_a (hb : b ⋙ p𝒟 = pℬ)
    {P P' : TwoFibreProductOver pT p𝒜 pℬ G F} (f : P ⟶ P') :
    ((mapBase (pT := pT) (p𝒜 := p𝒜) G F b hb).map f).a = f.a := rfl

/-- Changing the target does not change the second component of a morphism. -/
lemma mapBase_map_b (hb : b ⋙ p𝒟 = pℬ)
    {P P' : TwoFibreProductOver pT p𝒜 pℬ G F} (f : P ⟶ P') :
    ((mapBase (pT := pT) (p𝒜 := p𝒜) G F b hb).map f).b = f.b := rfl

/-- An endofunctor of a 2-fibre product that fixes objects and both components of morphisms is
the identity. -/
private theorem eq_id_of_obj_eq_of_map_eq {pT : T ⥤ 𝒞} {p𝒜 : 𝒜 ⥤ 𝒞} {p𝒟 : 𝒟 ⥤ 𝒞}
    {G : T ⥤ 𝒟} {F : 𝒜 ⥤ 𝒟}
    (K : TwoFibreProductOver pT p𝒜 p𝒟 G F ⥤ TwoFibreProductOver pT p𝒜 p𝒟 G F)
    (hobj : ∀ P, K.obj P = P) (ha : ∀ {P P'} (f : P ⟶ P'), HEq (K.map f).a f.a)
    (hb : ∀ {P P'} (f : P ⟶ P'), HEq (K.map f).b f.b) : K = 𝟭 _ := by
  refine Functor.ext hobj (fun _ _ f => Hom.ext' ?_ ?_)
  · exact eq_of_heq ((ha f).trans (by simp))
  · exact eq_of_heq ((hb f).trans (by simp))

/-- The two comparison functors are inverse to each other, over `ℬ`. -/
lemma mapBase_comp_unmapBase (hb : b ⋙ p𝒟 = pℬ) [b.Full] [b.Faithful] :
    mapBase (pT := pT) (p𝒜 := p𝒜) G F b hb ⋙ unmapBase hb =
      𝟭 (TwoFibreProductOver pT p𝒜 pℬ G F) :=
  eq_id_of_obj_eq_of_map_eq _
    (by
      rintro ⟨base, x, y, hx, hy, iso, vert⟩
      exact obj_ext (Iso.ext (b.preimage_map iso.hom)))
    (fun _ => HEq.rfl) (fun _ => HEq.rfl)

/-- The two comparison functors are inverse to each other, over `𝒟`. -/
lemma unmapBase_comp_mapBase (hb : b ⋙ p𝒟 = pℬ) [b.Full] [b.Faithful] :
    unmapBase (pT := pT) (p𝒜 := p𝒜) (G := G) (F := F) hb ⋙ mapBase G F b hb =
      𝟭 (TwoFibreProductOver pT p𝒜 p𝒟 (G ⋙ b) (F ⋙ b)) :=
  eq_id_of_obj_eq_of_map_eq _
    (by
      rintro ⟨base, x, y, hx, hy, iso, vert⟩
      exact obj_ext (Iso.ext (b.map_preimage iso.hom)))
    (fun _ => HEq.rfl) (fun _ => HEq.rfl)

/-- **Changing the target along a fully faithful 1-morphism over `𝒞`, as an equivalence over the
first factor.** -/
noncomputable def mapBaseFstEquivalenceOver (hb : b ⋙ p𝒟 = pℬ) [b.Full] [b.Faithful] :
    StacksRepresentableCFG.EquivalenceOver (fst pT p𝒜 pℬ G F)
      (fst pT p𝒜 p𝒟 (G ⋙ b) (F ⋙ b)) where
  hom := ⟨mapBase G F b hb, mapBase_comp_fst G F b hb⟩
  inv := ⟨unmapBase hb, unmapBase_comp_fst hb⟩
  unitIso := eqToIso (mapBase_comp_unmapBase hb).symm
  counitIso := eqToIso (unmapBase_comp_mapBase hb)
  unit_over := by
    ext P
    simp only [Functor.whiskerRight_app, eqToIso.hom, eqToHom_app, eqToHom_map]
  counit_over := by
    ext P
    simp only [Functor.whiskerRight_app, eqToIso.hom, eqToHom_app, eqToHom_map]

/-- `CategoryTheory.TwoFibreProductOver.mapBaseFstEquivalenceOver` read backwards: changing the
target back along a fully faithful 1-morphism over `𝒞`, as an equivalence over the first factor. -/
noncomputable def unmapBaseFstEquivalenceOver (hb : b ⋙ p𝒟 = pℬ) [b.Full] [b.Faithful] :
    StacksRepresentableCFG.EquivalenceOver (fst pT p𝒜 p𝒟 (G ⋙ b) (F ⋙ b))
      (fst pT p𝒜 pℬ G F) where
  hom := ⟨unmapBase hb, unmapBase_comp_fst hb⟩
  inv := ⟨mapBase G F b hb, mapBase_comp_fst G F b hb⟩
  unitIso := eqToIso (unmapBase_comp_mapBase hb).symm
  counitIso := eqToIso (mapBase_comp_unmapBase hb)
  unit_over := by
    ext P
    simp only [Functor.whiskerRight_app, eqToIso.hom, eqToHom_app, eqToHom_map]
  counit_over := by
    ext P
    simp only [Functor.whiskerRight_app, eqToIso.hom, eqToHom_app, eqToHom_map]

end Retarget

section StructureFibre

variable {𝒞 : Type uC} [Category.{vC} 𝒞] {𝒳 : Type uT} [Category.{vT} 𝒳]
  {S S' : 𝒞} (p : 𝒳 ⥤ Over S) (g : S ⟶ S')

/-- **The self-product of a category over `T/S` along its structure morphism is unchanged by
relocalizing the base along `g : S ⟶ S'`.** The identification is the backward target change
along the iterated slice at `𝟙 S`, then the base change along `g`, then the forward target change
along the iterated slice at `g`. -/
noncomputable def structureFibreEquivalenceOver :
    StacksRepresentableCFG.EquivalenceOver
      (fst p p (Over.forget (Over.mk (𝟙 S)))
        (p ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 S)))
        (p ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 S))))
      (fst (p ⋙ Over.map g) (p ⋙ Over.map g) (Over.forget (Over.mk g))
        (p ⋙ Over.iteratedSliceBackward (Over.mk g))
        (p ⋙ Over.iteratedSliceBackward (Over.mk g))) :=
  (unmapBaseFstEquivalenceOver (pT := p) (p𝒜 := p) (G := p) (F := p)
      (ℬ := Over (Over.mk (𝟙 S)).left) (𝒟 := Over (Over.mk (𝟙 S)))
      (pℬ := 𝟭 (Over S)) (p𝒟 := Over.forget (Over.mk (𝟙 S)))
      (b := Over.iteratedSliceBackward (Over.mk (𝟙 S))) (Over.mapId_eq S)).trans
    ((fstEquivalenceOver g (Functor.comp_id p) (Functor.comp_id p)).trans
      (mapBaseFstEquivalenceOver (pT := p ⋙ Over.map g) (p𝒜 := p ⋙ Over.map g)
        (ℬ := Over (Over.mk g).left) (𝒟 := Over (Over.mk g))
        (G := p) (F := p) (b := Over.iteratedSliceBackward (Over.mk g)) rfl))

/-- The comparison commutes strictly with the two structure functors, up to `Over.map g`. -/
lemma structureFibreEquivalenceOver_comp_structureFunctor :
    (structureFibreEquivalenceOver p g).hom.functor ⋙
        structureFunctor (p ⋙ Over.map g) (p ⋙ Over.map g) (Over.forget (Over.mk g))
          (p ⋙ Over.iteratedSliceBackward (Over.mk g))
          (p ⋙ Over.iteratedSliceBackward (Over.mk g)) =
      structureFunctor p p (Over.forget (Over.mk (𝟙 S)))
          (p ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 S)))
          (p ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 S))) ⋙ Over.map g :=
  rfl

/-- **The comparison carries the diagonal to the diagonal, strictly.** -/
lemma structureFibreEquivalenceOver_comp_diagonal
    (h₀ : (p ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 S))) ⋙
      Over.forget (Over.mk (𝟙 S)) = p)
    (h₁ : (p ⋙ Over.iteratedSliceBackward (Over.mk g)) ⋙
      Over.forget (Over.mk g) = p ⋙ Over.map g) :
    diagonal h₀ ⋙ (structureFibreEquivalenceOver p g).hom.functor = diagonal h₁ := by
  have hobj : ∀ A : 𝒳,
      (diagonal h₀ ⋙ (structureFibreEquivalenceOver p g).hom.functor).obj A
        = (diagonal h₁).obj A := by
    intro A
    refine obj_ext (Iso.ext ?_)
    exact (congrArg (Over.iteratedSliceBackward (Over.mk g)).map
      Functor.preimage_id).trans (Functor.map_id _ _)
  refine Functor.ext hobj (fun A B f => Hom.ext' ?_ ?_)
  · have e1 : (eqToHom (hobj A)).a = 𝟙 A := by rw [eqToHom_a]; exact eqToHom_refl A _
    have e2 : (eqToHom (hobj B).symm).a = 𝟙 B := by rw [eqToHom_a]; exact eqToHom_refl B _
    rw [comp_a, comp_a, e1, e2, diagonal_map_a]
    exact ((Category.id_comp _).trans (Category.comp_id _)).symm
  · have e1 : (eqToHom (hobj A)).b = 𝟙 A := by rw [eqToHom_b]; exact eqToHom_refl A _
    have e2 : (eqToHom (hobj B).symm).b = 𝟙 B := by rw [eqToHom_b]; exact eqToHom_refl B _
    rw [comp_b, comp_b, e1, e2, diagonal_map_b]
    exact ((Category.id_comp _).trans (Category.comp_id _)).symm

end StructureFibre

section ChangeBaseAndTarget

variable {𝒞 : Type uC} [Category.{vC} 𝒞] {𝒳 : Type uT} [Category.{vT} 𝒳]
  {𝒵 : Type uA} [Category.{vA} 𝒵] {𝒵' : Type uB} [Category.{vB} 𝒵']
  {𝒯 : Type uD} [Category.{vD} 𝒯]

/-- **A representing object for a 2-fibre product with a represented first factor survives a
change of the base along `g` together with a change of the target along a fully faithful `H`.** -/
lemma representedFibre_changeBase_and_target {S S' U : 𝒞} (g : S ⟶ S') (u : U ⟶ S)
    (p : 𝒳 ⥤ Over S) (pZ : 𝒵 ⥤ Over S) (pZ' : 𝒵' ⥤ Over S')
    (d : 𝒳 ⥤ 𝒵) (d' : 𝒳 ⥤ 𝒵') (H : 𝒵 ⥤ 𝒵') [H.Full] [H.Faithful]
    (hH : H ⋙ pZ' = pZ ⋙ Over.map g) (hd : d ⋙ H = d')
    (hD : d ⋙ pZ = p) (y : Over U ⥤ 𝒵) (hy : y ⋙ pZ = Over.map u)
    (q : 𝒯 ⥤ Over U)
    (e : StacksRepresentableCFG.EquivalenceOver (fst (Over.map u) p pZ y d) q) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (fst (Over.map (u ≫ g)) (p ⋙ Over.map g) pZ' (y ⋙ H) d') q) := by
  have e₀ := unrelocalizeFstEquivalenceOver_trans g hy hD e
  have e₂ := (unmapBaseFstEquivalenceOver (pT := Over.map u ⋙ Over.map g)
    (p𝒜 := p ⋙ Over.map g) (G := y) (F := d) (b := H) hH).trans e₀
  rw [Over.mapComp_eq, ← hd]
  exact ⟨e₂⟩

end ChangeBaseAndTarget

section StructureSelfProduct

variable {𝒞 : Type uC} [Category.{vC} 𝒞] {𝒳 : Type uT} [Category.{vT} 𝒳]
  {𝒯 : Type uD} [Category.{vD} 𝒯]

/-- **The self-product of the relative diagonal is unchanged by relocalizing the base.** If the
fibre of the diagonal of `p` over a point `U` of `T/S` is represented by `q`, then so is the fibre
of the diagonal of `p` viewed over `T/S'`, over the corresponding point of `T/S'`, and the
representing object comes with its structure morphism. -/
lemma representedFibre_structure_changeBase {S S' : 𝒞} (p : 𝒳 ⥤ Over S) (g : S ⟶ S')
    (U : Over S)
    (h₀ : (p ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 S))) ⋙
      Over.forget (Over.mk (𝟙 S)) = p)
    (h₁ : (p ⋙ Over.iteratedSliceBackward (Over.mk g)) ⋙
      Over.forget (Over.mk g) = p ⋙ Over.map g)
    (y : Over U.left ⥤ TwoFibreProductOver p p (Over.forget (Over.mk (𝟙 S)))
      (p ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 S)))
      (p ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 S))))
    (hy : y ⋙ structureFunctor p p (Over.forget (Over.mk (𝟙 S)))
      (p ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 S)))
      (p ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 S))) = Over.map U.hom)
    (q : 𝒯 ⥤ Over U.left)
    (e : StacksRepresentableCFG.EquivalenceOver
      (fst (Over.map U.hom) p
        (structureFunctor p p (Over.forget (Over.mk (𝟙 S)))
          (p ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 S)))
          (p ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 S)))) y
        (diagonal h₀)) q) :
    ∃ y' : Over U.left ⥤ TwoFibreProductOver (p ⋙ Over.map g) (p ⋙ Over.map g)
        (Over.forget (Over.mk g))
        (p ⋙ Over.iteratedSliceBackward (Over.mk g))
        (p ⋙ Over.iteratedSliceBackward (Over.mk g)),
      y' ⋙ structureFunctor (p ⋙ Over.map g) (p ⋙ Over.map g)
        (Over.forget (Over.mk g)) (p ⋙ Over.iteratedSliceBackward (Over.mk g))
        (p ⋙ Over.iteratedSliceBackward (Over.mk g)) = Over.map (U.hom ≫ g) ∧
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (fst (Over.map (U.hom ≫ g)) (p ⋙ Over.map g)
          (structureFunctor (p ⋙ Over.map g) (p ⋙ Over.map g)
            (Over.forget (Over.mk g)) (p ⋙ Over.iteratedSliceBackward (Over.mk g))
            (p ⋙ Over.iteratedSliceBackward (Over.mk g))) y'
          (diagonal h₁)) q) := by
  let E := (structureFibreEquivalenceOver p g).toEquivalence
  let H := E.functor
  have hH := structureFibreEquivalenceOver_comp_structureFunctor p g
  have hd := structureFibreEquivalenceOver_comp_diagonal p g h₀ h₁
  refine ⟨y ⋙ H, ?_, ?_⟩
  · change (y ⋙ (structureFibreEquivalenceOver p g).hom.functor) ⋙ _ = _
    rw [Functor.assoc, hH, ← Functor.assoc, hy, ← Over.mapComp_eq]
  · exact representedFibre_changeBase_and_target g U.hom p _ _ _ _ H hH hd rfl y hy q e

end StructureSelfProduct

end TwoFibreProductOver

end CategoryTheory

end
