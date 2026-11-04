module

public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRestrict

/-!
# The fibre of a morphism of presheaves over a representable section is a relocalization

Let `C` be a category, let `a : A ⟶ X` be a morphism of `C`, let `α : F ⟶ G` be a morphism of
presheaves on `C/X` and let `β : h_{A → X} ⟶ G` be a morphism from the representable presheaf of
`a`, i.e. a section of `G` over `A → X`. This file identifies the fibre product `F ×_G h_{A → X}`
of presheaves on `C/X`.

A section of `G` over `A → X` restricts, along the tautological morphism
`(W → A → X) ⟶ (A → X)`, to a section of `G` over every object of `C/X` of the form
`(Over.map a).obj W` for `W` an object of `C/A`. The *fibre of `α` over `β`* is accordingly a
presheaf on the smaller slice `C/A`:

```text
  (fibreOfSection a α β)(W)  =  { s ∈ F((Over.map a).obj W) | α s = β restricted to W } ,
```

a subpresheaf of the restriction `CategoryTheory.OverShriek.relocalizeRestrict` of `F` along
`CategoryTheory.Over.map a`. The theorem is that relocalizing it back to `C/X` produces the fibre
product: the square

```text
  Λ_a (fibreOfSection a α β) ⟶ F
        |                      |
        v                      v
      h_{A → X}   ----β---->   G
```

whose left leg is the structural morphism
`CategoryTheory.OverShriek.relocalizeToYoneda`, is cartesian.

## Main definitions

* `CategoryTheory.OverShriek.overMapTautHom`: the tautological morphism
  `(Over.map a).obj W ⟶ Over.mk a` of `C/X`, along which a section over `A → X` is restricted.
* `CategoryTheory.OverShriek.overMapMkIso`: an object `W` of `C/X` together with a factorization
  `ψ ≫ a = W.hom` is isomorphic to `(Over.map a).obj (Over.mk ψ)` by an isomorphism whose
  underlying morphism of `C` is an identity.
* `CategoryTheory.OverShriek.fibreOfSection`: the fibre of `α` over `β`, as a presheaf on `C/A`.
* `CategoryTheory.OverShriek.fibreOfSectionι`: its inclusion into the restriction of `F`.
* `CategoryTheory.OverShriek.relocalizeFibreOfSectionMap`: the comparison
  `Λ_a (fibreOfSection a α β) ⟶ F`.

## Main results

* `CategoryTheory.OverShriek.isPullback_relocalizeFibreOfSectionMap`: the square above is
  cartesian.

## References

* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Limits

namespace CategoryTheory.OverShriek

universe v u

variable {C : Type u} [Category.{v} C] {X A : C} (a : A ⟶ X)

/-- The tautological morphism `(W → A → X) ⟶ (A → X)` of `C/X` attached to an object `W` of
`C/A`: its underlying morphism of `C` is the structure morphism of `W`. Restriction along it
turns a section of a presheaf on `C/X` over `A → X` into a section over `(Over.map a).obj W`. -/
def overMapTautHom (W : Over A) : (Over.map a).obj W ⟶ Over.mk a :=
  Over.homMk W.hom rfl

/-- The underlying morphism of `C` of `CategoryTheory.OverShriek.overMapTautHom a W` is the
structure morphism of `W`. -/
@[simp] theorem overMapTautHom_left (W : Over A) : (overMapTautHom a W).left = W.hom := rfl

/-- The tautological morphisms are compatible with `CategoryTheory.Over.map`: restricting first
along a morphism of `C/A` and then along the tautological morphism is restricting along the
tautological morphism of the source. -/
theorem overMap_map_comp_overMapTautHom {W W' : Over A} (g : W' ⟶ W) :
    (Over.map a).map g ≫ overMapTautHom a W = overMapTautHom a W' :=
  Over.OverMorphism.ext (Over.w g)

/-- An object `W` of `C/X` together with a factorization `ψ ≫ a = W.hom` of its structure
morphism through `A` is isomorphic to `(Over.map a).obj (Over.mk ψ)`, by the isomorphism whose
two underlying morphisms of `C` are the identity of `W.left`. -/
def overMapMkIso {W : Over X} {ψ : W.left ⟶ A} (hψ : ψ ≫ a = W.hom) :
    W ≅ (Over.map a).obj (Over.mk ψ) where
  hom := Over.homMk (𝟙 W.left) ((Category.id_comp (ψ ≫ a)).trans hψ)
  inv := Over.homMk (𝟙 W.left) ((Category.id_comp W.hom).trans hψ.symm)
  hom_inv_id := Over.OverMorphism.ext (Category.id_comp _)
  inv_hom_id := Over.OverMorphism.ext (Category.id_comp _)

/-- The underlying morphism of `C` of the forward map of
`CategoryTheory.OverShriek.overMapMkIso a hψ` is the identity of `W.left`. -/
@[simp] theorem overMapMkIso_hom_left {W : Over X} {ψ : W.left ⟶ A} (hψ : ψ ≫ a = W.hom) :
    (overMapMkIso a hψ).hom.left = 𝟙 W.left :=
  rfl

/-- Restricting along `CategoryTheory.OverShriek.overMapMkIso` and then back is the identity. -/
theorem map_overMapMkIso_inv_hom (H : (Over X)ᵒᵖ ⥤ Type v) {W : Over X} {ψ : W.left ⟶ A}
    (hψ : ψ ≫ a = W.hom) (s : H.obj (op ((Over.map a).obj (Over.mk ψ)))) :
    H.map (overMapMkIso a hψ).inv.op (H.map (overMapMkIso a hψ).hom.op s) = s := by
  rw [← H.map_comp_apply, ← op_comp, (overMapMkIso a hψ).inv_hom_id, op_id, H.map_id_apply]

/-- Restricting back along `CategoryTheory.OverShriek.overMapMkIso` and then forward is the
identity. -/
theorem map_overMapMkIso_hom_inv (H : (Over X)ᵒᵖ ⥤ Type v) {W : Over X} {ψ : W.left ⟶ A}
    (hψ : ψ ≫ a = W.hom) (u : H.obj (op W)) :
    H.map (overMapMkIso a hψ).hom.op (H.map (overMapMkIso a hψ).inv.op u) = u := by
  rw [← H.map_comp_apply, ← op_comp, (overMapMkIso a hψ).hom_inv_id, op_id, H.map_id_apply]

variable {F G : (Over X)ᵒᵖ ⥤ Type v} (α : F ⟶ G) (β : yoneda.obj (Over.mk a) ⟶ G)

/-- **The fibre of `α : F ⟶ G` over a section `β` of `G` over `A → X`**, as a presheaf on the
slice `C/A`: a section over `W` is a section `s` of `F` over `(Over.map a).obj W` whose image
under `α` is the restriction of `β` along the tautological morphism of `W`. -/
def fibreOfSection : (Over A)ᵒᵖ ⥤ Type v where
  obj W := {s : F.obj (op ((Over.map a).obj (unop W))) //
    α.app (op ((Over.map a).obj (unop W))) s =
      β.app (op ((Over.map a).obj (unop W))) (overMapTautHom a (unop W))}
  map {W W'} g := ↾fun s => ⟨F.map ((Over.map a).map g.unop).op s.1, by
    have h1 := NatTrans.naturality_apply α ((Over.map a).map g.unop).op s.1
    have h2 := NatTrans.naturality_apply β ((Over.map a).map g.unop).op
      (overMapTautHom a (unop W))
    rw [h1, s.2, ← h2]
    exact congrArg (fun z => β.app (op ((Over.map a).obj (unop W'))) z)
      (overMap_map_comp_overMapTautHom a g.unop)⟩
  map_id W := by
    ext s
    have key : F.map ((Over.map a).map (𝟙 (unop W))).op s.1 = s.1 := by
      rw [(Over.map a).map_id, op_id]
      exact F.map_id_apply _ s.1
    exact key
  map_comp {W W' W''} g h := by
    ext s
    have key : F.map ((Over.map a).map (h.unop ≫ g.unop)).op s.1 =
        F.map ((Over.map a).map h.unop).op (F.map ((Over.map a).map g.unop).op s.1) := by
      rw [(Over.map a).map_comp, op_comp]
      exact F.map_comp_apply _ _ s.1
    exact key

/-- Restriction in `CategoryTheory.OverShriek.fibreOfSection a α β` along `g` is restriction
in `F` along `(Over.map a).map g.unop`, on underlying sections. -/
@[simp] theorem fibreOfSection_map_val {W W' : (Over A)ᵒᵖ} (g : W ⟶ W')
    (s : (fibreOfSection a α β).obj W) :
    ((fibreOfSection a α β).map g s).1 = F.map ((Over.map a).map g.unop).op s.1 :=
  rfl

/-- The inclusion of the fibre of `α` over `β` into the restriction of `F` along
`CategoryTheory.Over.map a`. -/
def fibreOfSectionι : fibreOfSection a α β ⟶ (relocalizeRestrict a).obj F where
  app _ := ↾fun s => s.1
  naturality _ _ _ := rfl

/-- The comparison `Λ_a (fibreOfSection a α β) ⟶ F`, the image of the inclusion of the
subpresheaf under the relocalization adjunction. -/
def relocalizeFibreOfSectionMap :
    (relocalizePresheafFunctor a).obj (fibreOfSection a α β) ⟶ F :=
  relocalizeOfRestricted a (fibreOfSectionι a α β)

/-- The comparison restricts the section carried by `(ψ, s)` along the isomorphism
`CategoryTheory.OverShriek.overMapMkIso` of the factorization. -/
theorem relocalizeFibreOfSectionMap_app_apply {W : (Over X)ᵒᵖ}
    (x : ((relocalizePresheafFunctor a).obj (fibreOfSection a α β)).obj W) :
    (relocalizeFibreOfSectionMap a α β).app W x =
      F.map (overMapMkIso a x.2).hom.op x.1.2.1 :=
  rfl

/-- If `α s` is the section `β` restricted along `t`, then restricting `s` along `f` gives `α`
of the section of `β` restricted along any `t'` equal to `f ≫ t`. -/
private theorem app_map_eq_of_comp_eq {P Q : Over X} (f : P ⟶ Q) (s : F.obj (op Q))
    (t : Q ⟶ Over.mk a) {t' : P ⟶ Over.mk a} (hs : α.app (op Q) s = β.app (op Q) t)
    (h : f ≫ t = t') : α.app (op P) (F.map f.op s) = β.app (op P) t' := by
  subst h
  rw [NatTrans.naturality_apply, hs]
  exact (NatTrans.naturality_apply β f.op t).symm

/-- **The fibre of a morphism of presheaves over a representable section is a relocalization.**
For `α : F ⟶ G` a morphism of presheaves on `C/X` and `β : h_{A → X} ⟶ G` a section of `G` over
`A → X`, the relocalization along `a` of `CategoryTheory.OverShriek.fibreOfSection` is the fibre
product of `F` and the representable presheaf of `a` over `G`, the structural morphism
`CategoryTheory.OverShriek.relocalizeToYoneda` being the projection to the representable
factor. -/
theorem isPullback_relocalizeFibreOfSectionMap :
    IsPullback (relocalizeFibreOfSectionMap a α β)
      (relocalizeToYoneda a (fibreOfSection a α β)) α β := by
  apply IsPullback.of_forall_isPullback_app
  intro W
  rw [Limits.Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext x
    obtain ⟨⟨ψ, s⟩, hx⟩ := x
    have hψ : ψ ≫ a = (unop W).hom := hx
    have hs : α.app (op ((Over.map a).obj (Over.mk ψ))) s.1 =
        β.app (op ((Over.map a).obj (Over.mk ψ))) (overMapTautHom a (Over.mk ψ)) := s.2
    exact app_map_eq_of_comp_eq a α β _ _ _ hs (Over.OverMorphism.ext (Category.id_comp ψ))
  · rintro ⟨⟨ψ, s⟩, hx⟩ ⟨⟨ψ', s'⟩, hx'⟩ ⟨h1, h2⟩
    have hψ : ψ ≫ a = (unop W).hom := hx
    have hψ' : ψ' ≫ a = (unop W).hom := hx'
    have h2' : (Over.homMk ψ hψ : unop W ⟶ Over.mk a) =
        (Over.homMk ψ' hψ' : unop W ⟶ Over.mk a) := h2
    have hbase : ψ = ψ' := congrArg Over.Hom.left h2'
    subst hbase
    obtain rfl : s = s' := by
      refine Subtype.ext ?_
      have h1' : F.map (overMapMkIso a hψ).hom.op s.1 =
          F.map (overMapMkIso a hψ).hom.op s'.1 := h1
      have key := congrArg (fun z => F.map (overMapMkIso a hψ).inv.op z) h1'
      rw [map_overMapMkIso_inv_hom a F hψ s.1, map_overMapMkIso_inv_hom a F hψ s'.1] at key
      exact key
    rfl
  · rintro u v huv
    have hv : v.left ≫ a = (unop W).hom := Over.w v
    refine ⟨relocalizeMk a (fibreOfSection a α β) v.left
      ⟨F.map (overMapMkIso a hv).inv.op u, ?_⟩ hv, ?_, ?_⟩
    · exact app_map_eq_of_comp_eq a α β _ _ _ huv (Over.OverMorphism.ext (Category.id_comp v.left))
    · exact map_overMapMkIso_hom_inv a F hv u
    · exact Over.OverMorphism.ext rfl

end CategoryTheory.OverShriek

end
