module

public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRepresentable
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRestrictProduct

/-!
# Representability of a restricted presheaf

Let `f : V ⟶ U` be a morphism of a category `C`. For a presheaf `F` on `C/U`, the restriction
`j^{-1} F` along `j = Over.map f` is representable exactly when the product
`h_{(V →f U)} ⨯ F` is.

One direction is the identification
`CategoryTheory.OverShriek.relocalizeRestrictIsoProduct` of `Λ_f (j^{-1} F)` with that
product, together with the fact that `Λ_f` carries a representable presheaf to a
representable presheaf. The other is direct: a representing object for the product is an
object `W` of `C/U` over `(V →f U)`, and the component of that structure morphism over `V`
represents `j^{-1} F`.

## Main results

* `CategoryTheory.OverShriek.isRepresentable_relocalizeRestrict_of_prod`
* `CategoryTheory.OverShriek.isRepresentable_relocalizeRestrict_iff`

## References

* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.OverShriek

universe v u

variable {C : Type u} [Category.{v} C] {U V : C} (f : V ⟶ U)

/-- **A representable product makes the restriction representable.** If `h_{(V →f U)} ⨯ F` is
represented by an object `W` of `C/U`, then the restriction of `F` to `C/V` is represented by
the component over `V` of the structure morphism `W ⟶ (V →f U)` that the first factor of the
product supplies.

A morphism `T ⟶ W` out of an object `T` of `C/V` — that is, out of `j T` — is a pair
consisting of a morphism `j T ⟶ (V →f U)` and a section of `F` over `j T`; the first
component is forced to be the canonical one exactly when the morphism `T ⟶ W` lies over `V`,
so what is left is a section of `j^{-1} F` over `T`. -/
theorem isRepresentable_relocalizeRestrict_of_prod (F : (Over U)ᵒᵖ ⥤ Type v)
    (h : (FunctorToTypes.prod (yoneda.obj (Over.mk f)) F).IsRepresentable) :
    ((relocalizeRestrict f).obj F).IsRepresentable := by
  obtain ⟨W, ⟨e⟩⟩ := h
  let p : W ⟶ Over.mk f := (e.homEquiv (𝟙 W)).1
  have hp {T : Over U} (g : T ⟶ W) : (e.homEquiv g).1 = g ≫ p :=
    congrArg (fun t => t.1) (e.homEquiv_eq g)
  let P : Over V := Over.mk p.left
  let lift {T : Over V} (g : T ⟶ P) : (Over.map f).obj T ⟶ W :=
    Over.homMk g.left (by
      change g.left ≫ W.hom = T.hom ≫ f
      rw [← p.w, ← Category.assoc]
      exact congrArg (· ≫ f) g.w)
  let canonical (T : Over V) : (Over.map f).obj T ⟶ Over.mk f := Over.homMk T.hom rfl
  have hfirst {T : Over V} (g : T ⟶ P) : (e.homEquiv (lift g)).1 = canonical T :=
    (hp (lift g)).trans (Over.OverMorphism.ext g.w)
  let inv {T : Over V} (x : F.obj (op ((Over.map f).obj T))) : T ⟶ P :=
    Over.homMk (e.homEquiv.symm (canonical T, x)).left (by
      have hh := hp (e.homEquiv.symm (canonical T, x))
      rw [congrArg (fun t => t.1) (e.homEquiv.apply_symm_apply (canonical T, x))] at hh
      exact congrArg Over.Hom.left hh.symm)
  have hinv {T : Over V} (x : F.obj (op ((Over.map f).obj T))) :
      lift (inv x) = e.homEquiv.symm (canonical T, x) := Over.OverMorphism.ext rfl
  refine ⟨P, ⟨{ homEquiv := ?_, homEquiv_comp := ?_ }⟩⟩
  · intro T
    refine ⟨fun g => (e.homEquiv (lift g)).2, inv, fun g => ?_, fun x => ?_⟩
    · refine Over.OverMorphism.ext ?_
      change (e.homEquiv.symm (canonical T, (e.homEquiv (lift g)).2)).left = g.left
      rw [← hfirst g]
      exact congrArg Over.Hom.left (e.homEquiv.symm_apply_apply (lift g))
    · change (e.homEquiv (lift (inv x))).2 = x
      rw [hinv]
      exact congrArg (fun t => t.2) (e.homEquiv.apply_symm_apply (canonical T, x))
  · intro T T' a g
    change (e.homEquiv (lift (a ≫ g))).2 = F.map ((Over.map f).map a).op _
    rw [show lift (a ≫ g) = (Over.map f).map a ≫ lift g from Over.OverMorphism.ext rfl,
      e.homEquiv_comp]
    rfl

/-- **The restriction of a presheaf is representable exactly when the product with the
representable presheaf of `(V →f U)` is.**

Relocalizing the restriction back along `f` gives that product, by
`CategoryTheory.OverShriek.relocalizeRestrictIsoProduct`, and relocalization carries a
representable presheaf to a representable presheaf, by
`CategoryTheory.OverShriek.relocalizeYonedaIso`; the converse is
`CategoryTheory.OverShriek.isRepresentable_relocalizeRestrict_of_prod`. -/
theorem isRepresentable_relocalizeRestrict_iff (F : (Over U)ᵒᵖ ⥤ Type v) :
    ((relocalizeRestrict f).obj F).IsRepresentable ↔
      (FunctorToTypes.prod (yoneda.obj (Over.mk f)) F).IsRepresentable := by
  refine ⟨fun ⟨W, ⟨e⟩⟩ => ?_, isRepresentable_relocalizeRestrict_of_prod f F⟩
  exact isRepresentable_of_natIso (yoneda.obj ((Over.map f).obj W))
    (((relocalizeYonedaIso f).app W).symm ≪≫
      (relocalizePresheafFunctor f).mapIso (Functor.representableByEquiv e) ≪≫
      relocalizeRestrictIsoProduct f F ≪≫
      FunctorToTypes.binaryProductIso (yoneda.obj (Over.mk f)) F)

end CategoryTheory.OverShriek

end
