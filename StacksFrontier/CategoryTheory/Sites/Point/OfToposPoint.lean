module

public import Mathlib.CategoryTheory.Functor.TypeValuedFlat
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
public import Mathlib.CategoryTheory.Sites.Localization
public import StacksFrontier.CategoryTheory.Elements
public import StacksFrontier.CategoryTheory.Sites.Point.FiberComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Every point of a topos comes from a point of the site

Let `p` be a point of the topos `Sh(C, J)`, i.e. a morphism of topoi `Sh(pt) → Sh(C, J)`. The
fibre functor
`u : C ⥤ Type w`, `u(X) = p⁻¹(h_X^#)`,
of the sheafified representables is the fibre functor of a point of the *site* `(C, J)`, and
the stalk functor of that point of the site is the inverse image `p⁻¹` of `p`. This is clause
(2) of Stacks 00YA; clause (1), that a point of the site gives a point of the topos, is
`CategoryTheory.GrothendieckTopology.Point.pointOfTopos`.

The functor `u` is the restriction along the Yoneda embedding of
`Ψ : (Cᵒᵖ ⥤ Type w) ⥤ Type w`, `Ψ(P) = p⁻¹(P^#)`,
and the proof turns on two properties of `Ψ`: it is a composite of two left adjoints, hence
preserves all colimits, and it is a composite of two left exact functors, hence preserves
finite limits. Colimit preservation gives the key covering lemma
(`PointOfTopos.exists_sitePointFiber_presheafStalk`): every element of `Ψ(P)` comes from an
element of `u(X)` along a morphism `h_X ⟶ P`, because `P` is a colimit of representables.
Left exactness gives, through `CategoryTheory.Functor.isCofiltered_elements`, that the
category of elements of `Ψ` is cofiltered; transporting that along the key covering lemma and
the full faithfulness of the Yoneda embedding makes the category of elements of `u` cofiltered.
The covering condition on `u` holds because the inclusion of a covering sieve becomes an
isomorphism after sheafification. Finally the comparison between the two stalk functors is
again obtained from the key covering lemma: the two functors on presheaves agree on
representables and both preserve colimits.

Because the presheaves here take values in `Type w` while `C` is only assumed locally
`w`-small, the Yoneda embedding used throughout is `CategoryTheory.shrinkYoneda`, and the
density theorem "every presheaf is a colimit of representables" is proved for it in the first
section.

## Main definitions

* `CategoryTheory.Presheaf.shrinkCoconeOfRepresentable`: the tautological cocone on the
  representables over a presheaf of `w`-types.
* `PointOfTopos.presheafStalkFunctor`: the functor `Ψ : P ↦ p⁻¹(P^#)`.
* `PointOfTopos.sitePointFiber`: the fibre functor `u : X ↦ p⁻¹(h_X^#)`.
* `PointOfTopos.sitePoint`: the point of the site `(C, J)` attached to a point of the topos.
* `PointOfTopos.sheafFiberIsoInverseImage`: the identification of its stalk functor with `p⁻¹`.

## Main results

* `CategoryTheory.Presheaf.shrinkColimitOfRepresentable`: the density theorem for
  `shrinkYoneda`.
* `PointOfTopos.exists_sitePointFiber_stalk`: the key covering lemma — every element of the
  stalk of a sheaf comes from a sheafified representable.
* `PointOfTopos.isCofiltered_sitePointFiber_elements`: the category of elements of `u` is
  cofiltered.
* `PointOfTopos.sitePointFiber_jointly_surjective`: covering sieves are jointly surjective
  on `u`.
* `PointOfTopos.exists_sitePoint`: Stacks 00YA (2).

## References

* [Stacks Project, Tag 00YA](https://stacks.math.columbia.edu/tag/00YA)
* [Stacks Project, Tag 00Y4](https://stacks.math.columbia.edu/tag/00Y4)
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe w v u

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]

/-- The tautological cocone exhibiting a presheaf of `w`-types on a locally `w`-small category
as a colimit of the representables `shrinkYoneda.obj X`, indexed by the opposite of the
category of elements of the presheaf: the leg at an element `x` of `P(X)` is the morphism
`shrinkYoneda.obj X ⟶ P` which Yoneda's lemma attaches to `x`.

This is the `shrinkYoneda` form of `CategoryTheory.Presheaf.coconeOfRepresentable`, which is
stated for `uliftYoneda` and therefore only for presheaves whose values are at least as large
as the hom-sets of `C`. -/
@[simps, sga "3 I 1.7.0", sga "3 I 1.7.1", sga "4 I 8.3.2"]
noncomputable def shrinkCoconeOfRepresentable (P : Cᵒᵖ ⥤ Type w) :
    Cocone ((Functor.Elements.π P).leftOp ⋙ shrinkYoneda.{w}) where
  pt := P
  ι :=
    { app x := shrinkYonedaEquiv.symm x.unop.val
      naturality {x₁ x₂} f := by
        dsimp
        rw [Category.comp_id]
        exact (shrinkYonedaEquiv_symm_map f.unop.hom (unop x₂).val).symm.trans
          (congrArg _ f.unop.map_val) }

/-- The morphism out of a presheaf `P` induced by a cocone on the diagram of representables
indexed by the category of elements of `P`: its value at an element `x` of `P(X)` is the
section of the cocone point over `X` which Yoneda's lemma attaches to the leg of the cocone at
`x`. It is the descent morphism of the density theorem
`CategoryTheory.Presheaf.shrinkColimitOfRepresentable`. -/
noncomputable def shrinkDescOfRepresentable {P : Cᵒᵖ ⥤ Type w}
    (s : Cocone ((Functor.Elements.π P).leftOp ⋙ shrinkYoneda.{w})) : P ⟶ s.pt where
  app X := ↾fun x ↦ shrinkYonedaEquiv (s.ι.app (op (Functor.elementsMk P X x)))
  naturality X Y f := by
    ext x
    have h := s.w (Functor.Elements.homMk (x := P.elementsMk X x)
      (y := P.elementsMk Y (P.map f x)) f rfl).op
    dsimp at h ⊢
    rw [← h, ← shrinkYonedaEquiv_naturality]
    rfl

/-- The value of `CategoryTheory.Presheaf.shrinkDescOfRepresentable` at an element. -/
@[simp]
theorem shrinkDescOfRepresentable_app_apply {P : Cᵒᵖ ⥤ Type w}
    (s : Cocone ((Functor.Elements.π P).leftOp ⋙ shrinkYoneda.{w})) (X : Cᵒᵖ)
    (x : P.obj X) :
    (shrinkDescOfRepresentable s).app X x =
      shrinkYonedaEquiv (s.ι.app (op (Functor.elementsMk P X x))) :=
  rfl

/-- Composing the morphism attached by Yoneda's lemma to a section with `g` is the morphism
attached to the image of the section under `g`. -/
private theorem shrinkYonedaEquiv_symm_comp_eq {X : C} {P Q : Cᵒᵖ ⥤ Type w} (x : P.obj (op X))
    (g : P ⟶ Q) : shrinkYonedaEquiv.symm x ≫ g = shrinkYonedaEquiv.symm (g.app _ x) := by
  apply shrinkYonedaEquiv.injective
  rw [shrinkYonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The descent morphism of a cocone on the diagram of representables is compatible with the
legs of the tautological cocone. -/
theorem shrinkYonedaEquiv_symm_comp_shrinkDescOfRepresentable {P : Cᵒᵖ ⥤ Type w}
    (s : Cocone ((Functor.Elements.π P).leftOp ⋙ shrinkYoneda.{w})) (X : Cᵒᵖ)
    (x : P.obj X) :
    shrinkYonedaEquiv.symm x ≫ shrinkDescOfRepresentable s =
      s.ι.app (op (Functor.elementsMk P X x)) := by
  rw [shrinkYonedaEquiv_symm_comp_eq, shrinkDescOfRepresentable_app_apply,
    Equiv.symm_apply_apply]

/-- The descent morphism of a cocone on the diagram of representables is the unique morphism
compatible with the legs of the tautological cocone. -/
theorem eq_shrinkDescOfRepresentable {P : Cᵒᵖ ⥤ Type w}
    {s : Cocone ((Functor.Elements.π P).leftOp ⋙ shrinkYoneda.{w})} (m : P ⟶ s.pt)
    (hm : ∀ (X : Cᵒᵖ) (x : P.obj X), shrinkYonedaEquiv.symm x ≫ m =
      s.ι.app (op (Functor.elementsMk P X x))) :
    m = shrinkDescOfRepresentable s := by
  ext X x
  have h := congrArg shrinkYonedaEquiv (hm X x)
  rw [shrinkYonedaEquiv_comp, Equiv.apply_symm_apply] at h
  exact h

/-- **The density theorem for `shrinkYoneda`.** Every presheaf of `w`-types on a locally
`w`-small category is the colimit of the representable presheaves `shrinkYoneda.obj X` indexed
by the opposite of its category of elements, via the tautological cocone
`CategoryTheory.Presheaf.shrinkCoconeOfRepresentable`.

This is the `shrinkYoneda` form of `CategoryTheory.Presheaf.colimitOfRepresentable`, which is
stated for `uliftYoneda` and therefore only for presheaves whose values are at least as large
as the hom-sets of `C`. Note that the indexing category is not `w`-small in general, so the
colimit itself need not exist in `Type w`; what is asserted is that this cocone is
universal. -/
@[sga "3 I 1.7.0", sga "3 I 1.7.1" "more general", sga "4 I 3.4", sga "4 I 8.3.2"]
noncomputable def shrinkColimitOfRepresentable (P : Cᵒᵖ ⥤ Type w) :
    IsColimit (shrinkCoconeOfRepresentable P) where
  desc s := shrinkDescOfRepresentable s
  fac s j :=
    shrinkYonedaEquiv_symm_comp_shrinkDescOfRepresentable s (unop j).obj (unop j).val
  uniq _ m hm :=
    eq_shrinkDescOfRepresentable m fun X x ↦ hm (op (Functor.elementsMk P X x))

end CategoryTheory.Presheaf

namespace PointOfTopos

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [LocallySmall.{w} C]
  [HasSheafify J (Type w)] (p : PointOfTopos.{w, v, u} J)

/-! ### The fibre functor of a point of the topos -/

/-- The stalk at a point `p` of the topos `Sh(C, J)` of the sheaf associated to a presheaf:
the composite of sheafification with `p⁻¹`. It is a composite of two left adjoints, hence a
left adjoint (`PointOfTopos.presheafStalkAdjunction`), and a composite of two left exact
functors, hence left exact. -/
@[sga "4 IV 6.8.2"]
noncomputable def presheafStalkFunctor : (Cᵒᵖ ⥤ Type w) ⥤ Type w :=
  presheafToSheaf J (Type w) ⋙ p.inverseImage

/-- `PointOfTopos.presheafStalkFunctor` is a left adjoint: it is the composite of the
sheafification adjunction with the adjunction `p⁻¹ ⊣ p_*`. -/
noncomputable def presheafStalkAdjunction :
    p.presheafStalkFunctor ⊣ p.pushforward ⋙ sheafToPresheaf J (Type w) :=
  (sheafificationAdjunction J (Type w)).comp p.adj

/-- `PointOfTopos.presheafStalkFunctor` preserves finite limits. -/
instance : PreservesFiniteLimits p.presheafStalkFunctor :=
  have := p.preservesFiniteLimits
  comp_preservesFiniteLimits _ _

/-- The fibre functor of the point of the site `(C, J)` attached to a point `p` of the topos
`Sh(C, J)`: it sends `X : C` to the stalk `p⁻¹(h_X^#)` at `p` of the sheafification of the
presheaf represented by `X`. This is the functor `u` of the proof of Stacks 00YA (2). -/
@[sga "4 IV 6.8.2"]
noncomputable def sitePointFiber : C ⥤ Type w :=
  shrinkYoneda.{w} ⋙ p.presheafStalkFunctor

/-- The fibre functor `PointOfTopos.sitePointFiber` is the restriction of
`PointOfTopos.presheafStalkFunctor` along the Yoneda embedding. -/
theorem shrinkYoneda_comp_presheafStalkFunctor :
    shrinkYoneda.{w} ⋙ p.presheafStalkFunctor = p.sitePointFiber :=
  rfl

/-! ### The key covering lemma -/

/-- **The key covering lemma, presheaf form.** Every element of the stalk at `p` of the sheaf
associated to a presheaf `P` comes from the stalk of a representable presheaf: there are an
object `X`, a morphism `η : h_X ⟶ P` and an element `x` of `u(X)` whose image under `η` is the
given element.

This is the statement that the maps `u(X) → p⁻¹(P^#)` induced by the morphisms out of
representables are jointly surjective. It holds because `P` is a colimit of representables
(`CategoryTheory.Presheaf.shrinkColimitOfRepresentable`), because
`PointOfTopos.presheafStalkFunctor` is a left adjoint and therefore preserves that colimit,
and because an element of a colimit of types comes from one of the indices. -/
@[sga "4 IV 6.8" "special case", sga "4 VIII 7.9.1" "partial"]
theorem exists_sitePointFiber_presheafStalk (P : Cᵒᵖ ⥤ Type w)
    (t : p.presheafStalkFunctor.obj P) :
    ∃ (X : C) (η : shrinkYoneda.{w}.obj X ⟶ P) (x : p.sitePointFiber.obj X),
      p.presheafStalkFunctor.map η x = t := by
  have : PreservesColimitsOfSize.{v, max u w} p.presheafStalkFunctor :=
    p.presheafStalkAdjunction.leftAdjoint_preservesColimits
  obtain ⟨j, x, hx⟩ := Limits.Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves p.presheafStalkFunctor
      (Presheaf.shrinkColimitOfRepresentable P)) t
  exact ⟨(unop j).obj.unop, (Presheaf.shrinkCoconeOfRepresentable P).ι.app j, x, hx⟩

/-- **The key covering lemma.** Every element of the stalk `p⁻¹F` of a sheaf at a point `p` of
the topos comes from a sheafified representable: there are an object `X`, an element `x` of
`u(X)` and a morphism of sheaves `s : h_X^# ⟶ F` with `p⁻¹(s)(x)` the given element.

This is the form in which the lemma is used in the proof of Stacks 00YA (2); it follows from
the presheaf form `PointOfTopos.exists_sitePointFiber_presheafStalk`, because the counit of the
sheafification adjunction is an isomorphism on sheaves. -/
@[sga "4 IV 6.8" "special case"]
theorem exists_sitePointFiber_stalk (F : Sheaf J (Type w)) (t : p.inverseImage.obj F) :
    ∃ (X : C) (x : p.sitePointFiber.obj X)
      (s : (presheafToSheaf J (Type w)).obj (shrinkYoneda.{w}.obj X) ⟶ F),
      p.inverseImage.map s x = t := by
  set ε := (sheafificationAdjunction J (Type w)).counit.app F with hε
  obtain ⟨X, η, x, hx⟩ := p.exists_sitePointFiber_presheafStalk ((sheafToPresheaf J (Type w)).obj F)
    (p.inverseImage.map (inv ε) t)
  have hinv : p.inverseImage.map (inv ε) ≫ p.inverseImage.map ε = 𝟙 _ := by
    rw [← Functor.map_comp, IsIso.inv_hom_id]
    exact p.inverseImage.map_id _
  refine ⟨X, x, (presheafToSheaf J (Type w)).map η ≫ ε, ?_⟩
  rw [Functor.map_comp]
  change p.inverseImage.map ε (p.presheafStalkFunctor.map η x) = t
  rw [hx]
  exact ConcreteCategory.congr_hom hinv t

/-! ### Clause (2) of the covering condition -/

/-- The image of a morphism of representables under `PointOfTopos.sitePointFiber`, read off
from the factorisation of the morphism through an arbitrary presheaf. -/
theorem sitePointFiber_map_preimage {P : Cᵒᵖ ⥤ Type w} {Z X : C}
    (η : shrinkYoneda.{w}.obj Z ⟶ P) (α : P ⟶ shrinkYoneda.{w}.obj X)
    (z : p.sitePointFiber.obj Z) :
    p.sitePointFiber.map ((fullyFaithfulShrinkYoneda C).preimage (η ≫ α)) z =
      p.presheafStalkFunctor.map α (p.presheafStalkFunctor.map η z) := by
  change p.presheafStalkFunctor.map
    (shrinkYoneda.{w}.map ((fullyFaithfulShrinkYoneda C).preimage (η ≫ α))) z = _
  rw [(fullyFaithfulShrinkYoneda C).map_preimage, Functor.map_comp]
  rfl

/-- **The covering condition for `PointOfTopos.sitePointFiber`.** If `R` is a covering sieve of
`X` then every element of `u(X)` is the image of an element of `u(Y)` under some arrow
`f : Y ⟶ X` of `R`.

The inclusion of a covering sieve into the presheaf it is a sieve in becomes an isomorphism
after sheafification (`CategoryTheory.Sieve.W_shrinkFunctor_ι_of_mem`), so it becomes a
bijection after applying `PointOfTopos.presheafStalkFunctor`; the key covering lemma then
produces the arrow out of a representable, which is an arrow of `C` because `shrinkYoneda` is
fully faithful, and it lies in `R` because it factors through the sieve. -/
theorem sitePointFiber_jointly_surjective {X : C} (R : Sieve X) (hR : R ∈ J X)
    (x : p.sitePointFiber.obj X) :
    ∃ (Y : C) (f : Y ⟶ X) (_ : R f) (y : p.sitePointFiber.obj Y),
      p.sitePointFiber.map f y = x := by
  have hsh : IsIso ((presheafToSheaf J (Type w)).map (Sieve.shrinkFunctor.{w} R).ι) :=
    (J.W_iff _).1 (Sieve.W_shrinkFunctor_ι_of_mem J R hR)
  have hiso : IsIso (p.presheafStalkFunctor.map (Sieve.shrinkFunctor.{w} R).ι) := by
    dsimp only [presheafStalkFunctor, Functor.comp_map]
    infer_instance
  obtain ⟨y₀, hy₀⟩ := ((isIso_iff_bijective
    (p.presheafStalkFunctor.map (Sieve.shrinkFunctor.{w} R).ι)).1 hiso).2 x
  obtain ⟨Z, η, z, hz⟩ := p.exists_sitePointFiber_presheafStalk
    (Sieve.shrinkFunctor.{w} R).toFunctor y₀
  refine ⟨Z, (fullyFaithfulShrinkYoneda C).preimage (η ≫ (Sieve.shrinkFunctor.{w} R).ι), ?_, z,
    ?_⟩
  · have h₁ : shrinkYonedaObjObjEquiv.symm
        ((fullyFaithfulShrinkYoneda C).preimage (η ≫ (Sieve.shrinkFunctor.{w} R).ι)) =
        (shrinkYonedaEquiv η).1 := by
      have h := congrArg shrinkYonedaEquiv
        ((fullyFaithfulShrinkYoneda C).map_preimage (η ≫ (Sieve.shrinkFunctor.{w} R).ι))
      rw [shrinkYonedaEquiv_shrinkYoneda_map, shrinkYonedaEquiv_comp] at h
      simpa using h
    have h₂ := (shrinkYonedaEquiv η).2
    rw [← h₁] at h₂
    simpa using h₂
  · rw [p.sitePointFiber_map_preimage, hz, hy₀]

/-! ### The category of elements of the fibre functor is cofiltered -/

omit [LocallySmall.{w} C] in
/-- The category of elements of `PointOfTopos.presheafStalkFunctor` is cofiltered: the category
of presheaves has finite limits and `PointOfTopos.presheafStalkFunctor` preserves them. -/
theorem isCofiltered_presheafStalkFunctor_elements :
    IsCofiltered p.presheafStalkFunctor.Elements :=
  p.presheafStalkFunctor.isCofiltered_elements

/-- **The category of elements of `u` is cofiltered.** This is the substantive half of the
verification that `PointOfTopos.sitePointFiber` is the fibre functor of a point of the site.

A pair of objects of `u.Elements`, or a pair of parallel arrows between two of them, is first
viewed in the category of elements of `PointOfTopos.presheafStalkFunctor`, which is cofiltered
because that functor is left exact; the cone object produced there is an element of the stalk
of some presheaf, and the key covering lemma replaces that presheaf by a representable, which
is an object of `C` because `shrinkYoneda` is fully faithful. -/
@[sga "4 IV 6.8.2" "Vois_C(p)ᵒᵖ is filtered",
  sga "4 IV 6.8.5" "partial",
  sga "4 VIII 7.9.1" "partial"]
theorem isCofiltered_sitePointFiber_elements : IsCofiltered p.sitePointFiber.Elements := by
  have hcof := p.isCofiltered_presheafStalkFunctor_elements
  have key : ∀ (W : p.presheafStalkFunctor.Elements),
      ∃ (Z : C) (z : p.sitePointFiber.obj Z) (η : shrinkYoneda.{w}.obj Z ⟶ W.1),
        p.presheafStalkFunctor.map η z = W.2 := by
    rintro @⟨P, t⟩
    obtain ⟨Z, η, z, hz⟩ := p.exists_sitePointFiber_presheafStalk P t
    exact ⟨Z, z, η, hz⟩
  refine { cone_objs := ?_, cone_maps := ?_, nonempty := ?_ }
  · rintro @⟨Xa, xa⟩ @⟨Xb, xb⟩
    obtain ⟨W, φ, ψ, -⟩ := IsCofilteredOrEmpty.cone_objs
      (Functor.elementsMk p.presheafStalkFunctor (shrinkYoneda.{w}.obj Xa) xa)
      (Functor.elementsMk p.presheafStalkFunctor (shrinkYoneda.{w}.obj Xb) xb)
    obtain ⟨Z, z, η, hη⟩ := key W
    exact ⟨Functor.elementsMk _ Z z,
      ⟨(fullyFaithfulShrinkYoneda C).preimage (η ≫ φ.1),
        by rw [p.sitePointFiber_map_preimage, hη]; exact φ.2⟩,
      ⟨(fullyFaithfulShrinkYoneda C).preimage (η ≫ ψ.1),
        by rw [p.sitePointFiber_map_preimage, hη]; exact ψ.2⟩, trivial⟩
  · rintro @⟨Xa, xa⟩ @⟨Xb, xb⟩ φ ψ
    obtain ⟨W, h, hh⟩ := IsCofilteredOrEmpty.cone_maps
      (show Functor.elementsMk p.presheafStalkFunctor (shrinkYoneda.{w}.obj Xa) xa ⟶
          Functor.elementsMk p.presheafStalkFunctor (shrinkYoneda.{w}.obj Xb) xb from
        ⟨shrinkYoneda.{w}.map φ.1, φ.2⟩)
      ⟨shrinkYoneda.{w}.map ψ.1, ψ.2⟩
    replace hh : h.hom ≫ shrinkYoneda.{w}.map φ.hom = h.hom ≫ shrinkYoneda.{w}.map ψ.hom :=
      congrArg Functor.Elements.Hom.hom hh
    obtain ⟨Z, z, η, hη⟩ := key W
    refine ⟨Functor.elementsMk _ Z z,
      ⟨(fullyFaithfulShrinkYoneda C).preimage (η ≫ h.1),
        by rw [p.sitePointFiber_map_preimage, hη]; exact h.2⟩, ?_⟩
    refine Functor.Elements.hom_ext (shrinkYoneda.{w}.map_injective ?_)
    change shrinkYoneda.{w}.map ((fullyFaithfulShrinkYoneda C).preimage (η ≫ h.1) ≫ φ.1) =
      shrinkYoneda.{w}.map ((fullyFaithfulShrinkYoneda C).preimage (η ≫ h.1) ≫ ψ.1)
    rw [Functor.map_comp, Functor.map_comp, (fullyFaithfulShrinkYoneda C).map_preimage,
      Category.assoc, Category.assoc]
    exact congrArg (fun g ↦ η ≫ g) hh
  · obtain ⟨W⟩ := hcof.nonempty
    obtain ⟨Z, z, -, -⟩ := key W
    exact ⟨Functor.elementsMk _ Z z⟩

/-- The smallness side condition on the category of elements of `u`: for an essentially
`w`-small category `C` the category of elements of a functor `C ⥤ Type w` is initially
`w`-small, which is
`CategoryTheory.CategoryOfElements.initiallySmall_elements_of_essentiallySmall`.

Essential smallness, rather than smallness, is what the geometry has: the small étale site of a
scheme has objects in `Type (u + 1)` and morphisms in `Type u`, so it is `EssentiallySmall.{u}`
but not `Small.{u}`.  Asking only for the former is what makes the reconstruction below available
at coefficients `Type u` — the universe the representable sheaves and the structure sheaf live
at — and not merely at `Type (u + 1)`. -/
theorem initiallySmall_sitePointFiber_elements_of_essentiallySmall [EssentiallySmall.{w} C] :
    InitiallySmall.{w} p.sitePointFiber.Elements :=
  CategoryOfElements.initiallySmall_elements_of_essentiallySmall _

/-! ### The point of the site attached to a point of the topos -/

/-- **Stacks 00YA (2), the construction.** The point of the site `(C, J)` attached to a point
`p` of the topos `Sh(C, J)`: its fibre functor is `u : X ↦ p⁻¹(h_X^#)`.

The three conditions on a point of a site are `PointOfTopos.isCofiltered_sitePointFiber_elements`,
`PointOfTopos.initiallySmall_sitePointFiber_elements_of_essentiallySmall` and
`PointOfTopos.sitePointFiber_jointly_surjective`. -/
noncomputable def sitePointOfEssentiallySmall [EssentiallySmall.{w} C] : J.Point.{w} where
  fiber := p.sitePointFiber
  isCofiltered := p.isCofiltered_sitePointFiber_elements
  initiallySmall := p.initiallySmall_sitePointFiber_elements_of_essentiallySmall
  jointly_surjective R hR x := p.sitePointFiber_jointly_surjective R hR x

/-- The fibre functor of the point of the site attached to a point of the topos is
`u : X ↦ p⁻¹(h_X^#)`. -/
@[simp]
theorem sitePointOfEssentiallySmall_fiber [EssentiallySmall.{w} C] :
    p.sitePointOfEssentiallySmall.fiber = p.sitePointFiber :=
  rfl

/-! ### Comparing the two fibre functors on presheaves -/

/-- For `x` an element of `u(X) = p⁻¹(h_X^#)`, the map `P(X) ⟶ p⁻¹(P^#)` sending a section `z`
of a presheaf `P` over `X` to the image of `x` under the morphism `h_X ⟶ P` that Yoneda's
lemma attaches to `z`. These maps are the components of the comparison transformation
`PointOfTopos.presheafFiberComparison`. -/
noncomputable def presheafStalkSection {X : C} (x : p.sitePointFiber.obj X) (P : Cᵒᵖ ⥤ Type w) :
    P.obj (op X) ⟶ p.presheafStalkFunctor.obj P :=
  ↾fun z ↦ p.presheafStalkFunctor.map (shrinkYonedaEquiv.symm z) x

/-- The value of `PointOfTopos.presheafStalkSection` at a section of the presheaf. -/
@[simp]
theorem presheafStalkSection_apply {X : C} (x : p.sitePointFiber.obj X) (P : Cᵒᵖ ⥤ Type w)
    (z : P.obj (op X)) :
    p.presheafStalkSection x P z = p.presheafStalkFunctor.map (shrinkYonedaEquiv.symm z) x :=
  rfl

/-- `PointOfTopos.presheafStalkSection` is compatible with restriction along a morphism of
`C`. -/
theorem map_op_comp_presheafStalkSection {X Y : C} (f : X ⟶ Y) (x : p.sitePointFiber.obj X)
    (P : Cᵒᵖ ⥤ Type w) :
    P.map f.op ≫ p.presheafStalkSection x P =
      p.presheafStalkSection (p.sitePointFiber.map f x) P := by
  ext z
  change p.presheafStalkFunctor.map (shrinkYonedaEquiv.symm (P.map f.op z)) x =
    p.presheafStalkFunctor.map (shrinkYonedaEquiv.symm z) (p.sitePointFiber.map f x)
  rw [shrinkYonedaEquiv_symm_map, Functor.map_comp]
  rfl

/-- `PointOfTopos.presheafStalkSection` is natural in the presheaf. -/
theorem presheafStalkSection_comp_map {X : C} (x : p.sitePointFiber.obj X)
    {P Q : Cᵒᵖ ⥤ Type w} (g : P ⟶ Q) :
    p.presheafStalkSection x P ≫ p.presheafStalkFunctor.map g =
      g.app (op X) ≫ p.presheafStalkSection x Q := by
  ext z
  change p.presheafStalkFunctor.map g
      (p.presheafStalkFunctor.map (shrinkYonedaEquiv.symm z) x) =
    p.presheafStalkFunctor.map (shrinkYonedaEquiv.symm (g.app (op X) z)) x
  rw [← Presheaf.shrinkYonedaEquiv_symm_comp_eq, Functor.map_comp]
  rfl

section EssentiallySmallSite

variable [EssentiallySmall.{w} C]

/-- The comparison transformation from the fibre functor on presheaves of the point
`PointOfTopos.sitePointOfEssentiallySmall` of the site to the stalk-of-the-sheafification functor
`PointOfTopos.presheafStalkFunctor` of the point `p` of the topos.

It is an isomorphism (`PointOfTopos.isIso_presheafFiberComparison_app`), which is what
identifies the two stalk functors. -/
noncomputable def presheafFiberComparisonAppOfEssentiallySmall (P : Cᵒᵖ ⥤ Type w) :
    (p.sitePointOfEssentiallySmall.presheafFiber (A := Type w)).obj P ⟶
      p.presheafStalkFunctor.obj P :=
  p.sitePointOfEssentiallySmall.presheafFiberDesc (fun _ x ↦ p.presheafStalkSection x P)
    (fun _ _ f x ↦ p.map_op_comp_presheafStalkSection f x P)

/-- The component of the comparison transformation composed with the canonical map
`P(X) ⟶ Φ.presheafFiber.obj P` is `PointOfTopos.presheafStalkSection`. -/
@[reassoc (attr := simp)]
theorem toPresheafFiber_presheafFiberComparisonAppOfEssentiallySmall (P : Cᵒᵖ ⥤ Type w) (X : C)
    (x : p.sitePointOfEssentiallySmall.fiber.obj X) :
    p.sitePointOfEssentiallySmall.toPresheafFiber X x P ≫
        p.presheafFiberComparisonAppOfEssentiallySmall P =
      p.presheafStalkSection x P :=
  p.sitePointOfEssentiallySmall.toPresheafFiber_presheafFiberDesc _ _ X x

/-- The comparison transformation from the fibre functor on presheaves of the point
`PointOfTopos.sitePointOfEssentiallySmall` of the site to the stalk-of-the-sheafification
functor of the point `p` of the topos, assembled from
`PointOfTopos.presheafFiberComparisonAppOfEssentiallySmall`. -/
noncomputable def presheafFiberComparisonOfEssentiallySmall :
    p.sitePointOfEssentiallySmall.presheafFiber (A := Type w) ⟶ p.presheafStalkFunctor where
  app := p.presheafFiberComparisonAppOfEssentiallySmall
  naturality P Q g := p.sitePointOfEssentiallySmall.presheafFiber_hom_ext fun X x ↦ by
    rw [← Category.assoc, GrothendieckTopology.Point.toPresheafFiber_naturality,
      Category.assoc, p.toPresheafFiber_presheafFiberComparisonAppOfEssentiallySmall,
      ← Category.assoc,
      p.toPresheafFiber_presheafFiberComparisonAppOfEssentiallySmall]
    exact (p.presheafStalkSection_comp_map x g).symm

/-- The components of the comparison transformation. -/
@[simp]
theorem presheafFiberComparisonOfEssentiallySmall_app (P : Cᵒᵖ ⥤ Type w) :
    p.presheafFiberComparisonOfEssentiallySmall.app P =
      p.presheafFiberComparisonAppOfEssentiallySmall P :=
  rfl

/-- The value of the comparison transformation on the canonical maps
`P(X) ⟶ Φ.presheafFiber.obj P` which present the fibre of a presheaf as a colimit. -/
@[simp]
theorem presheafFiberComparisonAppOfEssentiallySmall_toPresheafFiber (P : Cᵒᵖ ⥤ Type w) {X : C}
    (x : p.sitePointOfEssentiallySmall.fiber.obj X) (z : P.obj (op X)) :
    p.presheafFiberComparisonAppOfEssentiallySmall P
        (p.sitePointOfEssentiallySmall.toPresheafFiber X x P z) =
      p.presheafStalkFunctor.map (shrinkYonedaEquiv.symm z) x :=
  ConcreteCategory.congr_hom
    (p.toPresheafFiber_presheafFiberComparisonAppOfEssentiallySmall P X x) z

/-- **The comparison transformation is an isomorphism at a representable presheaf.** Composed
with Mathlib's isomorphism `shrinkYoneda ⋙ Φ.presheafFiber ≅ Φ.fiber` it is the identity: both
are determined by the image of the identity of `X` under the canonical map
`h_X(X) ⟶ Φ.presheafFiber.obj (h_X)`. -/
instance isIso_presheafFiberComparisonAppOfEssentiallySmall_shrinkYoneda_obj (Y : C) :
    IsIso (p.presheafFiberComparisonAppOfEssentiallySmall (shrinkYoneda.{w}.obj Y)) := by
  have h : p.sitePointOfEssentiallySmall.shrinkYonedaCompPresheafFiberIso.inv.app Y ≫
      p.presheafFiberComparisonAppOfEssentiallySmall (shrinkYoneda.{w}.obj Y) =
      𝟙 (p.presheafStalkFunctor.obj (shrinkYoneda.{w}.obj Y)) := by
    ext x
    change p.presheafFiberComparisonAppOfEssentiallySmall (shrinkYoneda.{w}.obj Y)
      (p.sitePointOfEssentiallySmall.shrinkYonedaCompPresheafFiberIso.inv.app Y x) = x
    rw [GrothendieckTopology.Point.shrinkYonedaCompPresheafFiberIso_inv_app_toPresheafFiber,
      p.presheafFiberComparisonAppOfEssentiallySmall_toPresheafFiber,
      show shrinkYonedaEquiv.symm (shrinkYonedaObjObjEquiv.symm (𝟙 Y)) = 𝟙 _ from by
        rw [← shrinkYonedaEquiv_shrinkYoneda_map (𝟙 Y), Equiv.symm_apply_apply,
          shrinkYoneda.{w}.map_id],
      p.presheafStalkFunctor.map_id]
    rfl
  have h2 : IsIso (p.sitePointOfEssentiallySmall.shrinkYonedaCompPresheafFiberIso.inv.app Y ≫
      p.presheafFiberComparisonAppOfEssentiallySmall (shrinkYoneda.{w}.obj Y)) := by
    rw [h]
    exact IsIso.id _
  exact IsIso.of_isIso_comp_left
    (p.sitePointOfEssentiallySmall.shrinkYonedaCompPresheafFiberIso.inv.app Y) _

/-- The comparison transformation on the diagram of representables indexed by the category of
elements of a presheaf, as an isomorphism of diagrams. -/
noncomputable def presheafFiberComparisonDiagramIsoOfEssentiallySmall (P : Cᵒᵖ ⥤ Type w) :
    ((Functor.Elements.π P).leftOp ⋙ shrinkYoneda.{w}) ⋙
        p.sitePointOfEssentiallySmall.presheafFiber (A := Type w) ≅
      ((Functor.Elements.π P).leftOp ⋙ shrinkYoneda.{w}) ⋙ p.presheafStalkFunctor :=
  NatIso.ofComponents
    (fun j ↦ @asIso _ _ _ _ _ (p.isIso_presheafFiberComparisonAppOfEssentiallySmall_shrinkYoneda_obj
      ((Functor.Elements.π P).leftOp.obj j)))
    fun _ ↦ p.presheafFiberComparisonOfEssentiallySmall.naturality _

/-- **The comparison transformation is an isomorphism at every presheaf.** Both functors
preserve all colimits — they are left adjoints — both agree on representables, and every
presheaf is a colimit of representables
(`CategoryTheory.Presheaf.shrinkColimitOfRepresentable`). -/
instance isIso_presheafFiberComparisonAppOfEssentiallySmall (P : Cᵒᵖ ⥤ Type w) :
    IsIso (p.presheafFiberComparisonAppOfEssentiallySmall P) := by
  have h₀ : PreservesColimitsOfSize.{v, max u w}
      (p.sitePointOfEssentiallySmall.presheafFiber (A := Type w)) :=
    p.sitePointOfEssentiallySmall.skyscraperPresheafAdjunction.leftAdjoint_preservesColimits
  have h₁ : PreservesColimitsOfSize.{v, max u w} p.presheafStalkFunctor :=
    p.presheafStalkAdjunction.leftAdjoint_preservesColimits
  have hA := isColimitOfPreserves (p.sitePointOfEssentiallySmall.presheafFiber (A := Type w))
    (Presheaf.shrinkColimitOfRepresentable P)
  have hB' := (IsColimit.precomposeHomEquiv
    (p.presheafFiberComparisonDiagramIsoOfEssentiallySmall P)
    (p.presheafStalkFunctor.mapCocone (Presheaf.shrinkCoconeOfRepresentable P))).symm
      (isColimitOfPreserves p.presheafStalkFunctor
        (Presheaf.shrinkColimitOfRepresentable P))
  let hcm : p.sitePointOfEssentiallySmall.presheafFiber.mapCocone
        (Presheaf.shrinkCoconeOfRepresentable P) ⟶
      (Cocone.precompose (p.presheafFiberComparisonDiagramIsoOfEssentiallySmall P).hom).obj
        (p.presheafStalkFunctor.mapCocone (Presheaf.shrinkCoconeOfRepresentable P)) :=
    { hom := p.presheafFiberComparisonAppOfEssentiallySmall P
      w := fun _ ↦ p.presheafFiberComparisonOfEssentiallySmall.naturality _ }
  have : IsIso hcm := IsColimit.hom_isIso hA hB' hcm
  exact (Cocone.forget _).map_isIso hcm

/-- The fibre functor on presheaves of the point `PointOfTopos.sitePointOfEssentiallySmall` of
the site is the stalk-of-the-sheafification functor of the point `p` of the topos. -/
@[sga "4 IV 6.8.2" "more general"]
noncomputable def presheafFiberIsoOfEssentiallySmall :
    p.sitePointOfEssentiallySmall.presheafFiber (A := Type w) ≅ p.presheafStalkFunctor :=
  NatIso.ofComponents (fun P ↦ asIso (p.presheafFiberComparisonAppOfEssentiallySmall P))
    fun g ↦ p.presheafFiberComparisonOfEssentiallySmall.naturality g

/-! ### Stacks 00YA (2) -/

/-- The stalk functor of the point `PointOfTopos.sitePointOfEssentiallySmall` of the site is the
inverse image functor of the given point `p` of the topos.

The comparison `PointOfTopos.presheafFiberIsoOfEssentiallySmall` identifies the two fibre
functors on presheaves; restricting along `sheafToPresheaf` gives `Φ.sheafFiber` on the left
and, on the right, the composite `sheafToPresheaf ⋙ presheafToSheaf ⋙ p⁻¹`, which is `p⁻¹`
because the counit of the sheafification adjunction is an isomorphism. -/
@[sga "4 IV 6.8.2" "(6.8.3), special case"]
noncomputable def sheafFiberIsoInverseImageOfEssentiallySmall :
    p.sitePointOfEssentiallySmall.sheafFiber (A := Type w) ≅ p.inverseImage :=
  have : IsIso ((sheafificationAdjunction J (Type w)).counit) := NatIso.isIso_of_isIso_app _
  Functor.isoWhiskerLeft (sheafToPresheaf J (Type w)) p.presheafFiberIsoOfEssentiallySmall ≪≫
    Functor.isoWhiskerRight (asIso (sheafificationAdjunction J (Type w)).counit)
      p.inverseImage ≪≫ p.inverseImage.leftUnitor

/-- **Stacks 00YA (2).** Every point of the topos `Sh(C, J)` arises from a point of the site
`(C, J)`: for a point `p` of the topos there is a point `Φ` of the site whose stalk functor
`Φ.sheafFiber` is isomorphic to `p⁻¹`.

The point of the site is `PointOfTopos.sitePointOfEssentiallySmall`, whose fibre functor is
`u : X ↦ p⁻¹(h_X^#)`, and the isomorphism is
`PointOfTopos.sheafFiberIsoInverseImageOfEssentiallySmall`. -/
theorem exists_sitePoint_of_essentiallySmall :
    ∃ Φ : J.Point.{w}, Nonempty (p.inverseImage ≅ Φ.sheafFiber) :=
  ⟨p.sitePointOfEssentiallySmall, ⟨p.sheafFiberIsoInverseImageOfEssentiallySmall.symm⟩⟩

end EssentiallySmallSite

/-! ### The reconstruction at a `w`-small site

A `w`-small, locally `w`-small category is essentially `w`-small
(`CategoryTheory.essentiallySmall_of_small_of_locallySmall`), so each statement of this section is
the one above it instantiated at that instance.  The two are kept apart because `Small.{w} C` is
the shape in which the earlier consumers of Stacks 00YA (2) ask for the reconstruction. -/

/-- The smallness side condition on the category of elements of `u`: for a `w`-small, locally
`w`-small category `C` the category of elements of a functor `C ⥤ Type w` is essentially
`w`-small, hence initially `w`-small. -/
theorem initiallySmall_sitePointFiber_elements [Small.{w} C] :
    InitiallySmall.{w} p.sitePointFiber.Elements :=
  p.initiallySmall_sitePointFiber_elements_of_essentiallySmall

/-- **Stacks 00YA (2), the construction.** The point of the site `(C, J)` attached to a point
`p` of the topos `Sh(C, J)`: its fibre functor is `u : X ↦ p⁻¹(h_X^#)`.

The three conditions on a point of a site are `PointOfTopos.isCofiltered_sitePointFiber_elements`,
`PointOfTopos.initiallySmall_sitePointFiber_elements` and
`PointOfTopos.sitePointFiber_jointly_surjective`. -/
noncomputable def sitePoint [Small.{w} C] : J.Point.{w} :=
  p.sitePointOfEssentiallySmall

/-- The fibre functor of the point of the site attached to a point of the topos is
`u : X ↦ p⁻¹(h_X^#)`. -/
@[simp]
theorem sitePoint_fiber [Small.{w} C] : p.sitePoint.fiber = p.sitePointFiber :=
  rfl

section Small

variable [Small.{w} C]

/-- The comparison transformation from the fibre functor on presheaves of the point
`PointOfTopos.sitePoint` of the site to the stalk-of-the-sheafification functor
`PointOfTopos.presheafStalkFunctor` of the point `p` of the topos.

It is an isomorphism (`PointOfTopos.isIso_presheafFiberComparisonApp`), which is what
identifies the two stalk functors. -/
noncomputable def presheafFiberComparisonApp (P : Cᵒᵖ ⥤ Type w) :
    (p.sitePoint.presheafFiber (A := Type w)).obj P ⟶ p.presheafStalkFunctor.obj P :=
  p.presheafFiberComparisonAppOfEssentiallySmall P

/-- The component of the comparison transformation composed with the canonical map
`P(X) ⟶ Φ.presheafFiber.obj P` is `PointOfTopos.presheafStalkSection`. -/
@[reassoc (attr := simp)]
theorem toPresheafFiber_presheafFiberComparisonApp (P : Cᵒᵖ ⥤ Type w) (X : C)
    (x : p.sitePoint.fiber.obj X) :
    p.sitePoint.toPresheafFiber X x P ≫ p.presheafFiberComparisonApp P =
      p.presheafStalkSection x P :=
  p.toPresheafFiber_presheafFiberComparisonAppOfEssentiallySmall P X x

/-- The comparison transformation from the fibre functor on presheaves of the point
`PointOfTopos.sitePoint` of the site to the stalk-of-the-sheafification functor of the point
`p` of the topos, assembled from `PointOfTopos.presheafFiberComparisonApp`. -/
noncomputable def presheafFiberComparison :
    p.sitePoint.presheafFiber (A := Type w) ⟶ p.presheafStalkFunctor :=
  p.presheafFiberComparisonOfEssentiallySmall

/-- The components of the comparison transformation. -/
@[simp]
theorem presheafFiberComparison_app (P : Cᵒᵖ ⥤ Type w) :
    p.presheafFiberComparison.app P = p.presheafFiberComparisonApp P :=
  rfl

/-- The value of the comparison transformation on the canonical maps
`P(X) ⟶ Φ.presheafFiber.obj P` which present the fibre of a presheaf as a colimit. -/
@[simp]
theorem presheafFiberComparisonApp_toPresheafFiber (P : Cᵒᵖ ⥤ Type w) {X : C}
    (x : p.sitePoint.fiber.obj X) (z : P.obj (op X)) :
    p.presheafFiberComparisonApp P (p.sitePoint.toPresheafFiber X x P z) =
      p.presheafStalkFunctor.map (shrinkYonedaEquiv.symm z) x :=
  p.presheafFiberComparisonAppOfEssentiallySmall_toPresheafFiber P x z

/-- **The comparison transformation is an isomorphism at a representable presheaf.** Composed
with Mathlib's isomorphism `shrinkYoneda ⋙ Φ.presheafFiber ≅ Φ.fiber` it is the identity: both
are determined by the image of the identity of `X` under the canonical map
`h_X(X) ⟶ Φ.presheafFiber.obj (h_X)`. -/
instance isIso_presheafFiberComparisonApp_shrinkYoneda_obj (Y : C) :
    IsIso (p.presheafFiberComparisonApp (shrinkYoneda.{w}.obj Y)) :=
  p.isIso_presheafFiberComparisonAppOfEssentiallySmall_shrinkYoneda_obj Y

/-- The comparison transformation on the diagram of representables indexed by the category of
elements of a presheaf, as an isomorphism of diagrams. -/
noncomputable def presheafFiberComparisonDiagramIso (P : Cᵒᵖ ⥤ Type w) :
    ((Functor.Elements.π P).leftOp ⋙ shrinkYoneda.{w}) ⋙
        p.sitePoint.presheafFiber (A := Type w) ≅
      ((Functor.Elements.π P).leftOp ⋙ shrinkYoneda.{w}) ⋙ p.presheafStalkFunctor :=
  p.presheafFiberComparisonDiagramIsoOfEssentiallySmall P

/-- **The comparison transformation is an isomorphism at every presheaf.** Both functors
preserve all colimits — they are left adjoints — both agree on representables, and every
presheaf is a colimit of representables
(`CategoryTheory.Presheaf.shrinkColimitOfRepresentable`). -/
instance isIso_presheafFiberComparisonApp (P : Cᵒᵖ ⥤ Type w) :
    IsIso (p.presheafFiberComparisonApp P) :=
  p.isIso_presheafFiberComparisonAppOfEssentiallySmall P

/-- The fibre functor on presheaves of the point `PointOfTopos.sitePoint` of the site is the
stalk-of-the-sheafification functor of the point `p` of the topos. -/
@[sga "4 IV 6.8.2" "more general"]
noncomputable def presheafFiberIso :
    p.sitePoint.presheafFiber (A := Type w) ≅ p.presheafStalkFunctor :=
  p.presheafFiberIsoOfEssentiallySmall

/-- The stalk functor of the point `PointOfTopos.sitePoint` of the site is the inverse image
functor of the given point `p` of the topos.

The comparison `PointOfTopos.presheafFiberIso` identifies the two fibre functors on presheaves;
restricting along `sheafToPresheaf` gives `Φ.sheafFiber` on the left and, on the right, the
composite `sheafToPresheaf ⋙ presheafToSheaf ⋙ p⁻¹`, which is `p⁻¹` because the counit of the
sheafification adjunction is an isomorphism. -/
@[sga "4 IV 6.8.2" "(6.8.3), special case"]
noncomputable def sheafFiberIsoInverseImage :
    p.sitePoint.sheafFiber (A := Type w) ≅ p.inverseImage :=
  p.sheafFiberIsoInverseImageOfEssentiallySmall

/-- **Stacks 00YA (2).** Every point of the topos `Sh(C, J)` arises from a point of the site
`(C, J)`: for a point `p` of the topos there is a point `Φ` of the site whose stalk functor
`Φ.sheafFiber` is isomorphic to `p⁻¹`.

The point of the site is `PointOfTopos.sitePoint`, whose fibre functor is `u : X ↦ p⁻¹(h_X^#)`,
and the isomorphism is `PointOfTopos.sheafFiberIsoInverseImage`. -/
theorem exists_sitePoint :
    ∃ Φ : J.Point.{w}, Nonempty (p.inverseImage ≅ Φ.sheafFiber) :=
  ⟨p.sitePoint, ⟨p.sheafFiberIsoInverseImage.symm⟩⟩

end Small

end PointOfTopos
