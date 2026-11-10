module

public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.InducedTopology
public import StacksFrontier.CategoryTheory.Sites.SubsingletonPresheaf

/-!
# The slice of a topos at a subterminal sheaf: the presheaf layer

Let `F` be a presheaf of sets on a category `C` whose values are subsingletons, and let
`j : D ⥤ C` be a fully faithful functor whose essential image is the *support* of `F`, the
objects over which `F` has a section.  Since `F` is a presheaf, that support is automatically
closed under morphisms into it, so a presheaf `G` equipped with a map `G ⟶ F` is concentrated
on the image of `j` in a strong sense: it has no sections at all outside it.

This file contains the two consequences at the level of presheaves, which is where all the
work is: a morphism out of such a `G` is determined by its restriction along `j`, and every
morphism defined on that restriction extends.  It also builds, for a presheaf `H` on `D`, its
*extension by the empty set* to `C`, whose sections over `U` are the pairs of a section of `F`
over `U` — of which there is at most one — and a section of `H` over the object of `D` chosen
above `U`.

This is the substitute, available in any coefficient universe, for the fibre functor of
[Stacks, Tag 0791].  The fibre `{t ∈ G(U) | φ(t) = s}` of a map `φ : G ⟶ F` over a section `s`
of a subterminal `F` is all of `G(U)`, so the fibre functor is plain restriction; Mathlib's
`CategoryTheory.OverPresheafAux`, which 0791 uses and which exists only for coefficients in the
hom universe of the site, is not needed.

## Main definitions

* `CategoryTheory.Stacks.Topos.Subterminal.imgObj` and `imgIso` — a choice of object of `D`
  realizing an object in the essential image of `j`, and the isomorphism realizing it.  Both
  are independent of the proof of membership, the essential image being a proposition.
* `CategoryTheory.Stacks.Topos.Subterminal.extendNatTrans` — the extension of a morphism
  defined over the image of `j`.
* `CategoryTheory.Stacks.Topos.Subterminal.extend` — extension by the empty set.
* `CategoryTheory.Stacks.Topos.Subterminal.srcIsoSelf` — over the image of an object of `D`,
  the chosen object is that object again.
* `CategoryTheory.Stacks.Topos.Subterminal.sectionOfEssImage` — the section of `F` over an
  object in the essential image of `j`.

## Main results

* `CategoryTheory.Stacks.Topos.Subterminal.natTrans_ext_of_essImage` — a morphism out of a
  presheaf supported on the essential image of `j` is determined by its restriction.
* `CategoryTheory.Stacks.Topos.Subterminal.whiskerLeft_extendNatTrans` — the extension
  restricts back to what it extends.
* `CategoryTheory.Stacks.Topos.Subterminal.essImage_of_hom` — the essential image of `j` is
  closed under morphisms into it.
* `CategoryTheory.Stacks.Topos.Subterminal.functorPushforward_functorPullback_of_essImage` —
  the sieves of `D` and the sieves of `C` on an object of the image correspond.

## Implementation notes

`srcObj` and `srcIso` are `@[reducible]`.  They are applied to a *proof* that an object lies in
the essential image, so proof irrelevance makes them independent of the section chosen; marking
them reducible is what makes that independence visible to `rw` and `simp`, which work at
`instances` transparency.  Without it the sheaf-theoretic consequences do not go through.

## References

* [Stacks Project, Tag 0791](https://stacks.math.columbia.edu/tag/0791)
-/

@[expose] public section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Stacks.Topos.Subterminal

open Opposite Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : Cᵒᵖ ⥤ Type w} {j : D ⥤ C}

/-- A choice of object of `D` whose image realizes an object in the essential image of `j`.
It does not depend on the proof, the essential image being a proposition. -/
noncomputable def imgObj {U : C} (h : j.essImage U) : D := h.choose

/-- The isomorphism realizing `imgObj h`. -/
noncomputable def imgIso {U : C} (h : j.essImage U) : j.obj (imgObj h) ≅ U := h.choose_spec.some

section Presheaf

variable {G G' : Cᵒᵖ ⥤ Type w}

/-- Two maps out of a presheaf supported on the essential image of `j` agree as soon as they
agree on the image of `j`: every section is transported from one over an object of that image. -/
theorem natTrans_ext_of_essImage (hG : ∀ {U : C}, G.obj (op U) → j.essImage U) {α β : G ⟶ G'}
    (hres : ∀ B : D, α.app (op (j.obj B)) = β.app (op (j.obj B))) : α = β := by
  ext ⟨U⟩ t
  obtain ⟨B, ⟨e⟩⟩ := hG t
  change α.app (op U) t = β.app (op U) t
  have ht : G.map e.inv.op (G.map e.hom.op t) = t := by
    rw [← Functor.map_comp_apply, ← op_comp, e.inv_hom_id, op_id,
      Functor.map_id_apply]
  have h1 := NatTrans.naturality_apply α e.inv.op (G.map e.hom.op t)
  have h2 := NatTrans.naturality_apply β e.inv.op (G.map e.hom.op t)
  rw [ht] at h1 h2
  rw [h1, h2, hres B]

variable (G G')

/-- The value at `U` of the extension of `γ`, defined over the image of `j`, to a presheaf
supported on the essential image of `j`: transport the section to the chosen object of `D` over
`U`, apply `γ` there, and transport back. -/
noncomputable def extendApp (hG : ∀ U : Cᵒᵖ, G.obj U → j.essImage U.unop)
    (γ : j.op ⋙ G ⟶ j.op ⋙ G') (U : Cᵒᵖ) (t : G.obj U) : G'.obj U :=
  G'.map (imgIso (hG U t)).inv.op
    (γ.app (op (imgObj (hG U t))) (G.map (imgIso (hG U t)).hom.op t))

/-- Naturality of `γ` transported along isomorphisms `e`, `e'` and a morphism `f` of `C` that
corresponds to a morphism `k` of `D`. -/
private theorem transport_naturality (γ : j.op ⋙ G ⟶ j.op ⋙ G') {U V : Cᵒᵖ} (f : U ⟶ V)
    {B B' : D} (e : j.obj B ≅ U.unop) (e' : j.obj B' ≅ V.unop) (k : B' ⟶ B)
    (hk : j.map k = e'.hom ≫ f.unop ≫ e.inv) (t : G.obj U) :
    G'.map e'.inv.op (γ.app (op B') (G.map e'.hom.op (G.map f t))) =
      G'.map f (G'.map e.inv.op (γ.app (op B) (G.map e.hom.op t))) := by
  have hsrcMor : (j.map k ≫ e.hom).op = f ≫ e'.hom.op :=
    Quiver.Hom.unop_inj (by rw [hk]; simp)
  have htgtMor : (e'.inv ≫ j.map k).op = e.inv.op ≫ f :=
    Quiver.Hom.unop_inj (by rw [hk]; simp)
  have hnat := NatTrans.naturality_apply γ k.op (G.map e.hom.op t)
  simp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op] at hnat
  have hsrc : G.map (j.map k).op (G.map e.hom.op t) = G.map e'.hom.op (G.map f t) := by
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, hsrcMor]
  rw [hsrc] at hnat
  rw [hnat, ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp,
    htgtMor]

variable [j.Full] [j.Faithful]

omit [j.Faithful] in
/-- `extendApp` is natural: the two chosen objects over the source and the target of a morphism
of `C` are joined by the morphism of `D` that full faithfulness extracts from it. -/
theorem extendApp_naturality (hG : ∀ U : Cᵒᵖ, G.obj U → j.essImage U.unop)
    (γ : j.op ⋙ G ⟶ j.op ⋙ G') {U V : Cᵒᵖ} (f : U ⟶ V) (t : G.obj U) :
    extendApp G G' hG γ V (G.map f t) = G'.map f (extendApp G G' hG γ U t) :=
  transport_naturality G G' γ f (imgIso (hG U t)) (imgIso (hG V (G.map f t))) (j.preimage _)
    (j.map_preimage _) t

/-- The extension of `γ` to a morphism of presheaves on all of `C`. -/
@[simps]
noncomputable def extendNatTrans (hG : ∀ U : Cᵒᵖ, G.obj U → j.essImage U.unop)
    (γ : j.op ⋙ G ⟶ j.op ⋙ G') : G ⟶ G' where
  app U := ↾extendApp G G' hG γ U
  naturality _ _ f := by ext t; exact extendApp_naturality G G' hG γ f t

omit [j.Faithful] in
/-- The extension restricts back to `γ` on the image of `j`. -/
theorem whiskerLeft_extendNatTrans (hG : ∀ U : Cᵒᵖ, G.obj U → j.essImage U.unop)
    (γ : j.op ⋙ G ⟶ j.op ⋙ G') :
    Functor.whiskerLeft j.op (extendNatTrans G G' hG γ) = γ := by
  ext ⟨B⟩ t
  have h := hG (op (j.obj B)) t
  simpa [extendApp] using (transport_naturality G G' γ (𝟙 (op (j.obj B))) (imgIso h)
    (Iso.refl _) (j.preimage (imgIso h).inv) (by simp) t).symm

end Presheaf

section Extend

variable (hsupp : ∀ U : C, Nonempty (F.obj (op U)) → j.essImage U) [j.Full] [j.Faithful]

/-- The object of `D` chosen over an object of `C` carrying a section of `F`.  It does not depend
on the section, the essential image being a proposition. -/
@[reducible] noncomputable def srcObj {U : Cᵒᵖ} (s : F.obj U) : D := imgObj (hsupp U.unop ⟨s⟩)

/-- The isomorphism realizing `srcObj`.  Like `srcObj` it is reducible, so that the proof
irrelevance making it independent of the section is visible to `rw` and to `simp`. -/
@[reducible] noncomputable def srcIso {U : Cᵒᵖ} (s : F.obj U) : j.obj (srcObj hsupp s) ≅ U.unop :=
  imgIso (hsupp U.unop ⟨s⟩)

variable [∀ X : Cᵒᵖ, Subsingleton (F.obj X)]

/-- The morphism of `D` that full faithfulness extracts from a morphism of `C`, between the
objects chosen over its target and its source. -/
noncomputable def srcHom {U V : Cᵒᵖ} (f : U ⟶ V) (s : F.obj U) :
    srcObj hsupp (F.map f s) ⟶ srcObj hsupp s :=
  j.preimage ((srcIso hsupp (F.map f s)).hom ≫ f.unop ≫ (srcIso hsupp s).inv)

omit [j.Faithful] [∀ (X : Cᵒᵖ), Subsingleton (F.obj X)] in
/-- The image under `j` of `srcHom hsupp f s` is `f` conjugated by the chosen isomorphisms. -/
theorem map_srcHom {U V : Cᵒᵖ} (f : U ⟶ V) (s : F.obj U) :
    j.map (srcHom hsupp f s) =
      (srcIso hsupp (F.map f s)).hom ≫ f.unop ≫ (srcIso hsupp s).inv :=
  j.map_preimage _

omit [∀ (X : Cᵒᵖ), Subsingleton (F.obj X)] in
/-- `srcHom` sends an identity morphism to the identity. -/
theorem srcHom_id {U : Cᵒᵖ} (s : F.obj U) : srcHom hsupp (𝟙 U) s = 𝟙 _ :=
  j.map_injective <| by
    rw [map_srcHom]
    change (srcIso hsupp s).hom ≫ (𝟙 U).unop ≫ (srcIso hsupp s).inv = j.map (𝟙 (srcObj hsupp s))
    simp

omit [∀ (X : Cᵒᵖ), Subsingleton (F.obj X)] in
/-- `srcHom` is contravariantly compatible with composition. -/
theorem srcHom_comp {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) (s : F.obj U) :
    srcHom hsupp (f ≫ g) s = srcHom hsupp g (F.map f s) ≫ srcHom hsupp f s := by
  apply j.map_injective
  rw [j.map_comp (srcHom hsupp g (F.map f s)) (srcHom hsupp f s),
    map_srcHom hsupp (f ≫ g) s, map_srcHom hsupp g (F.map f s), map_srcHom hsupp f s]
  simp

omit [j.Full] [j.Faithful] in
/-- Two sections of the extension agree as soon as their components over `D` do: the component
in `F` is unique, and the two chosen objects of `D` coincide. -/
theorem extend_ext {H : Dᵒᵖ ⥤ Type w} {U : Cᵒᵖ} {s s' : F.obj U}
    {x : H.obj (op (srcObj hsupp s))} {x' : H.obj (op (srcObj hsupp s'))} (hx : x = x') :
    (⟨s, x⟩ : Σ t : F.obj U, H.obj (op (srcObj hsupp t))) = ⟨s', x'⟩ := by
  obtain rfl := Subsingleton.elim s s'
  exact congrArg _ hx

variable (F j)

/-- **Extension by the empty set.**  The presheaf on `C` whose sections over `U` are the pairs
of a section of `F` over `U` — of which there is at most one — and a section of `H` over the
object of `D` chosen above `U`.  Outside the support of `F` it is empty, and on the image of `j`
it is `H`. -/
noncomputable def extend (H : Dᵒᵖ ⥤ Type w) : Cᵒᵖ ⥤ Type w where
  obj U := Σ s : F.obj U, H.obj (op (srcObj hsupp s))
  map f := ↾fun p ↦ ⟨F.map f p.1, H.map (srcHom hsupp f p.1).op p.2⟩
  map_id U := by
    ext ⟨s, x⟩
    · exact Subsingleton.elim _ _
    · refine heq_of_eq ?_
      change H.map (srcHom hsupp (𝟙 U) s).op x = x
      rw [srcHom_id, op_id]
      simp
  map_comp f g := by
    ext ⟨s, x⟩
    · exact Subsingleton.elim _ _
    · refine heq_of_eq ?_
      change H.map (srcHom hsupp (f ≫ g) s).op x =
        H.map (srcHom hsupp g (F.map f s)).op (H.map (srcHom hsupp f s).op x)
      rw [← Functor.map_comp_apply, ← op_comp, srcHom_comp]

/-- The sections of `extend F j hsupp H` over `U`. -/
theorem extend_obj (H : Dᵒᵖ ⥤ Type w) (U : Cᵒᵖ) :
    (extend F j hsupp H).obj U = Σ s : F.obj U, H.obj (op (srcObj hsupp s)) := rfl

/-- The restriction maps of `extend F j hsupp H`. -/
theorem extend_map_apply (H : Dᵒᵖ ⥤ Type w) {U V : Cᵒᵖ} (f : U ⟶ V)
    (p : (extend F j hsupp H).obj U) :
    (extend F j hsupp H).map f p = ⟨F.map f p.1, H.map (srcHom hsupp f p.1).op p.2⟩ := rfl

/-- The structure morphism of the extension: forget the section of `H`. -/
@[simps]
noncomputable def extendπ (H : Dᵒᵖ ⥤ Type w) : extend F j hsupp H ⟶ F where
  app _ := ↾Sigma.fst
  naturality _ _ _ := rfl

end Extend

section Support

variable (hmem : ∀ B : D, Nonempty (F.obj (op (j.obj B))))

include hmem in
/-- **The section of `F` carried by an object in the essential image of `j`**: transport a
section over `imgObj h`, the chosen object of `D` above it, along `imgIso h`.  Both of those
are independent of the proof `h`, the essential image being a proposition. -/
noncomputable def sectionOfEssImage {U : C} (h : j.essImage U) : F.obj (op U) :=
  F.map (imgIso h).inv.op (hmem (imgObj h)).some

variable (hsupp : ∀ U : C, Nonempty (F.obj (op U)) → j.essImage U)

include hmem hsupp in
/-- **The essential image of `j` is closed under morphisms into it**: it is the support of a
presheaf, and a presheaf has a section over the source of a morphism as soon as it has one over
its target. -/
theorem essImage_of_hom {V U : C} (f : V ⟶ U) (h : j.essImage U) : j.essImage V :=
  hsupp V ⟨F.map f.op (sectionOfEssImage hmem h)⟩

variable [j.Full] [j.Faithful]

omit [j.Faithful] in
include hmem hsupp in
/-- Pushing a sieve on an object of `D` forward and pulling it back recovers it, and — because
the essential image is closed under morphisms into it — so does the other composite. -/
theorem functorPushforward_functorPullback_of_essImage {A : D} (T : Sieve (j.obj A)) :
    (T.functorPullback j).functorPushforward j = T := by
  refine Sieve.ext fun V g ↦ ⟨?_, fun hg ↦ ?_⟩
  · rintro ⟨B, k, a, hk, rfl⟩
    exact T.downward_closed hk a
  · obtain ⟨B, ⟨ε⟩⟩ := essImage_of_hom hmem hsupp g ⟨A, ⟨Iso.refl _⟩⟩
    refine ⟨B, j.preimage (ε.hom ≫ g), ε.inv, ?_, by rw [j.map_preimage]; simp⟩
    change T.arrows (j.map (j.preimage (ε.hom ≫ g)))
    rw [j.map_preimage]
    exact T.downward_closed hg ε.hom

/-- For an object of `D`, the object chosen over its image is canonically isomorphic to it. -/
noncomputable def srcIsoSelf (B : D) (s : F.obj (op (j.obj B))) : srcObj hsupp s ≅ B :=
  (Functor.FullyFaithful.ofFullyFaithful j).preimageIso (srcIso hsupp s)

/-- The image under `j` of `srcIsoSelf hsupp B s` is `srcIso hsupp s`. -/
theorem map_srcIsoSelf_hom (B : D) (s : F.obj (op (j.obj B))) :
    j.map (srcIsoSelf hsupp B s).hom = (srcIso hsupp s).hom :=
  j.map_preimage _

end Support

end Stacks.Topos.Subterminal

end CategoryTheory

end
