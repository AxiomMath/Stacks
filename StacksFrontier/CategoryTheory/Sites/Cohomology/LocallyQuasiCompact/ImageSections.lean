module

public import Mathlib.CategoryTheory.Sites.Subsheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ProperDirectImage

/-!
# Sections of an inverse image are locally pulled back from the source site

Let `u : C ⥤ D` be a continuous functor of sites `(C, J) → (D, K)` and let
`L ⊣ u.sheafPushforwardContinuous` be the induced adjunction on sheaves of sets, so that `L` is
the inverse image `u^{-1}` of the morphism of topoi. This file proves that a sheaf `A` on `(D, K)`
at which the counit of the adjunction is invertible — equivalently, a sheaf in the essential image
of `u^{-1}` — has all of its sections locally pulled back from the image of `u`: for a section `a`
of `A` over `Z`, the arrows `h : W ⟶ Z` along which `a` restricts to the pullback of a section of
`A` over some `u V` form a `K`-covering sieve of `Z`.

The point is that this is proved **without any description of `u^{-1}`**. The usual route —
`u^{-1}` is the sheafification of a left Kan extension, `toSheafify` is locally surjective, and a
section of the Kan extension at `Z` is represented by a section over some `u V` — is unavailable
here: Mathlib's local surjectivity of `toSheafify` is stated for coefficients `Type (max u v)`
over a site with objects in `Type u` and morphisms in `Type v`, and the sites of Stacks 0DCU carry
coefficients in a third, independent universe. The argument below uses only the counit.

## Main definitions and results

* `Stacks.SiteImageSections.imageSections`: the subpresheaf of sections pulled back from the image
  of `u`.
* `Stacks.SiteImageSections.isIso_counit_app_obj`: the counit of an adjunction with invertible
  unit is invertible at every object in the image of the left adjoint.
* `Stacks.SiteImageSections.isIso_of_mono_of_isIso_map`: a monomorphism sent to an isomorphism by
  the right adjoint, at whose target the counit is invertible, is an isomorphism.
* `Stacks.SiteImageSections.sieveOfSection_imageSections_mem`: the sieve of arrows along which a
  section becomes pulled back from the image of `u` is a covering sieve.
* `sieveOfSection_imageSections_comparison_mem`, in the namespace
  `Stacks.Topology.LocallyQuasiCompactZariskiSituation`: the case of the Zariski comparison
  morphism, where `u` is the open-subset functor, so that sections of `π_X^{-1}F` are locally
  pulled back from sections of `F` over open subsets of `X`.

## Implementation notes

The proof is: let `A'` be the sheafification, as a subpresheaf, of the subpresheaf of sections
pulled back from the image of `u`. Over an object `u V` the two agree, because a section there is
pulled back from itself along the identity; so `u_*` of the inclusion `ι : A' ⟶ A` is an
isomorphism, and the adjunction therefore factors the counit at `A` through `ι`. The counit at `A`
is an isomorphism by hypothesis, so `ι` is a split epimorphism; it is also a monomorphism, being
an inclusion of subpresheaves, hence an isomorphism, hence `A' = ⊤`. Membership of `a` in `A'` at
`Z` is by definition the statement that the sieve is covering.

Being a subsheaf of a sheaf is `CategoryTheory.Subfunctor.sheafify_isSheaf`, and `A' = ⊤` is read
off from `CategoryTheory.Subfunctor.eq_top_iff_isIso`; both are universe-polymorphic in the
coefficients, which is what makes this route available where the sheafification route is not.

These declarations carry no tag: Stacks 0DCU has seven clauses and its covering set is not
complete until all of them are in the library.

## References

* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Stacks.SiteImageSections

universe w v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} (u : C ⥤ D)

/-- The sections of a sheaf on `(D, K)` which are pulled back from a section over an object in
the image of `u`: over `Z`, the sections of the form `A(c)(b)` for some `V : C`, some
`c : Z ⟶ u V` and some `b ∈ A(u V)`. -/
def imageSections (A : Sheaf K (Type w)) : Subfunctor A.obj where
  obj Z := {a | ∃ (V : C) (c : Z.unop ⟶ u.obj V) (b : A.obj.obj (op (u.obj V))),
    a = A.obj.map c.op b}
  map := by
    rintro Z Z' i a ⟨V, c, b, rfl⟩
    exact ⟨V, i.unop ≫ c, b, by rw [op_comp, Quiver.Hom.op_unop, Functor.map_comp_apply]⟩

/-- A section over an object in the image of `u` is itself pulled back from one, along the
identity. -/
theorem imageSections_obj_image (A : Sheaf K (Type w)) (V : C) :
    (imageSections u A).obj (op (u.obj V)) = ⊤ :=
  eq_top_iff.2 fun a _ => ⟨V, 𝟙 _, a, (Functor.map_id_apply A.obj _ a).symm⟩

variable {u}

/-- The counit of an adjunction whose unit is invertible is invertible at every object in the
image of the left adjoint: the left triangle identity exhibits it as a left inverse of an
isomorphism.

Nothing here is about sheaves: the proof uses only the left triangle identity, and the statement
is needed for abelian coefficients as well as for sheaves of sets, so it is stated for an
arbitrary adjunction. -/
theorem isIso_counit_app_obj {A : Type u₃} [Category.{v₃} A] {B : Type u₄} [Category.{v₄} B]
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) [IsIso adj.unit]
    (F : A) : IsIso (adj.counit.app (L.obj F)) := by
  have : IsIso (L.map (adj.unit.app F) ≫ adj.counit.app (L.obj F)) := by
    rw [adj.left_triangle_components F]
    exact IsIso.id _
  exact IsIso.of_isIso_comp_left (L.map (adj.unit.app F)) _

/-- A monomorphism `f : X ⟶ Y` which the right adjoint of an adjunction sends to an isomorphism,
and at whose target the counit of the adjunction is invertible, is itself an isomorphism: the
adjunction factors the counit at `Y` through `f`, exhibiting `f` as a split epimorphism.

Nothing here is about sheaves either, so it too is stated for an arbitrary adjunction. -/
theorem isIso_of_mono_of_isIso_map {A : Type u₃} [Category.{v₃} A] {B : Type u₄} [Category.{v₄} B]
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) {X Y : B} (f : X ⟶ Y) [Mono f] [IsIso (R.map f)]
    [IsIso (adj.counit.app Y)] : IsIso f := by
  have hfac : (L.map (inv (R.map f)) ≫ adj.counit.app X) ≫ f = adj.counit.app Y := by
    rw [Category.assoc, ← adj.counit_naturality f, ← Category.assoc, ← Functor.map_comp,
      IsIso.inv_hom_id, L.map_id, Category.id_comp]
  have : IsSplitEpi f :=
    IsSplitEpi.mk' ⟨inv (adj.counit.app Y) ≫ L.map (inv (R.map f)) ≫ adj.counit.app X, by
      rw [Category.assoc, hfac, IsIso.inv_hom_id]⟩
  exact isIso_of_mono_of_isSplitEpi f

variable [u.IsContinuous J K] {L : Sheaf J (Type w) ⥤ Sheaf K (Type w)}
  (adj : L ⊣ u.sheafPushforwardContinuous (Type w) J K)

/-- **Every section of a sheaf in the essential image of `u^{-1}` is locally pulled back from the
image of `u`.** The sieve of arrows `h : W ⟶ Z` along which a section `a` of `A` over `Z`
restricts to a section pulled back from an object `u V` is a covering sieve.

No description of `u^{-1}` is used: the hypothesis is that the counit of the adjunction is
invertible at `A`, which holds at every `A = u^{-1}F` as soon as the unit is invertible. -/
theorem sieveOfSection_imageSections_mem (A : Sheaf K (Type w))
    (hA : IsIso (adj.counit.app A)) {Z : D} (a : A.obj.obj (op Z)) :
    (imageSections u A).sieveOfSection a ∈ K Z := by
  let A' : Sheaf K (Type w) :=
    ⟨((imageSections u A).sheafify K).toFunctor, (isSheaf_iff_isSheaf_of_type K _).2
      (Subfunctor.sheafify_isSheaf _ ((isSheaf_iff_isSheaf_of_type K A.obj).1 A.property))⟩
  let ι : A' ⟶ A := ObjectProperty.homMk ((imageSections u A).sheafify K).ι
  have hιmono : Mono ι :=
    (sheafToPresheaf K _).mono_of_mono_map
      (inferInstanceAs (Mono ((imageSections u A).sheafify K).ι))
  have hRι : IsIso ((u.sheafPushforwardContinuous (Type w) J K).map ι) := by
    rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf J _), NatTrans.isIso_iff_isIso_app]
    intro V
    rw [isIso_iff_bijective]
    exact ⟨Subtype.coe_injective, fun b => ⟨⟨b, (imageSections u A).le_sheafify K _
      ⟨V.unop, 𝟙 _, b, (Functor.map_id_apply A.obj _ b).symm⟩⟩, rfl⟩⟩
  have hιiso : IsIso ι := isIso_of_mono_of_isIso_map adj ι
  have hιpre : IsIso ((imageSections u A).sheafify K).ι :=
    inferInstanceAs (IsIso ((sheafToPresheaf K (Type w)).map ι))
  show a ∈ ((imageSections u A).sheafify K).obj (op Z)
  rw [(Subfunctor.eq_top_iff_isIso _).2 hιpre]
  trivial

end Stacks.SiteImageSections

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w' v

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}

/-- **Sections of the Zariski comparison inverse image are locally pulled back from opens.**
For a sheaf `F` on the small Zariski site of `X` and a section `a` of `π_X^{-1}F` over an object
`Z` of the localized Zariski site, the arrows `h : W ⟶ Z` along which `a` restricts to the
pullback of a section of `π_X^{-1}F` over an open subset of `X`, viewed in the slice site, form a
Zariski covering sieve of `Z`. -/
theorem sieveOfSection_imageSections_comparison_mem
    (S : LocallyQuasiCompactZariskiSituation.{u, w'} S₀ Bound) (X : S.category)
    (F : Sheaf (Opens.grothendieckTopology X.obj) (Type (max u v))) {Z : Over X}
    (a : ((S.comparisonInverseImage.{u, w', v} X).obj F).obj.obj (Opposite.op Z)) :
    (Stacks.SiteImageSections.imageSections (S.opensToSlice X).1
        ((S.comparisonInverseImage.{u, w', v} X).obj F)).sieveOfSection a ∈
      S.zariskiTopology.over X Z := by
  have := S.opensToSlice_isContinuous X
  have := comparisonAdjunction_unit_isIso.{u, w', v} S X
  exact Stacks.SiteImageSections.sieveOfSection_imageSections_mem
    (S.comparisonAdjunction.{u, w', v} X) _
    (Stacks.SiteImageSections.isIso_counit_app_obj (S.comparisonAdjunction.{u, w', v} X) F) a

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
