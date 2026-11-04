module

public import Mathlib.CategoryTheory.Adjunction.Triple
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.CategoryTheory.Filtered.AlmostDirected
public import StacksFrontier.CategoryTheory.Filtered.SpanCocones
public import StacksFrontier.CategoryTheory.Sites.Presheaf.Functoriality.StructuredArrowCompletion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The adjoints of restriction along a continuous functor of sites

Let `(C, J)` and `(D, K)` be sites and let `u : C ⥤ D` be continuous, so that restriction along
`u.op` carries `K`-sheaves to `J`-sheaves and defines `g^{-1} = u^s = u^p : Sh(D) ⥤ Sh(C)`. Its
left adjoint `g_!` is computed as the sheafification `(u_p)^#` of the left Kan extension `u_p`
along `u.op`, and, when `u` is also cocontinuous, its right adjoint `g_*` is the restriction to
sheaves of the right Kan extension along `u.op`; together they form the triple `g_! ⊣ g^{-1} ⊣ g_*`
attached to the morphism of topoi `g : Sh(C) → Sh(D)`. This file proves that `g_!` is exact on
finite connected shapes, and that for `u` fully faithful both `g_!` and `g_*` are sections of
`g^{-1}`.

The functor `g_!` is *not* left exact: it does not carry the final sheaf on `C` to the final sheaf
on `D`, the site theoretic form of the failure of `j_!` to preserve the final object for an open
immersion `j` of topological spaces. What survives is exactness on *connected* finite shapes, and
it survives under a hypothesis on `u` alone. Indeed `u_p F(V)` is the colimit of `F` over the
opposite of the comma category `I_V` of pairs `(U, V ⟶ u(U))`; if `C` has fibre products and
equalizers and `u` preserves them, then any two morphisms out of an object of `(I_V)^{op}` are
dominated by a third and any two parallel morphisms are coequalized, so `(I_V)^{op}` is a disjoint
union of filtered categories and colimits over it commute with finite connected limits. As limits
of sheaves are limits of presheaves and sheafification is left exact, `g_!` commutes with finite
connected limits, in particular with fibre products and equalizers.

If `u` is moreover fully faithful, both outer functors of the triple are sections of `g^{-1}`: the
unit `F ⟶ g^{-1}g_!F` and the counit `g^{-1}g_*F ⟶ F` are isomorphisms for every sheaf `F` on `C`.
Concretely `(g_*F)(u(X))` is a limit of the `F(Y)` over the pairs `(Y, u(Y) ⟶ u(X))` and
`(u_pF)(u(X))` a colimit of the `F(Y)` over the pairs `(Y, u(X) ⟶ u(Y))`, and full faithfulness
makes `(X, u(𝟙_X))` initial, resp. terminal, in the indexing category, so both reduce to `F(X)`.
Thus `g` exhibits `Sh(C)` as a subtopos of `Sh(D)` in two ways, the site theoretic analogue of the
morphism of topoi attached to an open immersion of topological spaces. The unit of `g_! ⊣ g^{-1}`
is an isomorphism exactly when the counit of `g^{-1} ⊣ g_*` is.

## Main results

* `CategoryTheory.Functor.preservesLimitsOfShape_sheafPullback`: if `C` has fibre products and
  equalizers and the continuous functor `u` preserves them, then `g_!` preserves limits of every
  finite connected shape.
* `CategoryTheory.Functor.isIso_sheafAdjunctionCocontinuous_counit`: if `u` is cocontinuous,
  continuous and fully faithful, the counit `g^{-1}g_*F ⟶ F` is an isomorphism.
* `CategoryTheory.Functor.isIso_unit_of_sheafPushforwardContinuous`: under the same hypotheses, the
  unit `F ⟶ g^{-1}LF` is an isomorphism for every left adjoint `L` of `g^{-1}`.
* `CategoryTheory.Functor.isIso_sheafAdjunctionContinuous_unit`: the same conclusion for
  `CategoryTheory.Functor.sheafPullback`, whenever `g^{-1}` admits a left adjoint.

## References

* [Stacks 00XS](https://stacks.math.columbia.edu/tag/00XS)
* [Stacks 00XT](https://stacks.math.columbia.edu/tag/00XT)
-/

/-! ### `g_!` commutes with finite connected limits -/

section

open CategoryTheory Limits

universe w t v₁ v₂ u₁ u₂

/-- A morphism `f : x ⟶ y` of `B` followed by the transport along `e` of a morphism out of
`e.inverse.obj y` is the transport of a single morphism out of `e.inverse.obj x`. -/
public theorem comp_counitInv_app_map_assoc.{s₁, s₂, x₁, x₂}
    {A : Type x₁} [Category.{s₁} A] {B : Type x₂} [Category.{s₂} B]
    (e : A ≌ B) {x y : B} (f : x ⟶ y) {W : A} (a : e.inverse.obj y ⟶ W) :
    f ≫ e.counitInv.app y ≫ e.functor.map a
      = e.counitInv.app x ≫ e.functor.map (e.inverse.map f ≫ a) := by
  simp

/-- If every span in `A` can be completed to a commutative square, then so can every span in a
category `B` equivalent to `A`. -/
public theorem hasSpanCocone_of_equivalence.{s₁, s₂, x₁, x₂}
    {A : Type x₁} [Category.{s₁} A] {B : Type x₂} [Category.{s₂} B]
    (e : A ≌ B) (h : HasSpanCocone A) : HasSpanCocone B := by
  intro x y z f g
  obtain ⟨W, a, b, hab⟩ := h (e.inverse.map f) (e.inverse.map g)
  exact ⟨e.functor.obj W, e.counitInv.app y ≫ e.functor.map a,
    e.counitInv.app z ≫ e.functor.map b, by
      rw [comp_counitInv_app_map_assoc, comp_counitInv_app_map_assoc, hab]⟩

/-- If every parallel pair in `A` can be coequalized, then so can every parallel pair in a
category `B` equivalent to `A`. -/
public theorem hasCoequalizingHom_of_equivalence.{s₁, s₂, x₁, x₂}
    {A : Type x₁} [Category.{s₁} A] {B : Type x₂} [Category.{s₂} B]
    (e : A ≌ B) (h : HasCoequalizingHom A) : HasCoequalizingHom B := by
  intro x y a b
  obtain ⟨W, c, hc⟩ := h (e.inverse.map a) (e.inverse.map b)
  exact ⟨e.functor.obj W, e.counitInv.app y ≫ e.functor.map c, by
    rw [comp_counitInv_app_map_assoc, comp_counitInv_app_map_assoc, hc]⟩

/-- Let `u : C ⥤ D` be a functor, assume that `C` has fibre products and equalizers and that `u`
preserves them, and let `Y = op V` for an object `V` of `D`. Then the comma category
`CostructuredArrow u.op Y`, the opposite `(I_V)^{op}` of the category of pairs `(U, V ⟶ u(U))`, is
almost directed: each of its connected components is filtered. -/
private theorem isAlmostDirected_costructuredArrow
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (u : C ⥤ D)
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u] [PreservesLimitsOfShape WalkingParallelPair u]
    (Y : Dᵒᵖ) : IsAlmostDirected (CostructuredArrow u.op Y) := by
  obtain ⟨hspan, hcoeq⟩ := structuredArrow_op_span_and_parallelPair_completion u Y.unop
  have e := structuredArrowOpEquivalence u Y.unop
  exact ⟨isFiltered_component_of_cocone_and_coequaliser
    (hasSpanCocone_of_equivalence e hspan) (hasCoequalizingHom_of_equivalence e hcoeq)⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The evaluation of `F.lan` at `X` is the colimit over the costructured arrows over `X`. -/
private noncomputable def lanCompEvaluationIsoColim.{s₁, s₂, s₃, x₁, x₂, x₃}
    {A : Type x₁} [Category.{s₁} A] {B : Type x₂} [Category.{s₂} B]
    (E : Type x₃) [Category.{s₃} E] (F : A ⥤ B) (X : B)
    [∀ X : B, HasColimitsOfShape (CostructuredArrow F X) E] :
    F.lan ⋙ (evaluation B E).obj X ≅
      (Functor.whiskeringLeft _ _ E).obj (CostructuredArrow.proj F X) ⋙ colim :=
  NatIso.ofComponents (fun G =>
    IsColimit.coconePointUniqueUpToIso
    (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G X)
    (colimit.isColimit _)) (fun {G₁ G₂} φ => by
      apply (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G₁ X).hom_ext
      intro T
      have h₁ := fun (G : A ⥤ E) => IsColimit.comp_coconePointUniqueUpToIso_hom
        (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G X) (colimit.isColimit _) T
      have h₂ := congr_app (F.lanUnit.naturality φ) T.left
      dsimp at h₁ h₂ ⊢
      simp only [Category.assoc] at h₁ ⊢
      simp only [Functor.lan, Functor.lanUnit] at h₂ ⊢
      rw [reassoc_of% h₁, NatTrans.naturality_assoc, ← reassoc_of% h₂, h₁,
        ι_colimMap, Functor.whiskerLeft_app]
      rfl)

@[expose] public section

namespace CategoryTheory.Functor

/-- Let `u : C ⥤ D` be a continuous functor of sites such that `C` has fibre products and
equalizers and `u` preserves them. Then `g_! = u.sheafPullback` preserves limits of every finite
connected shape, in particular fibre products and equalizers. -/
@[stacks 00XS "If `u` is continuous and `C` has fibre products and equalizers which `u` preserves,
  then `g_!` commutes with fibre products and equalizers, and more generally with finite connected
  limits.", sga "4 III 1.3" "5), connected limits", sga "4 III 1.9.2" "more general"]
public theorem preservesLimitsOfShape_sheafPullback
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsContinuous J K] [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u] [PreservesLimitsOfShape WalkingParallelPair u]
    [HasSheafify K (Type w)] [∀ Y : Dᵒᵖ, Small.{w} (CostructuredArrow u.op Y)]
    (I : Type t) [SmallCategory I] [FinCategory I] [IsConnected I] :
    PreservesLimitsOfShape I (u.sheafPullback (Type w) J K) := by
  have : PreservesLimitsOfShape I (u.op.lan : (Cᵒᵖ ⥤ Type w) ⥤ (Dᵒᵖ ⥤ Type w)) :=
    preservesLimitsOfShape_of_evaluation _ I fun Y =>
      have := isAlmostDirected_costructuredArrow u Y
      have := preservesLimitsOfShape_colim_of_isConnected (CostructuredArrow u.op Y) I
      preservesLimitsOfShape_of_natIso (lanCompEvaluationIsoColim (Type w) u.op Y).symm
  have : PreservesLimitsOfShape I
      (Functor.sheafPullbackConstruction.sheafPullback u (Type w) J K) :=
    show PreservesLimitsOfShape I
      (sheafToPresheaf J (Type w) ⋙ u.op.lan ⋙ presheafToSheaf K (Type w)) from inferInstance
  exact preservesLimitsOfShape_of_natIso
    (Functor.sheafPullbackConstruction.sheafPullbackIso u (Type w) J K).symm

end CategoryTheory.Functor

end

end

/-! ### A fully faithful functor of sites embeds its topos -/

section

open CategoryTheory

universe v₁ v₂ w w' u₁ u₂

/-- A natural transformation between functors valued in a full subcategory of `C` is an
isomorphism if and only if each of its components is an isomorphism in `C`. -/
private lemma isIso_iff_isIso_hom_app.{s₁, s₂, x₁, x₂} {E : Type x₁} [Category.{s₁} E]
    {C : Type x₂} [Category.{s₂} C] {P : ObjectProperty C} {F G : E ⥤ P.FullSubcategory}
    (α : F ⟶ G) :
    IsIso α ↔ ∀ X, IsIso (α.app X).hom :=
  (NatTrans.isIso_iff_isIso_app α).trans
    (forall_congr' fun _ ↦ (ObjectProperty.isIso_hom_iff _).symm)

@[expose] public section

namespace CategoryTheory.Functor

/-- If `u : C ⥤ D` is cocontinuous, continuous and fully faithful, the counit
`g^{-1}g_*F ⟶ F` of `g^{-1} ⊣ g_*` is an isomorphism; equivalently `g_*` is fully faithful. -/
@[stacks 00XT "If `u` is cocontinuous, continuous and fully faithful, the canonical map
  `g^{-1}g_*F → F` is an isomorphism for every sheaf `F` on `C`. Existence of `g_!` is not needed
  for this half.",
  sga "4 III 2.6" "u ff ⇒ u_* ff",
  stacks 0788 "(1)(c) and (2)(c): the counit of the cocontinuous sheaf adjunction is invertible",
  sga "4 IV 4.10.5" "more general"]
public instance isIso_sheafAdjunctionCocontinuous_counit
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (u : C ⥤ D)
    (A : Type w) [Category.{w'} A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsCocontinuous J K] [u.IsContinuous J K] [u.Full] [u.Faithful]
    [∀ F : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension F] :
    IsIso (u.sheafAdjunctionCocontinuous A J K).counit :=
  (isIso_iff_isIso_hom_app _).2 fun F ↦ by
    rw [Functor.sheafAdjunctionCocontinuous_counit_app_hom]
    exact inferInstanceAs (IsIso ((u.op.ranAdjunction A).counit.app F.obj))

/-- If `u : C ⥤ D` is cocontinuous, continuous and fully faithful, then for every left adjoint `L`
of `g^{-1} = u^s` the unit `F ⟶ g^{-1}LF` of `L ⊣ g^{-1}` is an isomorphism. -/
@[stacks 00XT "If `u` is cocontinuous, continuous and fully faithful, the canonical map
  `F → g^{-1}g_!F` is an isomorphism, for every left adjoint `g_!` of `g^{-1}`.",
  sga "4 III 2.6" "u ff ⇒ u_! ff", sga "4 I 5.6" "i⇒iii", sga "4 IV 4.10.5" "more general"]
public theorem isIso_unit_of_sheafPushforwardContinuous
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (u : C ⥤ D)
    (A : Type w) [Category.{w'} A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsCocontinuous J K] [u.IsContinuous J K] [u.Full] [u.Faithful]
    [∀ F : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension F]
    {L : Sheaf J A ⥤ Sheaf K A} (adj : L ⊣ u.sheafPushforwardContinuous A J K) :
    IsIso adj.unit :=
  (Adjunction.Triple.isIso_unit_iff_isIso_counit ⟨adj, u.sheafAdjunctionCocontinuous A J K⟩).2
    (isIso_sheafAdjunctionCocontinuous_counit u A J K)

/-- If `u : C ⥤ D` is cocontinuous, continuous and fully faithful and `g^{-1}` has a left adjoint
`g_!`, the unit `F ⟶ g^{-1}g_!F` of `g_! ⊣ g^{-1}` is an isomorphism; equivalently `g_!` is fully
faithful. -/
@[stacks 00XT "If `u` is cocontinuous, continuous and fully faithful, the canonical map
  `F → g^{-1}g_!F` is an isomorphism for every sheaf `F` on `C`.",
  sga "4 III 2.6" "u ff ⇒ u_! ff",
  sga "4 VII 4.1" "more general"]
public instance isIso_sheafAdjunctionContinuous_unit
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (u : C ⥤ D)
    (A : Type w) [Category.{w'} A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsCocontinuous J K] [u.IsContinuous J K] [u.Full] [u.Faithful]
    [∀ F : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension F]
    [(u.sheafPushforwardContinuous A J K).IsRightAdjoint] :
    IsIso (u.sheafAdjunctionContinuous A J K).unit :=
  isIso_unit_of_sheafPushforwardContinuous u A J K (u.sheafAdjunctionContinuous A J K)

end CategoryTheory.Functor

end

end
