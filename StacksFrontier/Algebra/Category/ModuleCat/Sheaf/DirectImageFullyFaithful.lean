module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Triple

/-!
# `g^*g_! = id` on sheaves of modules, for a fully faithful functor of sites

Let `u : C ⥤ D` be a functor of sites which is continuous, cocontinuous and fully faithful, so
that the associated morphism of topoi `g : Sh(C) ⟶ Sh(D)` presents `Sh(C)` as a subtopos of
`Sh(D)` and `g^{-1}` is restriction along `u`. Let `O` be a sheaf of rings on `D` and let
`φ : S ⟶ {}_su O` be an invertible structure morphism, so that restriction of sheaves of modules
`g^* = SheafOfModules.pushforward φ` carries `O`-modules to `S`-modules. The unit `id ⟶ g^*L` of
any left adjoint `L` of `g^*` is an isomorphism, and the direct image of sheaves of modules along
`u` is fully faithful.

## Main definitions

* `Stacks.SheafOfModules.RestrictScalars.equivalence`: restriction of scalars along an
  isomorphism of sheaves of rings, as an equivalence, with the universe of the module sections
  independent of the universe of the sheaves of rings.
* `PresheafOfModules.ffIndexHom`: for a fully faithful `u`, the unique index morphism `x ⟶ y`
  of `C` lying under a structural morphism `u x ⟶ u y`.
* `PresheafOfModules.ffDirectImageCounitInv`: the inverse of the counit of the direct image of
  presheaves of modules, sending a section to the compatible family of its restrictions.

## Main results

* `PresheafOfModules.isIso_directImageModuleCounit`: the counit `g^*g_* ⟶ id` of the direct
  image of presheaves of modules is an isomorphism, hence
  `PresheafOfModules.fullyFaithfulDirectImage`.
* `SheafOfModules.isIso_pushforward0DirectImageAdjunction_counit` with
  `SheafOfModules.full_directImage` and `SheafOfModules.faithful_directImage`: the same on
  sheaves of modules.
* `SheafOfModules.isIso_unit_of_pushforward₀`: the unit of any left adjoint of restriction is an
  isomorphism, for the strict form of restriction in which the sheaf of rings of the source is
  `{}_su O` on the nose.
* `SheafOfModules.isIso_unit_of_isIso_coefficient`: the same for an arbitrary invertible
  structure morphism `φ`.

## References

* [Stacks Project, Tag 00XT](https://stacks.math.columbia.edu/tag/00XT)
* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
* [Stacks Project, Tag 0789](https://stacks.math.columbia.edu/tag/0789)
* [Stacks Project, Tag 0797](https://stacks.math.columbia.edu/tag/0797)
-/


@[expose] public noncomputable section

open CategoryTheory Opposite

universe m r w vC vD uC uD v u

namespace Stacks.SheafOfModules.RestrictScalars

/-- Restricting a presheaf of `T`-modules along `α : S ⟶ T` and then along a section `β : T ⟶ S`
of `α` returns it, naturally. -/
def presheafCompIso {C : Type u} [Category.{v} C] {S T : Cᵒᵖ ⥤ RingCat.{r}} (α : S ⟶ T)
    (β : T ⟶ S) (h : β ≫ α = 𝟙 T) :
    PresheafOfModules.restrictScalars.{m} α ⋙ PresheafOfModules.restrictScalars.{m} β ≅
      𝟭 (PresheafOfModules.{m} T) := by
  let objectIso (M : PresheafOfModules.{m} T) (Z : Cᵒᵖ) :
      (((PresheafOfModules.restrictScalars.{m} α ⋙
        PresheafOfModules.restrictScalars.{m} β).obj M).obj Z) ≅ M.obj Z := by
    have hba : (α.app Z).hom.comp (β.app Z).hom = RingHom.id (T.obj Z) := by
      simpa using congrArg (fun z : T ⟶ T ↦ (z.app Z).hom) h
    exact (ModuleCat.restrictScalarsComp'App (β.app Z).hom (α.app Z).hom
        ((α.app Z).hom.comp (β.app Z).hom) rfl (M.obj Z)).symm ≪≫
      ModuleCat.restrictScalarsId'App ((α.app Z).hom.comp (β.app Z).hom) hba (M.obj Z)
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · exact ⟨PresheafOfModules.Hom.mk (fun Z ↦ (objectIso M Z).hom) (by intro Z Z' g; ext x; rfl),
      PresheafOfModules.Hom.mk (fun Z ↦ (objectIso M Z).inv) (by intro Z Z' g; ext x; rfl),
      by ext; rfl, by ext; rfl⟩
  · intro M N φ
    ext
    rfl

/-- Restricting a sheaf of `T`-modules along `α : S ⟶ T` and then along a section `β : T ⟶ S` of
`α` returns it, naturally. -/
def compIso {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {S T : Sheaf J RingCat.{r}} (α : S ⟶ T) (β : T ⟶ S) (h : β ≫ α = 𝟙 T) :
    _root_.SheafOfModules.restrictScalars.{m} α ⋙ _root_.SheafOfModules.restrictScalars.{m} β ≅
      𝟭 (_root_.SheafOfModules.{m} T) := by
  let e := presheafCompIso.{m} α.hom β.hom (congrArg (fun q : T ⟶ T ↦ q.hom) h)
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · exact ⟨⟨(e.app M.val).hom⟩, ⟨(e.app M.val).inv⟩,
      _root_.SheafOfModules.hom_ext (e.app M.val).hom_inv_id,
      _root_.SheafOfModules.hom_ext (e.app M.val).inv_hom_id⟩
  · intro M N φ
    exact _root_.SheafOfModules.hom_ext (e.hom.naturality φ.val)

/-- Restriction of scalars along an isomorphism of sheaves of rings, as an equivalence, at a
universe of module sections independent of the universe of the sheaves of rings. -/
def equivalence {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {S T : Sheaf J RingCat.{r}} (α : S ⟶ T) [IsIso α] :
    _root_.SheafOfModules.{m} T ≌ _root_.SheafOfModules.{m} S :=
  CategoryTheory.Equivalence.mk (_root_.SheafOfModules.restrictScalars.{m} α)
    (_root_.SheafOfModules.restrictScalars.{m} (inv α))
    (compIso.{m} α (inv α) (by simp)).symm (compIso.{m} (inv α) α (by simp))

/-- Restriction of scalars along an isomorphism of sheaves of rings is an equivalence, at a
universe of module sections independent of the universe of the sheaves of rings. -/
instance isEquivalence {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {S T : Sheaf J RingCat.{r}} (α : S ⟶ T) [IsIso α] :
    (_root_.SheafOfModules.restrictScalars.{m} α).IsEquivalence :=
  (equivalence.{m} α).isEquivalence_functor

end Stacks.SheafOfModules.RestrictScalars

namespace PresheafOfModules

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (f : C ⥤ D) [f.Full] [f.Faithful] (R : Dᵒᵖ ⥤ RingCat.{r})

/-- The index morphism of `C` under a structural morphism of `D`: for a fully faithful `f` and an
object `j = (y, ψ : f x ⟶ f y)` of the category indexing the right Kan extension along `f.op` at
`f x`, the unique morphism `x ⟶ y` of `Cᵒᵖ` with `f.op` of it equal to `ψ`. -/
def ffIndexHom {x : Cᵒᵖ} (j : StructuredArrow (f.op.obj x) f.op) : x ⟶ j.right :=
  f.op.preimage j.hom

omit [f.Faithful] in
/-- The image under `f.op` of the index morphism at `j` is the structural morphism of `j`. -/
@[simp] lemma map_ffIndexHom {x : Cᵒᵖ} (j : StructuredArrow (f.op.obj x) f.op) :
    f.op.map (ffIndexHom f j) = j.hom := f.op.map_preimage _

/-- The index morphisms are compatible with the morphisms of the indexing category. -/
lemma ffIndexHom_comp {x : Cᵒᵖ} {j k : StructuredArrow (f.op.obj x) f.op} (g : j ⟶ k) :
    ffIndexHom f j ≫ g.right = ffIndexHom f k :=
  f.op.map_injective (by
    rw [f.op.map_comp, map_ffIndexHom, map_ffIndexHom, StructuredArrow.w g])

/-- The index morphism at the identity index is the identity. -/
lemma ffIndexHom_self (x : Cᵒᵖ) :
    ffIndexHom f (StructuredArrow.mk (𝟙 (f.op.obj x))) = 𝟙 x :=
  f.op.map_injective (by rw [map_ffIndexHom, f.op.map_id]; rfl)

variable (N : PresheafOfModules.{max uC vD w} (f.op ⋙ R))

/-- The compatible family of sections attached to a single section over `x`: its value at an index
`j` is the given section restricted along `PresheafOfModules.ffIndexHom`. -/
def ffCounitInvSections (x : Cᵒᵖ) (t : N.obj x) :
    directImageSections.{r, w} f R N (f.op.obj x) :=
  ⟨fun j ↦ N.map (ffIndexHom f j) t, fun {j k} g ↦ by
    rw [← N.map_comp_apply, ffIndexHom_comp f g]⟩

/-- The inverse of the counit of the direct image of presheaves of modules, for a fully faithful
functor of index categories. -/
def ffDirectImageCounitInv :
    N ⟶ (directImage.{r, w} f R ⋙ pushforward₀.{max uC vD w} f R).obj N where
  app x := ModuleCat.ofHom
    { toFun := ffCounitInvSections f R N x
      map_add' := fun t t' ↦ by
        apply Subtype.ext; funext j; exact map_add _ _ _
      map_smul' := fun a t ↦ by
        apply Subtype.ext; funext j
        change N.map (ffIndexHom f j) (a • t) = R.map j.hom a • N.map (ffIndexHom f j) t
        rw [N.map_smul]
        change R.map (f.op.map (ffIndexHom f j)) a • _ = _
        rw [map_ffIndexHom] }
  naturality := by
    intro x y a
    ext t
    refine Subtype.ext (funext fun j ↦ ?_)
    change N.map (ffIndexHom f j) (N.map a t) = _
    rw [← N.map_comp_apply]
    change _ = N.map (ffIndexHom f (StructuredArrow.mk (f.op.map a ≫ j.hom))) t
    have h : a ≫ ffIndexHom f j =
        ffIndexHom f (StructuredArrow.mk (f.op.map a ≫ j.hom)) :=
      f.op.map_injective (by rw [f.op.map_comp, map_ffIndexHom, map_ffIndexHom]; rfl)
    rw [h]

/-- The counit `g^*g_* ⟶ id` of the direct image of presheaves of modules is an isomorphism at
every presheaf of modules, when the functor of index categories is fully faithful. -/
theorem isIso_directImageModuleCounit_app :
    IsIso ((directImageModuleCounit.{r, w} f R).app N) := by
  refine ⟨ffDirectImageCounitInv f R N, ?_, ?_⟩
  · ext x s
    refine Subtype.ext (funext fun j ↦ ?_)
    change N.map (ffIndexHom f j) (s.val (StructuredArrow.mk (𝟙 (f.op.obj x)))) = s.val j
    exact s.property (StructuredArrow.homMk (ffIndexHom f j)
      (by simpa using map_ffIndexHom f j) :
      (StructuredArrow.mk (𝟙 (f.op.obj x)) : StructuredArrow (f.op.obj x) f.op) ⟶ j)
  · ext x t
    change N.map (ffIndexHom f (StructuredArrow.mk (𝟙 (f.op.obj x)))) t = t
    rw [ffIndexHom_self, N.map_id]
    rfl

/-- The counit of the direct image of presheaves of modules along a fully faithful functor is an
isomorphism. -/
theorem isIso_directImageModuleCounit :
    IsIso (directImageModuleCounit.{r, w} f R) := by
  have : ∀ N, IsIso ((directImageModuleCounit.{r, w} f R).app N) :=
    isIso_directImageModuleCounit_app f R
  exact NatIso.isIso_of_isIso_app _

/-- The direct image of presheaves of modules along a fully faithful functor is fully faithful. -/
def fullyFaithfulDirectImage : (directImage.{r, w} f R).FullyFaithful :=
  haveI : IsIso (pushforward₀DirectImageAdjunction.{r, w} f R).counit :=
    isIso_directImageModuleCounit f R
  (pushforward₀DirectImageAdjunction.{r, w} f R).fullyFaithfulROfIsIsoCounit

end PresheafOfModules

namespace SheafOfModules

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (f : C ⥤ D) [f.Full] [f.Faithful] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [f.IsContinuous J K] [f.IsCocontinuous J K] (O : Sheaf K RingCat.{r})

omit [f.Full] [f.Faithful] in
/-- The direct image of sheaves of modules, read on underlying presheaves of modules, is the
direct image of presheaves of modules, as an equality of functors. -/
theorem directImage_comp_forget :
    directImage.{r, w} f J K O ⋙ forget O =
      forget ((f.sheafPushforwardContinuous RingCat.{r} J K).obj O) ⋙
        PresheafOfModules.directImage.{r, w} f O.obj := rfl

/-- The direct image of sheaves of modules along a fully faithful continuous and cocontinuous
functor of sites is full. -/
instance full_directImage : (directImage.{r, w} f J K O).Full :=
  haveI : (forget ((f.sheafPushforwardContinuous RingCat.{r} J K).obj O) ⋙
      PresheafOfModules.directImage.{r, w} f O.obj).Full :=
    ((fullyFaithfulForget _).comp
      (PresheafOfModules.fullyFaithfulDirectImage.{r, w} f O.obj)).full
  Functor.Full.of_comp_faithful_iso (eqToIso (directImage_comp_forget.{r, w} f J K O))

/-- The direct image of sheaves of modules along a fully faithful continuous and cocontinuous
functor of sites is faithful. -/
instance faithful_directImage : (directImage.{r, w} f J K O).Faithful :=
  haveI : (forget ((f.sheafPushforwardContinuous RingCat.{r} J K).obj O) ⋙
      PresheafOfModules.directImage.{r, w} f O.obj).Faithful :=
    ((fullyFaithfulForget _).comp
      (PresheafOfModules.fullyFaithfulDirectImage.{r, w} f O.obj)).faithful
  Functor.Faithful.of_comp_eq (directImage_comp_forget.{r, w} f J K O)

/-- The counit `g^*g_* ⟶ id` of the direct image of sheaves of modules along a fully faithful
continuous and cocontinuous functor of sites is an isomorphism. -/
theorem isIso_pushforward0DirectImageAdjunction_counit :
    IsIso (pushforward₀DirectImageAdjunction.{r, w} f J K O).counit :=
  Adjunction.counit_isIso_of_R_fully_faithful _

/-- `g^*g_! = id` on sheaves of modules: for a continuous, cocontinuous and fully faithful
functor of sites, the unit `id ⟶ g^*L` of any left adjoint `L` of the strict restriction of
sheaves of modules is an isomorphism. -/
theorem isIso_unit_of_pushforward₀
    {P : SheafOfModules.{max uC vD w}
        ((f.sheafPushforwardContinuous RingCat.{r} J K).obj O) ⥤
      SheafOfModules.{max uC vD w} O}
    (adj : P ⊣ pushforward₀.{r, w} f J K O) : IsIso adj.unit :=
  (Adjunction.Triple.isIso_unit_iff_isIso_counit
    ⟨adj, pushforward₀DirectImageAdjunction.{r, w} f J K O⟩).2
      (isIso_pushforward0DirectImageAdjunction_counit f J K O)

omit [f.Full] [f.Faithful] [f.IsCocontinuous J K] in
/-- Restriction of sheaves of modules along a structure morphism `φ` is the strict restriction
followed by restriction of scalars along `φ`, as an equality of functors. -/
theorem pushforward_eq_pushforward₀_comp_restrictScalars {S : Sheaf J RingCat.{r}}
    (φ : S ⟶ (f.sheafPushforwardContinuous RingCat.{r} J K).obj O) :
    pushforward.{max uC vD w} φ =
      pushforward₀.{r, w} f J K O ⋙ restrictScalars.{max uC vD w} φ := rfl

/-- `g^*g_! = id` on sheaves of modules, for an invertible structure morphism: for a continuous,
cocontinuous and fully faithful functor of sites `f` and an invertible morphism of sheaves of rings
`φ : S ⟶ {}_sf O`, the unit `id ⟶ g^*L` of any left adjoint `L` of `SheafOfModules.pushforward φ`
is an isomorphism. -/
theorem isIso_unit_of_isIso_coefficient {S : Sheaf J RingCat.{r}}
    (φ : S ⟶ (f.sheafPushforwardContinuous RingCat.{r} J K).obj O) [IsIso φ]
    {P : SheafOfModules.{max uC vD w} S ⥤ SheafOfModules.{max uC vD w} O}
    (adj : P ⊣ pushforward.{max uC vD w} φ) : IsIso adj.unit := by
  have : (restrictScalars.{max uC vD w} (inv φ)).IsEquivalence :=
    (Stacks.SheafOfModules.RestrictScalars.equivalence.{max uC vD w} φ).isEquivalence_inverse
  have adj₂ := (pushforward₀DirectImageAdjunction.{r, w} f J K O).comp
    (Stacks.SheafOfModules.RestrictScalars.equivalence.{max uC vD w} φ).toAdjunction
  have hc : IsIso adj₂.counit := Adjunction.counit_isIso_of_R_fully_faithful _
  exact (Adjunction.Triple.isIso_unit_iff_isIso_counit ⟨adj, adj₂⟩).2 hc

end SheafOfModules

end
