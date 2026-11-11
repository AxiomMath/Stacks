module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Sites.Sheafification
public import StacksFrontier.CategoryTheory.Sites.Point.AbelianStalkExact
public import StacksFrontier.CategoryTheory.Sites.Point.StalkLeftAdjoint
import StacksCore.Tactic.StacksAttribute

/-!
# Points of a site in the sense of the Stacks project

Stacks 00Y5 defines a *point* of a site `C` to be a functor `u : C ⥤ Sets` such that

1. for every covering `{U_i → U}` the map `∐ u(U_i) → u(U)` is surjective;
2. for every covering `{U_i → U}` and every morphism `V → U` the maps
   `u(U_i ×_U V) → u(U_i) ×_{u(U)} u(V)` are bijective;
3. the stalk functor `Sh(C) ⥤ Sets`, `F ↦ F_p = colim_{(U, x)} F(U)`, is left exact.

This file defines these points, `GrothendieckTopology.SitePoint`, and shows that such a point
is a point of the site in Mathlib's sense (`GrothendieckTopology.Point`, the fibre functors of
SGA 4 IV 6.3) with the same fibre functor, hence with the same stalk functors on presheaves and
sheaves with values in any category. The difference between the two notions is that Mathlib asks
for the category of neighbourhoods `u.Elements` to be cofiltered; this is proved here from
(1), (2) and (3), following the proof of Stacks 04EN:

* the pushforward `u^p E = (U ↦ Map(u(U), E))` is a sheaf, by (1) and (2) (Stacks 00Y7);
* hence the stalk functor on sheaves is left adjoint to `E ↦ u^p E`, and so is the composite of
  sheafification with it; the stalk functor on presheaves, which is left adjoint to `u^p` as
  well (Stacks 00Y7), is therefore isomorphic to that composite (Stacks 00Y8), and is left exact
  by (3) and the exactness of sheafification (Stacks 00WJ);
* the stalk of the representable presheaf `h_U` is `u(U)` (Stacks 00Y6), and the left exactness
  of the stalk functor on the terminal presheaf, on products `h_U × h_V` and on equalizers of
  pairs `h_V ⇉ h_U` gives the three conditions for `u.Elements` to be cofiltered.

With this bridge, Stacks 04EP is proved for the points of this file.

## Main definitions

* `GrothendieckTopology.SitePoint`: a point of a site, Stacks 00Y5.
* `GrothendieckTopology.SitePoint.toPoint`: the point of the site in Mathlib's sense with the
  same fibre functor.

## Main results

* `GrothendieckTopology.SitePoint.isSheaf_presheafPushforward`: `u^p E` is a sheaf.
* `GrothendieckTopology.SitePoint.presheafStalkIso`: the stalk of a presheaf of sets is the stalk
  of its sheafification.
* `GrothendieckTopology.SitePoint.isCofiltered_elements`: the category of neighbourhoods of a
  point is cofiltered.
* `GrothendieckTopology.SitePoint.exactFunctor_abelianSheafStalk`,
  `GrothendieckTopology.SitePoint.exactFunctor_abelianPresheafStalk` and
  `GrothendieckTopology.SitePoint.isIso_abelianPresheafStalk_map_toSheafify`: Stacks 04EP.

## Implementation notes

* The site is a small category `C : Type w` with a Grothendieck topology `J`, and `Sets` is
  `Type w`. A category of the Stacks project has a set of objects and sets of morphisms
  (Stacks 0014), so this is the setting of the source, and it makes the colimits defining the
  stalks exist.
* A covering `{U_i → U}` is a family `f : ∀ i, U i ⟶ U` indexed by a set `I : Type w` whose
  sieve `Sieve.ofArrows U f` is a covering sieve of `J`. The source's axioms of a site
  (Stacks 00VH) ask that the fibre products `U_i ×_U V` of a covering exist; for a Grothendieck
  topology every family `{U' → U, id_U}` is a covering, so this is `HasPullbacks C`, which is
  what makes condition (2) expressible.
* The stalk functor of a functor `u : C ⥤ Type w` is `CategoryTheory.elementColimit u A`, the
  colimit of the sections of a presheaf over the opposite of `u.Elements` (Stacks 04EH); the
  stalk functor of `p.toPoint` is this functor on the nose.
* For abelian presheaves the stalk is the colimit in `AddCommGrpCat`; its underlying set is the
  stalk of the underlying presheaf of sets (`abelianPresheafStalkForgetIso`), which is how the
  source equips `F_p` with its group structure.

## References

* [Stacks Project, Tag 00Y5](https://stacks.math.columbia.edu/tag/00Y5)
* [Stacks Project, Tag 04EN](https://stacks.math.columbia.edu/tag/04EN)
* [Stacks Project, Tag 04EP](https://stacks.math.columbia.edu/tag/04EP)
-/

@[expose] public section

open CategoryTheory Limits Opposite PresheafPushforwardStalkAdjunction

universe w

namespace CategoryTheory.GrothendieckTopology

variable {C : Type w} [SmallCategory C] [HasPullbacks C] (J : GrothendieckTopology C)

/-- **Stacks 00Y5.** A point of the site `(C, J)`: a functor `u : C ⥤ Type w` such that

1. for every covering `{U_i → U}` the map `∐ u(U_i) → u(U)` is surjective;
2. for every covering `{U_i → U}` and every morphism `V → U` the maps
   `u(U_i ×_U V) → u(U_i) ×_{u(U)} u(V)` are bijective;
3. the stalk functor `Sh(C) ⥤ Sets`, `F ↦ F_p`, is left exact.

A covering is a family of morphisms indexed by a set whose sieve covers for `J`. -/
@[stacks 00Y5]
structure SitePoint where
  /-- The functor `u : C ⥤ Sets` of the point. -/
  fiber : C ⥤ Type w
  /-- Condition (1): for a covering `{U_i → U}` the map `∐ u(U_i) → u(U)` is surjective. -/
  surjective {I : Type w} {U : C} {Ui : I → C} (f : ∀ i, Ui i ⟶ U)
    (hf : Sieve.ofArrows Ui f ∈ J U) (x : fiber.obj U) :
    ∃ (i : I) (y : fiber.obj (Ui i)), fiber.map (f i) y = x
  /-- Condition (2): for a covering `{U_i → U}` and a morphism `V → U` the comparison maps
  `u(U_i ×_U V) → u(U_i) ×_{u(U)} u(V)` are bijective. -/
  bijective {I : Type w} {U : C} {Ui : I → C} (f : ∀ i, Ui i ⟶ U)
    (hf : Sieve.ofArrows Ui f ∈ J U) {V : C} (g : V ⟶ U) (i : I) :
    Function.Bijective (pullbackComparison fiber (f i) g)
  /-- Condition (3): the stalk functor on sheaves of sets is left exact. -/
  leftExact : PreservesFiniteLimits (sheafToPresheaf J (Type w) ⋙ presheafStalk fiber)

namespace SitePoint

variable {J} (p : J.SitePoint)

/-- Condition (1) of a point for covering sieves: every element of `u(U)` comes from `u(Y)`
along some arrow `Y ⟶ U` of a covering sieve of `U`. -/
lemma exists_of_mem {U : C} {S : Sieve U} (hS : S ∈ J U) (x : p.fiber.obj U) :
    ∃ (Y : C) (f : Y ⟶ U) (_ : S f) (y : p.fiber.obj Y), p.fiber.map f y = x := by
  obtain ⟨I, Y, f, rfl⟩ := S.exists_eq_ofArrows
  obtain ⟨i, y, hy⟩ := p.surjective f hS x
  exact ⟨_, f i, Sieve.ofArrows_mk _ _ i, y, hy⟩

/-- Condition (2) of a point in terms of elements: if `y ∈ u(U_i)` and `v ∈ u(V)` have the same
image in `u(U)`, they come from an element of `u(U_i ×_U V)`. -/
lemma exists_pullback {I : Type w} {U : C} {Ui : I → C} (f : ∀ i, Ui i ⟶ U)
    (hf : Sieve.ofArrows Ui f ∈ J U) {V : C} (g : V ⟶ U) (i : I)
    (y : p.fiber.obj (Ui i)) (v : p.fiber.obj V) (h : p.fiber.map (f i) y = p.fiber.map g v) :
    ∃ z : p.fiber.obj (Limits.pullback (f i) g),
      p.fiber.map (Limits.pullback.fst _ _) z = y ∧
        p.fiber.map (Limits.pullback.snd _ _) z = v := by
  obtain ⟨z, hz⟩ := (p.bijective f hf g i).2 ((Types.pullbackIsoPullback _ _).inv ⟨(y, v), h⟩)
  refine ⟨z, ?_, ?_⟩
  · have := congrArg (Limits.pullback.fst (p.fiber.map (f i)) (p.fiber.map g)) hz
    rw [← types_comp_apply (pullbackComparison _ _ _) (Limits.pullback.fst _ _),
      pullbackComparison_comp_fst] at this
    rw [this, Types.pullbackIsoPullback_inv_fst_apply]
  · have := congrArg (Limits.pullback.snd (p.fiber.map (f i)) (p.fiber.map g)) hz
    rw [← types_comp_apply (pullbackComparison _ _ _) (Limits.pullback.snd _ _),
      pullbackComparison_comp_snd] at this
    rw [this, Types.pullbackIsoPullback_inv_snd_apply]

/-- Two elements `y₁ ∈ u(Y₁)`, `y₂ ∈ u(Y₂)` lying over the same element of `u(U)` along arrows
`f₁, f₂` of a covering sieve come from a common element of `u(Y₁ ×_U Y₂)`. -/
lemma exists_pullback_of_mem {U : C} {S : Sieve U} (hS : S ∈ J U)
    {Y₁ Y₂ : C} {f₁ : Y₁ ⟶ U} {f₂ : Y₂ ⟶ U} (hf₁ : S f₁) (y₁ : p.fiber.obj Y₁)
    (y₂ : p.fiber.obj Y₂) (h : p.fiber.map f₁ y₁ = p.fiber.map f₂ y₂) :
    ∃ z : p.fiber.obj (Limits.pullback f₁ f₂),
      p.fiber.map (Limits.pullback.fst _ _) z = y₁ ∧
        p.fiber.map (Limits.pullback.snd _ _) z = y₂ := by
  let I : Type w := Σ Y : C, {f : Y ⟶ U // S f}
  have hI : Sieve.ofArrows (fun i : I => i.1) (fun i => i.2.1) ∈ J U :=
    J.superset_covering (fun Y f hf => Sieve.ofArrows_mk _ _ (⟨Y, f, hf⟩ : I)) hS
  exact p.exists_pullback (fun i : I => i.2.1) hI f₂ ⟨Y₁, f₁, hf₁⟩ y₁ y₂ h

/-- **Stacks 00Y7**, the sheaf property: for a point `p = u` and a set `E`, the presheaf
`u^p E : U ↦ Map(u(U), E)` is a sheaf. -/
theorem isSheaf_presheafPushforward (E : Type w) :
    Presheaf.IsSheaf J ((presheafPushforward p.fiber).obj E) := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro U S hS x hx
  -- Two representatives of the same element of `u(U)` give the same value.
  have key : ∀ {Y₁ Y₂ : C} {f₁ : Y₁ ⟶ U} {f₂ : Y₂ ⟶ U} (h₁ : S f₁) (h₂ : S f₂)
      (y₁ : p.fiber.obj Y₁) (y₂ : p.fiber.obj Y₂),
      p.fiber.map f₁ y₁ = p.fiber.map f₂ y₂ → x f₁ h₁ y₁ = x f₂ h₂ y₂ := by
    intro Y₁ Y₂ f₁ f₂ h₁ h₂ y₁ y₂ h
    obtain ⟨z, hz₁, hz₂⟩ := p.exists_pullback_of_mem hS h₁ y₁ y₂ h
    have := congrFun (hx (Limits.pullback.fst f₁ f₂) (Limits.pullback.snd f₁ f₂) h₁ h₂
      Limits.pullback.condition) z
    rw [presheafPushforward_obj_map_apply, presheafPushforward_obj_map_apply,
      Quiver.Hom.unop_op, Quiver.Hom.unop_op, hz₁, hz₂] at this
    exact this
  choose Y f hf y hy using fun a : p.fiber.obj U => p.exists_of_mem hS a
  refine ⟨fun a => x (f a) (hf a) (y a), fun Z g hg => ?_, fun t ht => ?_⟩
  · funext v
    rw [presheafPushforward_obj_map_apply, Quiver.Hom.unop_op]
    exact key _ _ _ _ (hy _)
  · funext a
    have := congrFun (ht (f a) (hf a)) (y a)
    rw [presheafPushforward_obj_map_apply, Quiver.Hom.unop_op, hy] at this
    exact this

/-- The skyscraper sheaf functor `E ↦ u^p E` of a point. -/
noncomputable def skyscraperSheafFunctor : Type w ⥤ Sheaf J (Type w) :=
  ObjectProperty.lift _ (presheafPushforward p.fiber) p.isSheaf_presheafPushforward

/-- The stalk functor on sheaves of sets is left adjoint to the skyscraper sheaf functor. -/
noncomputable def sheafStalkAdjunction :
    sheafToPresheaf J (Type w) ⋙ presheafStalk p.fiber ⊣ p.skyscraperSheafFunctor :=
  Adjunction.restrictFullyFaithful (iC := sheafToPresheaf J (Type w)) (iD := 𝟭 _)
    (adjunction p.fiber) (fullyFaithfulSheafToPresheaf J _) (Functor.FullyFaithful.id _)
    (Functor.rightUnitor _).symm (Functor.leftUnitor _)

/-- **Stacks 00Y8.** The stalk of a presheaf of sets at a point is the stalk of its
sheafification: both functors are left adjoint to `E ↦ u^p E`. -/
noncomputable def presheafStalkIso :
    presheafToSheaf J (Type w) ⋙ sheafToPresheaf J (Type w) ⋙ presheafStalk p.fiber ≅
      presheafStalk p.fiber :=
  ((sheafificationAdjunction J (Type w)).comp p.sheafStalkAdjunction).leftAdjointUniq
    (adjunction p.fiber)

/-- The stalk functor of a point on presheaves of sets is left exact. -/
instance preservesFiniteLimits_presheafStalk :
    PreservesFiniteLimits (presheafStalk p.fiber) := by
  have := p.leftExact
  exact preservesFiniteLimits_of_natIso p.presheafStalkIso

/-- The value of `thetaInv` on the class of `a : V ⟶ U` at the neighbourhood `(V, y)`. -/
lemma thetaInv_ι (U : C) (j : p.fiber.Elementsᵒᵖ) (a : j.unop.1 ⟶ U) :
    thetaInv p.fiber U (colimit.ι ((Functor.Elements.π p.fiber).op ⋙ yoneda.obj U) j a) =
      p.fiber.map a j.unop.2 := by
  unfold thetaInv
  rw [colimit.ι_desc_apply, thetaInvCocone_ι_app_apply]

/-- The category of neighbourhoods of a point is cofiltered. This follows from the left exactness
of the stalk functor on presheaves of sets, which the proof of Stacks 04EN deduces from
condition (3) of a point. -/
theorem isCofiltered_elements : IsCofiltered p.fiber.Elements := by
  refine
    { cone_objs := fun a b => ?_
      cone_maps := fun b a α β => ?_
      nonempty := ?_ }
  · -- The stalk of `h_U × h_V` is `u(U) × u(V)`.
    have hl := isLimitOfHasBinaryProductOfPreservesLimit (presheafStalk p.fiber)
      (yoneda.obj a.1) (yoneda.obj b.1)
    obtain ⟨l, hl₁, hl₂⟩ := BinaryFan.IsLimit.lift' hl
      (↾fun _ : PUnit.{w + 1} => theta p.fiber a.1 a.2)
      (↾fun _ : PUnit.{w + 1} => theta p.fiber b.1 b.2)
    obtain ⟨j, z, hz⟩ := Types.jointly_surjective'
      (F := (Functor.Elements.π p.fiber).op ⋙ (yoneda.obj a.1 ⨯ yoneda.obj b.1)) (l PUnit.unit)
    have e₁ : (presheafStalk p.fiber).map prod.fst (l PUnit.unit) = theta p.fiber a.1 a.2 :=
      ConcreteCategory.congr_hom hl₁ PUnit.unit
    have e₂ : (presheafStalk p.fiber).map prod.snd (l PUnit.unit) = theta p.fiber b.1 b.2 :=
      ConcreteCategory.congr_hom hl₂ PUnit.unit
    rw [← hz, presheafStalk_map_ι_apply] at e₁ e₂
    have h₁ := congrArg (thetaInv p.fiber a.1) e₁
    have h₂ := congrArg (thetaInv p.fiber b.1) e₂
    rw [thetaInv_ι, thetaInv_theta] at h₁ h₂
    exact ⟨j.unop, ⟨_, h₁⟩, ⟨_, h₂⟩, True.intro⟩
  · -- The stalk of the equalizer of `h_α, h_β : h_V ⇉ h_U`.
    have hl := isLimitOfHasEqualizerOfPreservesLimit (presheafStalk p.fiber)
      (yoneda.map α.1) (yoneda.map β.1)
    have hk : ∀ γ : b ⟶ a, (presheafStalk p.fiber).map (yoneda.map γ.1)
        (theta p.fiber b.1 b.2) = theta p.fiber a.1 a.2 := by
      intro γ
      rw [← theta_thetaInv p.fiber a.1 ((presheafStalk p.fiber).map _ _)]
      congr 1
      unfold theta stalkMk
      rw [presheafStalk_map_ι_apply, thetaInv_ι]
      simp
    obtain ⟨l, hl'⟩ := Fork.IsLimit.lift' hl
      (↾fun _ : PUnit.{w + 1} => theta p.fiber b.1 b.2) (by
        ext ⟨⟩
        exact (hk α).trans (hk β).symm)
    obtain ⟨j, z, hz⟩ := Types.jointly_surjective'
      (F := (Functor.Elements.π p.fiber).op ⋙ equalizer (yoneda.map α.1) (yoneda.map β.1))
      (l PUnit.unit)
    have e : (presheafStalk p.fiber).map (equalizer.ι (yoneda.map α.1) (yoneda.map β.1))
        (l PUnit.unit) = theta p.fiber b.1 b.2 :=
      ConcreteCategory.congr_hom hl' PUnit.unit
    rw [← hz, presheafStalk_map_ι_apply] at e
    have h := congrArg (thetaInv p.fiber b.1) e
    rw [thetaInv_ι, thetaInv_theta] at h
    refine ⟨j.unop, ⟨_, h⟩, ?_⟩
    apply Functor.Elements.hom_ext
    have := ConcreteCategory.congr_hom
      (NatTrans.congr_app (equalizer.condition (yoneda.map α.1) (yoneda.map β.1))
        (op j.unop.1)) z
    simpa using this
  · -- The stalk of the terminal presheaf is a point.
    have ht : IsTerminal ((presheafStalk p.fiber).obj (⊤_ (Cᵒᵖ ⥤ Type w))) :=
      IsTerminal.isTerminalObj _ _ terminalIsTerminal
    obtain ⟨j, -, -⟩ := Types.jointly_surjective'
      (F := (Functor.Elements.π p.fiber).op ⋙ ⊤_ (Cᵒᵖ ⥤ Type w))
      ((Types.isTerminalEquivUnique _ ht).default)
    exact ⟨j.unop⟩

/-- **Stacks 00Y5 and SGA 4 IV 6.3.** A point of the site in the sense of the Stacks project is a
point in Mathlib's sense, with the same fibre functor. -/
noncomputable def toPoint : J.Point.{w} where
  fiber := p.fiber
  isCofiltered := p.isCofiltered_elements
  initiallySmall := initiallySmall_of_essentiallySmall _
  jointly_surjective _ hR x := p.exists_of_mem hR x

@[simp]
lemma toPoint_fiber : p.toPoint.fiber = p.fiber := rfl

/-- The stalk functor on presheaves of the point `p.toPoint` is the stalk functor of `p`. -/
lemma toPoint_presheafFiber (A : Type*) [Category A] [HasColimitsOfSize.{w, w} A] :
    p.toPoint.presheafFiber (A := A) = elementColimit p.fiber A := rfl

/-- The stalk functor on sheaves of the point `p.toPoint` is the stalk functor of `p`. -/
lemma toPoint_sheafFiber (A : Type*) [Category A] [HasColimitsOfSize.{w, w} A] :
    p.toPoint.sheafFiber (A := A) = sheafToPresheaf J A ⋙ elementColimit p.fiber A := rfl

/-- The stalk of an abelian presheaf at a point, computed in `AddCommGrpCat`, has as underlying
set the stalk of the underlying presheaf of sets. This is the group structure on `F_p` of the
source. -/
noncomputable def abelianPresheafStalkForgetIso :
    (Functor.whiskeringRight _ _ _).obj (forget AddCommGrpCat.{w}) ⋙ presheafStalk p.fiber ≅
      elementColimit p.fiber AddCommGrpCat.{w} ⋙ forget AddCommGrpCat.{w} :=
  p.toPoint.presheafFiberCompIso (forget AddCommGrpCat.{w})

/-- **Stacks 04EP, part (1).** For a point `p` of a site, the stalk functor
`Ab(C) ⥤ Ab`, `F ↦ F_p`, is exact. -/
@[stacks 04EP "(1)"]
theorem exactFunctor_abelianSheafStalk :
    exactFunctor (Sheaf J AddCommGrpCat.{w}) AddCommGrpCat.{w}
      (sheafToPresheaf J AddCommGrpCat.{w} ⋙ elementColimit p.fiber AddCommGrpCat.{w}) :=
  Stacks.exactFunctor_abelianSheafFiber p.toPoint

/-- **Stacks 04EP, part (2).** For a point `p` of a site, the stalk functor
`PAb(C) ⥤ Ab`, `F ↦ F_p`, is exact. -/
@[stacks 04EP "(2)"]
theorem exactFunctor_abelianPresheafStalk :
    exactFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{w}) AddCommGrpCat.{w}
      (elementColimit p.fiber AddCommGrpCat.{w}) :=
  Stacks.exactFunctor_abelianPresheafFiber p.toPoint

/-- **Stacks 04EP, part (3).** For a point `p` of a site and an abelian presheaf `F`, the stalk
at `p` of the canonical map `F ⟶ F^#` is an isomorphism `F_p ≅ (F^#)_p`. -/
@[stacks 04EP "(3)"]
theorem isIso_abelianPresheafStalk_map_toSheafify (F : Cᵒᵖ ⥤ AddCommGrpCat.{w}) :
    IsIso ((elementColimit p.fiber AddCommGrpCat.{w}).map (CategoryTheory.toSheafify J F)) :=
  Stacks.isIso_abelianPresheafFiber_map_toSheafify p.toPoint F

end SitePoint

end CategoryTheory.GrothendieckTopology
