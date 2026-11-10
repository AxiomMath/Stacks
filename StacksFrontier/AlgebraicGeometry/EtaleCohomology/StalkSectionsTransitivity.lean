module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.SpecializationStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkOfDerivedPushforward

/-!
# Transitivity of the map from an étale stalk to sections over the strict henselization

Let `X` be a scheme, `x` a geometric point of `X`, and let `T` be a scheme over the strict
henselization `Spec 𝒪^{sh}_{X,x}` with structure morphism `g : T ⟶ X`. The map

`F_x ⟶ Γ(T, g⁻¹F)`

of `AlgebraicGeometry.etaleStalkToSectionsAb` carries the germ at `x` of a section of an abelian
étale sheaf `F` over an étale neighbourhood `W` of `x` to its restriction along the composite
`T ⟶ Spec 𝒪^{sh}_{X,x} ⟶ W`. This file proves that the family of these maps is *transitive in
the scheme over the strict henselization*: if `T'` is another scheme over `Spec 𝒪^{sh}_{X,x}` and
`c : T' ⟶ T` is a morphism over it, then the map for `T'` is the map for `T` followed by
restriction of sections along `c`.

Restriction along `c` is `Stacks.EtaleCohomology.smallEtaleGlobalSectionsRestrictionAb`, which
lands in `Γ(T', c⁻¹g⁻¹F)`; the composition isomorphism
`Stacks.EtaleCohomology.smallEtalePullbackAbCompIso` identifies that with `Γ(T', (c ≫ g)⁻¹F)`.
The two together are `Stacks.EtaleCohomology.smallEtaleSectionsRestrictionAb`, and the
transitivity statement is `AlgebraicGeometry.etaleStalkToSectionsAb_comp_sectionsRestrictionAb`.

The existing transitivity statement
`Stacks.EtaleCohomology.map_comp_smallEtaleSectionsPullbackAb` is transitivity in the *étale
object*: restricting a section along a morphism `W ⟶ V` of étale neighbourhoods before pulling it
back. That is a different statement, and it is the one the construction of
`AlgebraicGeometry.etaleStalkToSectionsAb` out of the stalk needs; the transitivity proved here
is in the other variable, and it is what identifies the map for a tower of schemes over the
strict henselization.

## Main definitions

* `Stacks.EtaleCohomology.smallEtaleSectionsRestrictionAb` — restriction of global sections of an
  inverse image along a morphism `c : T' ⟶ T` of schemes over `Z`, from `Γ(T, g⁻¹F)` to
  `Γ(T', (g')⁻¹F)` for any `g'` with `c ≫ g = g'`.

## Main results

* `Stacks.Sites.unit_comp_leftAdjointUniq_app` — the units of two inverse-image/direct-image
  adjunctions for sites, composed and then compared with the unit of the adjunction for the
  composite site morphism through the canonical isomorphism of left adjoints, act on sections
  over an object as restriction along the comparison morphism of sites.
* `Stacks.Sites.sectionsPullbackComparison_comp` — transitivity of the comparison map on
  sections `Stacks.Sites.sectionsPullbackComparison` along a composite of continuous functors of
  sites, given that compatibility of the units.
* `Stacks.EtaleCohomology.smallEtaleBaseChangeLift_comp` — the morphism of étale objects
  determined by a section of a base change is transitive: the one for `T'` over the composite is
  the composite of the one for `T'` over `T` with the base change of the one for `T`, read
  through the base-change composition isomorphism.
* `Stacks.EtaleCohomology.smallEtaleSectionsPullbackAb_comp_sectionsRestrictionAb` — restriction
  of sections over an étale object to global sections of an inverse image is transitive in the
  scheme over the base.
* `AlgebraicGeometry.etaleStalkToSectionsAb_comp_sectionsRestrictionAb` — **the transitivity in
  the scheme over the strict henselization**: for `T' ⟶ T ⟶ Spec 𝒪^{sh}_{X,x}` the map
  `F_x ⟶ Γ(T', ·)` is the map `F_x ⟶ Γ(T, ·)` followed by restriction along `T' ⟶ T`.
* `AlgebraicGeometry.etaleStalkToSectionsAb_id_comp_sectionsRestrictionAb` — **[Stacks, Tag
  0GJ3]** the displayed composite of the source: the identification
  `F_s = Γ(Spec 𝒪^{sh}_{S,s}, p⁻¹F)`, followed by pullback by the geometric point `t` of
  `Spec 𝒪^{sh}_{S,s}`, is the specialization map followed by the identification
  `F_{t ≫ p} = Γ(t, (t ≫ p)⁻¹F)`.

## Implementation notes

*Why the adjunctions are the whole content.* The map on sections is
`Stacks.Sites.sectionsPullbackComparison`, the unit of the inverse-image/direct-image adjunction
of the sites followed by restriction along a morphism of the target site. Transitivity in the
scheme therefore unwinds to two facts: the unit of the adjunction for a composite agrees with the
composite of the units once the two left adjoints are identified, which is
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` because
`Stacks.EtaleCohomology.smallEtalePullbackAbCompIso` is by construction
`CategoryTheory.Adjunction.leftAdjointUniq` of the two conjugate adjunctions; and the geometric
statement that the chosen lifts into the base changes are compatible, which holds because a
morphism out of the identity object of a small étale site into a base change is determined by its
first projection.

*The hypothesis on the base morphism.* Restriction along `c : T' ⟶ T` produces sections of the
inverse image along `c ≫ g`, which for a tower over the strict henselization is
`c ≫ (q ≫ p)` rather than the `(c ≫ q) ≫ p` that
`AlgebraicGeometry.etaleStalkToSectionsAb` is indexed by.
`Stacks.EtaleCohomology.smallEtaleSectionsRestrictionAb` therefore takes the target base morphism
and a proof that it is the composite, as the two composition isomorphisms of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/StalkOfDerivedPushforward.lean` already do; the
transitivity statement supplies that proof from associativity.

*What this does not yet give.* The transitivity proved here is in one geometric point: the
schemes `T` and `T'` lie over the *same* strict henselization. Three further consumers need more
than that.

Stacks 0GJ8 compares the stalk at `s` with the stalk at a geometric point `t` of
`Spec 𝒪^{sh}_{S,s}`, so its square runs between two different strict henselizations. Reducing it
by `CategoryTheory.Functor.rightDerived_fac_app` leaves a square on sheaves whose two sides are
the maps of `AlgebraicGeometry.pushforwardStalkToStrictHenselizationSectionsAb` at `s` and at
`t ≫ p`; closing it needs, besides the transitivity proved here, the analogue of
`AlgebraicGeometry.etaleStalkToSectionsAb_id_comp_sectionsRestrictionAb` with the geometric point
`t` replaced by an arbitrary scheme over `Spec 𝒪^{sh}_{S,t ≫ p}`, the morphism `id_X × c` of base
changes built from the morphism of strict henselizations of Stacks 0GJ4, and the compatibility of
the two counits of the inverse-image/direct-image adjunction with it.

Stacks 0GIX's last assertion needs the base change map of Stacks 0E47 for the small étale sites
of schemes; the library has 0E47 only for ringed topoi, in the file
`BaseChangePastingOnRingedTopoi.lean` of the directory
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/`.

Stacks 0GJS needs the compatibility of `AlgebraicGeometry.vanishingCyclesFibreMap` with an
identification of varieties of vanishing cycles over *two* schemes `X` and `X'`, so again not the
transitivity proved here, and in addition the stalk base-change isomorphism for abelian sheaves,
recorded as missing in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/SmallEtaleStalkBaseChange.lean`.

## References

* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 0GJ3](https://stacks.math.columbia.edu/tag/0GJ3)
* [Stacks Project, Tag 0GJN](https://stacks.math.columbia.edu/tag/0GJN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.Sites

/-- A composite of two two-step composites, rewritten through four factorizations of its
constituents. This is the bookkeeping of
`Stacks.Sites.sectionsPullbackComparison_comp` separated from its content, so that the
associativity juggling happens in an arbitrary category rather than among sections of sheaves,
where the types of the morphisms involved agree only up to unfolding. -/
private theorem comp_fac {C : Type*} [Category C] {X B₁ B₂ D₁ D₂ D₃ E₁ E₂ E₃ : C}
    {u₁ : X ⟶ B₁} {mg : B₁ ⟶ B₂} {u₂ : B₂ ⟶ D₁} {mh : D₁ ⟶ D₂} {ee : D₂ ⟶ E₂}
    {u₂' : B₁ ⟶ D₃} {mG : D₃ ⟶ D₁} {mhg : D₃ ⟶ D₂} {ee' : D₃ ⟶ E₁} {m₃ : E₁ ⟶ E₂}
    {u₃ : X ⟶ E₃} {mv : E₃ ⟶ E₁} {mk : E₃ ⟶ E₂}
    (h₂ : mg ≫ u₂ = u₂' ≫ mG) (hm : mG ≫ mh = mhg) (h₃ : mhg ≫ ee = ee' ≫ m₃)
    (hu : u₁ ≫ u₂' ≫ ee' = u₃ ≫ mv) (hm₂ : mv ≫ m₃ = mk) :
    (u₁ ≫ mg) ≫ (u₂ ≫ mh) ≫ ee = u₃ ≫ mk :=
  calc (u₁ ≫ mg) ≫ (u₂ ≫ mh) ≫ ee = u₁ ≫ (mg ≫ u₂) ≫ mh ≫ ee := by simp
    _ = u₁ ≫ (u₂' ≫ mG) ≫ mh ≫ ee := by rw [h₂]
    _ = u₁ ≫ u₂' ≫ (mG ≫ mh) ≫ ee := by simp
    _ = u₁ ≫ u₂' ≫ mhg ≫ ee := by rw [hm]
    _ = u₁ ≫ u₂' ≫ ee' ≫ m₃ := by rw [h₃]
    _ = (u₁ ≫ u₂' ≫ ee') ≫ m₃ := by simp
    _ = (u₃ ≫ mv) ≫ m₃ := by rw [hu]
    _ = u₃ ≫ mv ≫ m₃ := by simp
    _ = u₃ ≫ mk := by rw [hm₂]

/-! ### Transitivity of the comparison map on sections -/

section Comparison

variable {C₁ : Type*} [Category C₁] {C₂ : Type*} [Category C₂] {C₃ : Type*} [Category C₃]
  (G₁ : C₁ ⥤ C₂) (G₂ : C₂ ⥤ C₃) (G₃ : C₁ ⥤ C₃) (A : Type*) [Category A]
  (J₁ : GrothendieckTopology C₁) (J₂ : GrothendieckTopology C₂) (J₃ : GrothendieckTopology C₃)
  [G₁.IsContinuous J₁ J₂] [G₂.IsContinuous J₂ J₃] [G₃.IsContinuous J₁ J₃]
  {P₁ : Sheaf J₁ A ⥤ Sheaf J₂ A} {P₂ : Sheaf J₂ A ⥤ Sheaf J₃ A} {P₃ : Sheaf J₁ A ⥤ Sheaf J₃ A}
  (adj₁ : P₁ ⊣ G₁.sheafPushforwardContinuous A J₁ J₂)
  (adj₂ : P₂ ⊣ G₂.sheafPushforwardContinuous A J₂ J₃)
  (adj₃ : P₃ ⊣ G₃.sheafPushforwardContinuous A J₁ J₃)

/-- **The unit of the adjunction for a composite of sites, on sections.** Let `G₁`, `G₂` be
continuous functors of sites with inverse-image functors `P₁`, `P₂`, let `G₃` be a continuous
functor isomorphic to `G₁ ⋙ G₂` by `ε` with inverse-image functor `P₃`, and identify
`P₁ ⋙ P₂` with `P₃` as left adjoints of the two isomorphic direct-image functors. Then on
sections over an object `U` the composite of the two units, followed by that identification, is
the unit of the third adjunction followed by restriction along `ε`.

This is `CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` read on sections, the direct
image being restriction along the functor of sites. -/
theorem unit_comp_leftAdjointUniq_app (ε : G₁ ⋙ G₂ ≅ G₃) (F : Sheaf J₁ A) (U : C₁) :
    (adj₁.unit.app F).hom.app (op U) ≫
        (adj₂.unit.app (P₁.obj F)).hom.app (op (G₁.obj U)) ≫
          ((Adjunction.leftAdjointUniq (adj₁.comp adj₂) (Adjunction.ofNatIsoRight adj₃
            (Functor.sheafPushforwardContinuousComp' ε A J₁ J₂ J₃).symm)).hom.app F).hom.app
              (op (G₂.obj (G₁.obj U))) =
      (adj₃.unit.app F).hom.app (op U) ≫ (P₃.obj F).obj.map (ε.hom.app U).op := by
  have hunit := congrArg (fun β : F ⟶ (G₂.sheafPushforwardContinuous A J₂ J₃ ⋙
      G₁.sheafPushforwardContinuous A J₁ J₂).obj (P₃.obj F) => β.hom.app (op U))
    (Adjunction.unit_leftAdjointUniq_hom_app (adj₁.comp adj₂)
      (Adjunction.ofNatIsoRight adj₃
        (Functor.sheafPushforwardContinuousComp' ε A J₁ J₂ J₃).symm) F)
  simp only [Adjunction.comp_unit_app, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Iso.symm_hom] at hunit
  simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Category.assoc,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Functor.sheafPushforwardContinuous_map_hom_app,
    Functor.sheafPushforwardContinuousComp'_inv_app_hom_app] at hunit
  exact hunit

/-- **Transitivity of the comparison map on sections along a composite of functors of sites.**
Comparing a section over `U` along `g : V ⟶ G₁.obj U` and then along `h : V' ⟶ G₂.obj V` is
comparing it along `k : V' ⟶ G₃.obj U`, provided `k` is `h` followed by the image of `g` and the
comparison morphism `ν` of the two functors `C₁ ⥤ C₃`, and provided the identification `e` of
`P₁ ⋙ P₂` with `P₃` is compatible with the units over `U` and `ν`.

`Stacks.Sites.unit_comp_leftAdjointUniq_app` supplies that compatibility for the identification
of left adjoints, which is the case of interest. -/
theorem sectionsPullbackComparison_comp (e : P₁ ⋙ P₂ ≅ P₃)
    {U : C₁} {V : C₂} {V' : C₃} (ν : G₂.obj (G₁.obj U) ⟶ G₃.obj U)
    (hν : ∀ F : Sheaf J₁ A,
      (adj₁.unit.app F).hom.app (op U) ≫ (adj₂.unit.app (P₁.obj F)).hom.app (op (G₁.obj U)) ≫
          (e.hom.app F).hom.app (op (G₂.obj (G₁.obj U))) =
        (adj₃.unit.app F).hom.app (op U) ≫ (P₃.obj F).obj.map ν.op)
    (g : V ⟶ G₁.obj U) (h : V' ⟶ G₂.obj V) (k : V' ⟶ G₃.obj U)
    (hk : (h ≫ G₂.map g) ≫ ν = k) :
    sectionsPullbackComparison G₁ A J₁ J₂ adj₁ g ≫
        Functor.whiskerLeft P₁ (sectionsPullbackComparison G₂ A J₂ J₃ adj₂ h) ≫
        Functor.whiskerRight e.hom ((sheafSections J₃ A).obj (op V')) =
      sectionsPullbackComparison G₃ A J₁ J₃ adj₃ k := by
  ext F
  have hm : (P₂.obj (P₁.obj F)).obj.map (G₂.map g).op ≫ (P₂.obj (P₁.obj F)).obj.map h.op =
      (P₂.obj (P₁.obj F)).obj.map (h ≫ G₂.map g).op := by
    rw [← Functor.map_comp, ← op_comp]
  have hm₂ : (P₃.obj F).obj.map ν.op ≫ (P₃.obj F).obj.map (h ≫ G₂.map g).op =
      (P₃.obj F).obj.map k.op := by
    rw [← Functor.map_comp, ← op_comp, hk]
  exact comp_fac ((adj₂.unit.app (P₁.obj F)).hom.naturality g.op) hm
    ((e.hom.app F).hom.naturality (h ≫ G₂.map g).op) (hν F) hm₂

end Comparison

/-- Transitivity of a comparison on sections is unchanged by conjugating the sections functors
of the two targets with isomorphisms, for instance the identification of global sections with
sections over a terminal object. This is the whiskering bookkeeping of
`Stacks.EtaleCohomology.smallEtaleSectionsPullbackAb_comp_sectionsRestrictionAb`. -/
private theorem whiskeredSectionsComparison_comp {S₁ : Type*} [Category S₁] {S₂ : Type*}
    [Category S₂] {S₃ : Type*} [Category S₃] {A : Type*} [Category A] {P₁ : S₁ ⥤ S₂}
    {P₂ : S₂ ⥤ S₃} {P₃ : S₁ ⥤ S₃} (e : P₁ ⋙ P₂ ≅ P₃) {Q : S₁ ⥤ A} {R₂ Γ₂ : S₂ ⥤ A}
    {R₃ Γ₃ : S₃ ⥤ A} (ι₂ : Γ₂ ≅ R₂) (ι₃ : Γ₃ ≅ R₃) (a₁ : Q ⟶ P₁ ⋙ R₂) (a₂ : R₂ ⟶ P₂ ⋙ R₃)
    (a₃ : Q ⟶ P₃ ⋙ R₃)
    (ha : a₁ ≫ Functor.whiskerLeft P₁ a₂ ≫ Functor.whiskerRight e.hom R₃ = a₃) :
    (a₁ ≫ Functor.whiskerLeft P₁ ι₂.inv) ≫
        (Functor.whiskerLeft P₁ (ι₂.hom ≫ a₂ ≫ Functor.whiskerLeft P₂ ι₃.inv) ≫
          Functor.whiskerRight e.hom Γ₃) =
      a₃ ≫ Functor.whiskerLeft P₃ ι₃.inv := by
  subst ha
  ext F
  simp

end Stacks.Sites

namespace Stacks.EtaleCohomology

/-! ### Base change of étale objects along a composite -/

section BaseChange

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (W : Z.Etale)

/-- The comparison of base change along a composite with the composite of the base changes is
compatible with the projections to the étale object: this is the content of the associativity of
fibre products that `Stacks.EtaleCohomology.smallEtaleBaseChangeComp` packages. -/
theorem smallEtaleBaseChangeComp_hom_app_left_fst :
    ((smallEtaleBaseChangeComp f g).hom.app W).left ≫
        pullback.fst (pullback.snd W.hom g) f ≫ pullback.fst W.hom g =
      pullback.fst W.hom (f ≫ g) := by
  let : MorphismProperty.HasPullbacksAlong
      (@Etale : MorphismProperty Scheme.{u}) f := ⟨fun _ _ ↦ inferInstance⟩
  let : MorphismProperty.HasPullbacksAlong
      (@Etale : MorphismProperty Scheme.{u}) g := ⟨fun _ _ ↦ inferInstance⟩
  let : MorphismProperty.IsStableUnderBaseChangeAlong
      (@Etale : MorphismProperty Scheme.{u}) f :=
    ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  let : MorphismProperty.IsStableUnderBaseChangeAlong
      (@Etale : MorphismProperty Scheme.{u}) g :=
    ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  simp only [smallEtaleBaseChangeComp]
  exact MorphismProperty.Over.pullbackComp_left_fst_fst f g W

/-- The inverse of `Stacks.EtaleCohomology.smallEtaleBaseChangeComp`, on first projections. -/
theorem smallEtaleBaseChangeComp_inv_app_left_fst :
    ((smallEtaleBaseChangeComp f g).inv.app W).left ≫ pullback.fst W.hom (f ≫ g) =
      pullback.fst (pullback.snd W.hom g) f ≫ pullback.fst W.hom g := by
  have hid : ((smallEtaleBaseChangeComp f g).inv.app W).left ≫
      ((smallEtaleBaseChangeComp f g).hom.app W).left = 𝟙 _ := by
    have h : (smallEtaleBaseChangeComp f g).inv.app W ≫
        (smallEtaleBaseChangeComp f g).hom.app W = 𝟙 _ := by
      rw [← NatTrans.comp_app, (smallEtaleBaseChangeComp f g).inv_hom_id]; rfl
    exact congrArg (fun m => m.left) h
  rw [← smallEtaleBaseChangeComp_hom_app_left_fst f g W, ← Category.assoc, hid,
    Category.id_comp]
  rfl

end BaseChange

/-! ### Transitivity of the lifts into a base change -/

section Lift

/-- A three-fold composite, rewritten through five factorizations of its constituents. This is
the bookkeeping of `Stacks.EtaleCohomology.smallEtaleBaseChangeLift_comp` separated from its
content, so that the associativity juggling happens in an arbitrary category rather than among
morphisms of étale objects, whose underlying objects are fibre products carrying instance
arguments that agree only up to proof irrelevance. -/
private theorem comp_fst_fac {C : Type*} [Category C] {A B D E G H I : C}
    {a : A ⟶ B} {b : B ⟶ D} {i : D ⟶ E} {f₁ : E ⟶ G} {f₂ : D ⟶ H} {f₃ : H ⟶ G}
    {f₀ : B ⟶ I} {l : I ⟶ H} {k : A ⟶ I} {m : I ⟶ G} {n : A ⟶ G}
    (h₁ : i ≫ f₁ = f₂ ≫ f₃) (h₂ : b ≫ f₂ = f₀ ≫ l) (h₃ : l ≫ f₃ = m)
    (h₄ : a ≫ f₀ = k) (h₅ : k ≫ m = n) :
    (a ≫ b ≫ i) ≫ f₁ = n :=
  calc (a ≫ b ≫ i) ≫ f₁ = a ≫ b ≫ i ≫ f₁ := by simp
    _ = a ≫ b ≫ f₂ ≫ f₃ := by rw [h₁]
    _ = a ≫ (b ≫ f₂) ≫ f₃ := by simp
    _ = a ≫ (f₀ ≫ l) ≫ f₃ := by rw [h₂]
    _ = (a ≫ f₀) ≫ l ≫ f₃ := by simp
    _ = k ≫ m := by rw [h₄, h₃]
    _ = n := h₅

variable {Z T T' : Scheme.{u}} (p : T ⟶ Z) (c : T' ⟶ T) (W : Z.Etale)

/-- A morphism from the identity object of the small étale site of `T` into the base change of an
étale object `W` along `p` is determined by its first projection to `W`: the second projection is
forced by the structure morphism. -/
theorem smallEtaleBaseChangeLift_eq (r : T ⟶ W.left) (hr : r ≫ W.hom = p)
    (m : Scheme.Etale.mk (𝟙 T) ⟶ (smallEtaleBaseChange p).obj W)
    (hm : m.left ≫ pullback.fst W.hom p = r) :
    m = smallEtaleBaseChangeLift p W r hr := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · exact hm.trans (pullback.lift_fst r (𝟙 T) (hr.trans (Category.id_comp p).symm)).symm
  · exact (MorphismProperty.Over.w m).trans
      (pullback.lift_snd r (𝟙 T) (hr.trans (Category.id_comp p).symm)).symm

/-- **Transitivity of the lifts into a base change.** The morphism of étale objects determined by
a morphism `r' = c ≫ r` into `W` over `c ≫ p` is the one determined by `c` over `p`, followed by
the base change along `c` of the one determined by `r`, read through the comparison of base
change along `c ≫ p` with the composite of the base changes. -/
theorem smallEtaleBaseChangeLift_comp (r : T ⟶ W.left) (hr : r ≫ W.hom = p)
    (r' : T' ⟶ W.left) (hr' : r' ≫ W.hom = c ≫ p) (hcr : c ≫ r = r') :
    (smallEtaleBaseChangeLift c (Scheme.Etale.mk (𝟙 T)) c (Category.comp_id c) ≫
        (smallEtaleBaseChange c).map (smallEtaleBaseChangeLift p W r hr)) ≫
        (smallEtaleBaseChangeComp c p).inv.app W =
      smallEtaleBaseChangeLift (c ≫ p) W r' hr' := by
  have hleft : ((smallEtaleBaseChangeLift c (Scheme.Etale.mk (𝟙 T)) c (Category.comp_id c) ≫
        (smallEtaleBaseChange c).map (smallEtaleBaseChangeLift p W r hr)) ≫
        (smallEtaleBaseChangeComp c p).inv.app W).left =
      (smallEtaleBaseChangeLift c (Scheme.Etale.mk (𝟙 T)) c (Category.comp_id c)).left ≫
        ((smallEtaleBaseChange c).map (smallEtaleBaseChangeLift p W r hr)).left ≫
        ((smallEtaleBaseChangeComp c p).inv.app W).left := by
    rw [Category.assoc]; rfl
  exact smallEtaleBaseChangeLift_eq (c ≫ p) W r' hr' _
    (hleft ▸ comp_fst_fac (smallEtaleBaseChangeComp_inv_app_left_fst c p W)
      (pullback.lift_fst _ _ _) (pullback.lift_fst _ _ _) (pullback.lift_fst _ _ _) hcr)

end Lift

/-! ### Restriction of sections of an inverse image along a morphism over the base -/

section Restriction

variable {Z T T' : Scheme.{u}} (g : T ⟶ Z) (c : T' ⟶ T) (g' : T' ⟶ Z)

/-- Restriction of global sections of an inverse image along a morphism `c : T' ⟶ T` of schemes
over `Z`: restrict the section along `c`, which gives a global section of `c⁻¹g⁻¹F` on `T'`, and
read that as a global section of `(g')⁻¹F` by the composition isomorphism for inverse images,
`g'` being the composite `c ≫ g`. -/
def smallEtaleSectionsRestrictionAb (hc : c ≫ g = g') :
    smallEtalePullbackAb g ⋙ Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1} ⟶
      smallEtalePullbackAb g' ⋙ Sheaf.Γ (smallEtaleTopology T') Ab.{u + 1} :=
  Functor.whiskerLeft (smallEtalePullbackAb g) (smallEtaleGlobalSectionsRestrictionAb c) ≫
    Functor.whiskerRight ((smallEtalePullbackAbCompIso c g).hom ≫
      eqToHom (congrArg (fun m : T' ⟶ Z => smallEtalePullbackAb m) hc))
      (Sheaf.Γ (smallEtaleTopology T') Ab.{u + 1})

/-- At the composite itself, restriction of sections is restriction along `c` followed by the
composition isomorphism for inverse images, with no transport. -/
theorem smallEtaleSectionsRestrictionAb_comp :
    smallEtaleSectionsRestrictionAb g c (c ≫ g) rfl =
      Functor.whiskerLeft (smallEtalePullbackAb g) (smallEtaleGlobalSectionsRestrictionAb c) ≫
        Functor.whiskerRight (smallEtalePullbackAbCompIso c g).hom
          (Sheaf.Γ (smallEtaleTopology T') Ab.{u + 1}) := by
  simp [smallEtaleSectionsRestrictionAb]

end Restriction

/-! ### Transitivity in the scheme over the base -/

section Transitivity

variable {Z T T' : Scheme.{u}} (p : T ⟶ Z) (W : Z.Etale) (c : T' ⟶ T) (p' : T' ⟶ Z)

/-- **Restriction of sections over an étale object is transitive in the scheme over the base.**
Restricting a section of an abelian étale sheaf over `W` to a global section of its inverse image
on `T` along `r`, and then restricting that along `c : T' ⟶ T`, is restricting the section
directly along `r' = c ≫ r`. -/
theorem smallEtaleSectionsPullbackAb_comp_sectionsRestrictionAb
    (r : T ⟶ W.left) (hr : r ≫ W.hom = p) (hc : c ≫ p = p')
    (r' : T' ⟶ W.left) (hr' : r' ≫ W.hom = p') (hcr : c ≫ r = r') :
    smallEtaleSectionsPullbackAb p W r hr ≫ smallEtaleSectionsRestrictionAb p c p' hc =
      smallEtaleSectionsPullbackAb p' W r' hr' := by
  subst hc
  rw [smallEtaleSectionsRestrictionAb_comp]
  exact Stacks.Sites.whiskeredSectionsComparison_comp (smallEtalePullbackAbCompIso c p)
    (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology T) Ab.{u + 1} (isTerminalEtaleMkId T))
    (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology T') Ab.{u + 1} (isTerminalEtaleMkId T'))
    (Stacks.Sites.sectionsPullbackComparison (smallEtaleBaseChange p) Ab.{u + 1}
      (smallEtaleTopology Z) (smallEtaleTopology T) (smallEtaleAdjunctionAb p)
      (smallEtaleBaseChangeLift p W r hr))
    (Stacks.Sites.sectionsPullbackComparison (smallEtaleBaseChange c) Ab.{u + 1}
      (smallEtaleTopology T) (smallEtaleTopology T') (smallEtaleAdjunctionAb c)
      (smallEtaleBaseChangeLift c (Scheme.Etale.mk (𝟙 T)) c (Category.comp_id c)))
    (Stacks.Sites.sectionsPullbackComparison (smallEtaleBaseChange (c ≫ p)) Ab.{u + 1}
      (smallEtaleTopology Z) (smallEtaleTopology T') (smallEtaleAdjunctionAb (c ≫ p))
      (smallEtaleBaseChangeLift (c ≫ p) W r' hr'))
    (Stacks.Sites.sectionsPullbackComparison_comp (smallEtaleBaseChange p)
      (smallEtaleBaseChange c) (smallEtaleBaseChange (c ≫ p)) Ab.{u + 1}
      (smallEtaleTopology Z) (smallEtaleTopology T) (smallEtaleTopology T')
      (smallEtaleAdjunctionAb p) (smallEtaleAdjunctionAb c) (smallEtaleAdjunctionAb (c ≫ p))
      (smallEtalePullbackAbCompIso c p) ((smallEtaleBaseChangeComp c p).symm.hom.app W)
      (fun F => Stacks.Sites.unit_comp_leftAdjointUniq_app (smallEtaleBaseChange p)
        (smallEtaleBaseChange c) (smallEtaleBaseChange (c ≫ p)) Ab.{u + 1}
        (smallEtaleTopology Z) (smallEtaleTopology T) (smallEtaleTopology T')
        (smallEtaleAdjunctionAb p) (smallEtaleAdjunctionAb c) (smallEtaleAdjunctionAb (c ≫ p))
        (smallEtaleBaseChangeComp c p).symm F W)
      (smallEtaleBaseChangeLift p W r hr)
      (smallEtaleBaseChangeLift c (Scheme.Etale.mk (𝟙 T)) c (Category.comp_id c))
      (smallEtaleBaseChangeLift (c ≫ p) W r' hr')
      (smallEtaleBaseChangeLift_comp p c W r hr r' hr' hcr))

end Transitivity

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

/-! ### Transitivity in the scheme over the strict henselization -/

section Stalk

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (x : GeometricPoint X)
  {T T' : Scheme.{u}} (q : T ⟶ strictHenselization B X hX x) (c : T' ⟶ T)
  (q' : T' ⟶ strictHenselization B X hX x)

/-- **The map from an étale stalk to sections is transitive in the scheme over the strict
henselization.** For schemes `T` and `T'` over `Spec 𝒪^{sh}_{X,x}` and a morphism `c : T' ⟶ T`
over it, the map `F_x ⟶ Γ(T', ·)` of Stacks 0GJN is the map `F_x ⟶ Γ(T, ·)` followed by
restriction of sections along `c`.

Both sides are maps out of the stalk at `x`, which is the colimit of the sections over the étale
neighbourhoods of `x`, so it suffices to compare them on a germ; there the statement is the
transitivity of restriction of sections over an étale object in the scheme over the base, the
chosen morphisms into the neighbourhood being compatible because `c ≫ q = q'`. -/
theorem etaleStalkToSectionsAb_comp_sectionsRestrictionAb (hq : c ≫ q = q') :
    etaleStalkToSectionsAb B X hX x q ≫
        smallEtaleSectionsRestrictionAb (q ≫ strictHenselizationToBase B X hX x) c
          (q' ≫ strictHenselizationToBase B X hX x)
          ((Category.assoc c q (strictHenselizationToBase B X hX x)).symm.trans
            (congrArg (fun y : T' ⟶ strictHenselization B X hX x =>
              y ≫ strictHenselizationToBase B X hX x) hq)) =
      etaleStalkToSectionsAb B X hX x q' := by
  ext F : 2
  refine smallEtaleStalkAb_hom_ext x.hom F fun W v => ?_
  refine (Category.assoc _ _ _).symm.trans
    ((congrArg (fun y => y ≫ _)
        (etaleStalkToSectionsAb_toPresheafFiber B X hX x q F W v)).trans
      ((congrArg (fun σ => NatTrans.app σ F)
          (smallEtaleSectionsPullbackAb_comp_sectionsRestrictionAb
            (q ≫ strictHenselizationToBase B X hX x) W c
            (q' ≫ strictHenselizationToBase B X hX x)
            (q ≫ strictHenselizationNeighborhoodLift B X hX x W v)
            (by rw [Category.assoc, strictHenselizationNeighborhoodLift_comp])
            ((Category.assoc c q (strictHenselizationToBase B X hX x)).symm.trans
              (congrArg (fun y : T' ⟶ strictHenselization B X hX x =>
                y ≫ strictHenselizationToBase B X hX x) hq))
            (q' ≫ strictHenselizationNeighborhoodLift B X hX x W v)
            (by rw [Category.assoc, strictHenselizationNeighborhoodLift_comp])
            (by rw [← Category.assoc, hq]))).trans
        (etaleStalkToSectionsAb_toPresheafFiber B X hX x q' F W v).symm))

end Stalk

/-! ### The displayed description of the specialization map -/

section Specialization

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
  (t : GeometricPoint (strictHenselization B S hS s))

/-- **Stacks 0GJ3, the displayed composite.** Let `S` be a scheme, `s` a geometric point of `S`,
`p : Spec(𝒪^{sh}_{S,s}) ⟶ S` the structure morphism of the strict henselization at `s`, and `t` a
geometric point of `Spec(𝒪^{sh}_{S,s})`. Then the identification
`F_s = Γ(Spec(𝒪^{sh}_{S,s}), p⁻¹F)` of Stacks 03Q9, followed by pullback of sections by `t`, is
the specialization map `sp : F_s ⟶ F_{t ≫ p}` followed by the identification
`F_{t ≫ p} = Γ(t, (t ≫ p)⁻¹F)` of Stacks 03Q1.

This is the source's displayed description of `sp` as pullback by `t`. The two identifications
are `AlgebraicGeometry.etaleStalkToSectionsAb` at the identity of the strict henselization and
`AlgebraicGeometry.geometricStalkToPullbackSectionsAb`; they are the canonical maps, which Stacks
03Q9 and 03Q1 assert are isomorphisms. -/
@[stacks 0GJ3 "the displayed composite: the identification of the stalk at `s` with sections over
the strict henselization, followed by pullback by `t`, is the specialization map followed by the
identification of the stalk at the specialized point with sections on that point. The two
identifications are the canonical maps; this statement compares them and does not assert that
either is invertible. Invertibility is Stacks 03Q1 and Stacks 03Q9. Of these the library carries
03Q1 for `Type`-valued sheaves, as `AlgebraicGeometry.smallEtalePullbackStalkIso`, and 03Q9 only
conditionally on the base being the spectrum of a strictly henselian local ring; neither is in
the abelian form and at the generality used here, so neither is applied."]
theorem etaleStalkToSectionsAb_id_comp_sectionsRestrictionAb :
    etaleStalkToSectionsAb B S hS s (𝟙 (strictHenselization B S hS s)) ≫
        smallEtaleSectionsRestrictionAb
          (𝟙 (strictHenselization B S hS s) ≫ strictHenselizationToBase B S hS s) t.hom
          (t.hom ≫ strictHenselizationToBase B S hS s)
          ((Category.assoc t.hom (𝟙 (strictHenselization B S hS s))
              (strictHenselizationToBase B S hS s)).symm.trans
            (congrArg (fun y : t.source ⟶ strictHenselization B S hS s =>
              y ≫ strictHenselizationToBase B S hS s) (Category.comp_id t.hom))) =
      smallEtaleSpecializationStalkAb B S hS s t ≫
        geometricStalkToPullbackSectionsAb (t.hom ≫ strictHenselizationToBase B S hS s) :=
  (etaleStalkToSectionsAb_comp_sectionsRestrictionAb B S hS s
      (𝟙 (strictHenselization B S hS s)) t.hom t.hom (Category.comp_id t.hom)).trans
    (etaleStalkToSectionsAb_eq_smallEtaleSpecializationStalkAb B S hS s t)

end Specialization

end AlgebraicGeometry

end
