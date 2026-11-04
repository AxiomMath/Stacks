module

public import StacksFrontier.CategoryTheory.Sites.InverseSystem.CohomologyOfColimitOfFiniteSites
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.InjectiveSystemsOfAbelianSheaves
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.InverseImagesOfASingleSheaf
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.PushforwardCoherence
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.SystemTransitionCalculus
public import StacksFrontier.CategoryTheory.Sites.FreeRepresentableSheaf
public import StacksFrontier.Homology.Ext.MapExactFunctorComp

/-!
# `Ext` over a colimit of sites with finite coverings

Let `D` be an inverse system of sites with finite coverings (Stacks 0A34, 00VH), with colimit site
`C` (Stacks 09YL, 0A35), let `F` be a system of abelian sheaves on its levels (Stacks 0EXZ) and let
`𝒢` present `colim_j f_j⁻¹ F_j` on `C`. Stacks 09YP computes the cohomology of `𝒢` over an object
of `C` as the filtered colimit of the cohomologies of the `F_j`. This file states and proves the
`Ext`-form of that computation, for a *first variable* which is itself given at every level:

`colim_{A : Over i} Ext^n(𝒜_A, F_{A.left}) = Ext^n(𝒜_∞, 𝒢)`.

A `FirstVariable` over an index `i` is a family `𝒜_A` of abelian sheaves on the levels below `i`,
with comparison maps `𝒜_A ⟶ f⁻¹ 𝒜_B` for the arrows `f : A ⟶ B` of `Over i` satisfying the two
cocycle laws, an abelian sheaf `𝒜_∞` on the colimit site and compatible maps
`𝒜_∞ ⟶ u_{A}⁻¹ 𝒜_A`. Its transition maps on `Ext` are `Ext` along the exact inverse image,
conjugated by those comparison maps and by the transitions of `F`, and its legs are `Ext` along
the exact inverse image to the colimit site, conjugated by the legs of `𝒜` and of `F`.

## Main definitions

* `Stacks.WeakSites.ExtColimit.colimitPullback` — the inverse image to the colimit site.
* `Stacks.WeakSites.ExtColimit.colimitPullbackCompIso` — `f_a⁻¹ ⋙ u_k⁻¹ ≅ u_j⁻¹`.
* `Stacks.WeakSites.ExtColimit.systemLeg` — the leg `u_j⁻¹ F_j ⟶ 𝒢` of a colimit presentation.
* `Stacks.WeakSites.ExtColimit.FirstVariable` — the first variable.
* `Stacks.WeakSites.ExtColimit.extDiagram`, `Stacks.WeakSites.ExtColimit.extCocone` — the diagram
  `A ↦ Ext^n(𝒜_A, F_{A.left})` and its cocone at `Ext^n(𝒜_∞, 𝒢)`.
* `Stacks.WeakSites.ExtColimit.pullbackFirstVariable` — the first variable `A ↦ (A.hom)⁻¹ P`
  attached to an abelian sheaf `P` on the level `i`.

## Main results

* `Stacks.WeakSites.ExtColimit.systemLeg_compat` — the legs of a colimit presentation are
  compatible with the transitions of the system, in inverse-image form.
* `Stacks.WeakSites.ExtColimit.nonempty_isColimit_stdCocone` — if the `Ext` cocone is a colimit in
  degree zero for every system, and `Ext` out of `𝒜_∞` into the colimit sheaf of a pointwise
  injective system vanishes in positive degrees, then the `Ext` cocone is a colimit in every
  degree.

## Implementation notes

Asking for the comparison maps of `𝒜`, rather than deriving them from a single sheaf at the level
`i`, is what keeps the coherence out of the cocycle: the transitions of the `Ext` diagram compose
because those of `𝒜` and those of `F` do, each against the *same* composition isomorphism of
inverse images, which then cancels.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open CategoryTheory.Sites.InverseSystem

universe v u w a b

namespace Stacks.WeakSites.ExtColimit

open InverseSystemOfFiniteSites Stacks.Homology Stacks.WeakSites.ColimitSiteCohomology

/-- **The transpose of a transition of inverse images is invertible.** For adjunctions
`L ⊣ R`, `L' ⊣ R'`, `Lf ⊣ Pf` and a comparison `e : Pf ⋙ R ≅ R'`, the map `L F ⟶ Pf (L' F)`
transposing the unit of `L' ⊣ R'` read through `e` has, as its transpose `Lf (L F) ⟶ L' F`, the
canonical comparison of the two left adjoints of `R'`; in particular it is invertible. -/
theorem isIso_transpose_transition {S T T' : Type*} [Category S] [Category T] [Category T']
    {L : S ⥤ T} {R : T ⥤ S} (adj : L ⊣ R) {L' : S ⥤ T'} {R' : T' ⥤ S} (adj' : L' ⊣ R')
    {Lf : T ⥤ T'} {Pf : T' ⥤ T} (adjf : Lf ⊣ Pf) (e : Pf ⋙ R ≅ R') (F : S) :
    IsIso ((adjf.homEquiv _ _).symm
      ((adj.homEquiv F _).symm (adj'.unit.app F ≫ e.inv.app (L'.obj F)))) := by
  have hL : (adj.comp adjf).homEquiv F _ ((adjf.homEquiv _ _).symm
      ((adj.homEquiv F _).symm (adj'.unit.app F ≫ e.inv.app (L'.obj F)))) =
      adj'.unit.app F ≫ e.inv.app (L'.obj F) := by
    rw [Adjunction.comp_homEquiv]
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
  have hR : (adj.comp adjf).homEquiv F _
      ((Adjunction.leftAdjointCompIso adj adjf adj' e).hom.app F) =
      adj'.unit.app F ≫ e.inv.app (L'.obj F) := by
    rw [Adjunction.homEquiv_unit]
    exact (unit_conjugateEquiv_symm adj' (adj.comp adjf) e.inv F).symm
  rw [((adj.comp adjf).homEquiv F _).injective (hL.trans hR.symm)]
  exact NatIso.isIso_app_of_isIso _ F

/-- **A filtered colimit of abelian groups is recognised elementwise**: a cocone over a filtered
diagram is a colimit as soon as every element of its vertex comes from a stage and every element
of a stage that vanishes in the vertex vanishes at a further stage. -/
noncomputable def isColimitOfElementwise {J : Type a} [Category.{b} J] [IsFiltered J]
    {G : J ⥤ AddCommGrpCat.{w}} [HasColimit G] [PreservesColimit G (forget AddCommGrpCat.{w})]
    (c : Cocone G) (hsurj : ∀ x : c.pt, ∃ (j : J) (y : G.obj j), c.ι.app j y = x)
    (hzero : ∀ (j : J) (y : G.obj j), c.ι.app j y = 0 → ∃ (k : J) (f : j ⟶ k), G.map f y = 0) :
    IsColimit c :=
  haveI := reflectsColimit_of_reflectsIsomorphisms G (forget AddCommGrpCat.{w})
  isColimitOfReflects (forget AddCommGrpCat.{w})
    (Types.FilteredColimit.isColimitOf' _ _ (fun x => by
      obtain ⟨j, y, hy⟩ := hsurj x
      exact ⟨j, y, hy.symm⟩) (fun j x y h => by
      let x' : G.obj j := x
      let y' : G.obj j := y
      obtain ⟨k, f, hf⟩ := hzero j (x' - y') (by
        have e : c.ι.app j (x' - y') = c.ι.app j x' - c.ι.app j y' := map_sub _ _ _
        rw [e, sub_eq_zero]
        exact h)
      refine ⟨k, f, ?_⟩
      have e : G.map f (x' - y') = G.map f x' - G.map f y' := map_sub _ _ _
      rw [e, sub_eq_zero] at hf
      exact hf))

variable (D : InverseSystemOfFiniteSites.{v, u, max u v w})

/-- Inverse image along a transition of the system, at the coefficients of this file. -/
abbrev pb {i j : D.I} (a : i ⟶ j) :
    Sheaf (D.J j) Ab.{max u v w} ⥤ Sheaf (D.J i) Ab.{max u v w} :=
  abelianSheafPullback.{v, u, max u v w, max u v w} D a

/-- Inverse image along a transition of the system preserves finite limits. -/
instance pb_preservesFiniteLimits {i j : D.I} (a : i ⟶ j) :
    PreservesFiniteLimits (pb.{v, u, w} D a) := by
  let _ := D.continuous a
  have := InverseSystemOfFiniteSites.hasSheafifyAb.{v, u, max u v w, max u v w} D i
  exact Stacks.Sites.AbelianPullback.preservesFiniteLimits_sheafPullback_ab_largeSections
    (D.isMorphismOfSites a)

/-- Inverse image along a transition of the system preserves finite colimits. -/
instance pb_preservesFiniteColimits {i j : D.I} (a : i ⟶ j) :
    PreservesFiniteColimits (pb.{v, u, w} D a) :=
  have := (abelianSheafAdjunction.{v, u, max u v w, max u v w} D a).leftAdjoint_preservesColimits
  inferInstance

/-- Inverse image along a transition of the system is additive. -/
instance pb_additive {i j : D.I} (a : i ⟶ j) : (pb.{v, u, w} D a).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The abelian sheaves on each level have enough injectives. -/
theorem levelEnoughInjectives (i : D.I) : EnoughInjectives (Sheaf (D.J i) Ab.{max u v w}) :=
  enoughInjectives.{v, u, max u v w, max u v w} D i

/-- The abelian sheaves on each level have `Ext` groups in the universe `max u v w`. -/
theorem levelHasExt (i : D.I) : HasExt.{max u v w} (Sheaf (D.J i) Ab.{max u v w}) :=
  have := levelEnoughInjectives.{v, u, w} D i
  hasExt_of_enoughInjectives _

section ColimitSite

variable {C : Type (max u v w)} [SmallCategory C]
  (uC : ∀ i, D.C i ⥤ C) (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
  (K : Precoverage C) [∀ i, (uC i).IsContinuous (D.J i) K.toGrothendieck]

/-- Direct image to a level from the colimit site. -/
abbrev colimitPushforward (j : D.I) :
    Sheaf K.toGrothendieck Ab.{max u v w} ⥤ Sheaf (D.J j) Ab.{max u v w} :=
  (uC j).sheafPushforwardContinuous Ab.{max u v w} (D.J j) K.toGrothendieck

/-- Inverse image from a level to the colimit site. -/
abbrev colimitPullback (j : D.I) :
    Sheaf (D.J j) Ab.{max u v w} ⥤ Sheaf K.toGrothendieck Ab.{max u v w} :=
  (uC j).sheafPullback Ab.{max u v w} (D.J j) K.toGrothendieck

/-- The adjunction between inverse and direct image for a level and the colimit site. -/
abbrev colimitAdj (j : D.I) :
    colimitPullback.{v, u, w} D uC K j ⊣ colimitPushforward.{v, u, w} D uC K j :=
  (uC j).sheafAdjunctionContinuous Ab.{max u v w} (D.J j) K.toGrothendieck

/-- `u_k_* ⋙ f_{a,*} ≅ u_j_*`, read off the identity `u_a ⋙ u_k = u_j`. -/
def colimitPushforwardCompIso {k j : D.I} (a : k ⟶ j) :
    colimitPushforward.{v, u, w} D uC K k ⋙
        abelianSheafPushforward.{v, u, max u v w, max u v w} D a ≅
      colimitPushforward.{v, u, w} D uC K j :=
  letI := D.continuous a
  Functor.sheafPushforwardContinuousComp' (eqToIso (hu a)) Ab.{max u v w} (D.J j) (D.J k)
    K.toGrothendieck

/-- **`f_a⁻¹ ⋙ u_k⁻¹ ≅ u_j⁻¹`**: the comparison of inverse images to the colimit site, by
uniqueness of left adjoints. -/
def colimitPullbackCompIso {k j : D.I} (a : k ⟶ j) :
    pb.{v, u, w} D a ⋙ colimitPullback.{v, u, w} D uC K k ≅ colimitPullback.{v, u, w} D uC K j :=
  (((abelianSheafAdjunction.{v, u, max u v w, max u v w} D a).comp
    (colimitAdj.{v, u, w} D uC K k)).ofNatIsoRight
      (colimitPushforwardCompIso.{v, u, w} D uC hu K a)).leftAdjointUniq
    (colimitAdj.{v, u, w} D uC K j)

variable {D uC K}

omit [∀ i, (uC i).IsContinuous (D.J i) K.toGrothendieck] in
private theorem comp_comp_eqToHom_comp_eqToHom {𝒞 : Type*} [Category 𝒞] {X Y Z W : 𝒞}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h₁ : Z = W) (h₂ : W = Z) :
    (f ≫ g ≫ eqToHom h₁) ≫ eqToHom h₂ = f ≫ g := by
  simp

/-- The leg `u_j⁻¹ F_j ⟶ 𝒢` of a family `F_j ⟶ u_j_* 𝒢`, in inverse-image form. -/
def systemLeg {F : AbelianSheafSystem.{v, u, max u v w, max u v w} D}
    {𝒢 : Sheaf K.toGrothendieck Ab.{max u v w}} (ι : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ 𝒢.obj)
    (j : D.I) : (colimitPullback.{v, u, w} D uC K j).obj (F.obj j) ⟶ 𝒢 :=
  ((colimitAdj.{v, u, w} D uC K j).homEquiv _ _).symm ⟨ι j⟩

/-- **Legs in direct-image form compose with transitions, in inverse-image form.** For
`α : X ⟶ f_{a,*} Y`, `β : Y ⟶ u_{k,*} Z` and `γ : X ⟶ u_{j,*} Z` with `γ` the composite of `α`,
`f_{a,*} β` and the comparison `f_{a,*} u_{k,*} ≅ u_{j,*}`, the transposes satisfy
`u_j⁻¹ X ≅ u_k⁻¹ f_a⁻¹ X ⟶ u_k⁻¹ Y ⟶ Z` equals `u_j⁻¹ X ⟶ Z`. -/
theorem pullback_leg_compat {k j : D.I} (a : k ⟶ j) {X : Sheaf (D.J j) Ab.{max u v w}}
    {Y : Sheaf (D.J k) Ab.{max u v w}} {Z : Sheaf K.toGrothendieck Ab.{max u v w}}
    (α : X ⟶ (abelianSheafPushforward.{v, u, max u v w, max u v w} D a).obj Y)
    (β : Y ⟶ (colimitPushforward.{v, u, w} D uC K k).obj Z)
    (γ : X ⟶ (colimitPushforward.{v, u, w} D uC K j).obj Z)
    (h : γ = α ≫ (abelianSheafPushforward.{v, u, max u v w, max u v w} D a).map β ≫
      (colimitPushforwardCompIso.{v, u, w} D uC hu K a).hom.app Z) :
    (colimitPullbackCompIso.{v, u, w} D uC hu K a).inv.app X ≫
        (colimitPullback.{v, u, w} D uC K k).map
          (((abelianSheafAdjunction.{v, u, max u v w, max u v w} D a).homEquiv _ _).symm α) ≫
        ((colimitAdj.{v, u, w} D uC K k).homEquiv _ _).symm β =
      ((colimitAdj.{v, u, w} D uC K j).homEquiv _ _).symm γ := by
  apply ((colimitAdj.{v, u, w} D uC K j).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply,
    ← cancel_mono ((colimitPushforwardCompIso.{v, u, w} D uC hu K a).inv.app Z)]
  refine (leftAdjointUniq_ofNatIsoRight_homEquiv_inv
    (abelianSheafAdjunction.{v, u, max u v w, max u v w} D a) (colimitAdj.{v, u, w} D uC K k)
    (colimitAdj.{v, u, w} D uC K j) (colimitPushforwardCompIso.{v, u, w} D uC hu K a) _).trans ?_
  rw [Adjunction.comp_homEquiv, Equiv.trans_apply, Adjunction.homEquiv_naturality_left,
    Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply, h]
  simp

/-- **The legs of a compatible family are compatible with the transitions, in inverse-image
form**: `u_j⁻¹ F_j ≅ u_k⁻¹ f_a⁻¹ F_j ⟶ u_k⁻¹ F_k ⟶ 𝒢` is the leg at `j`. -/
theorem systemLeg_compat {F : AbelianSheafSystem.{v, u, max u v w, max u v w} D}
    {𝒢 : Sheaf K.toGrothendieck Ab.{max u v w}} (ι : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ 𝒢.obj)
    (hι : IsCompatible.{v, u, max u v w, max u v w} D uC hu F 𝒢.obj ι) {k j : D.I} (a : k ⟶ j) :
    (colimitPullbackCompIso.{v, u, w} D uC hu K a).inv.app (F.obj j) ≫
        (colimitPullback.{v, u, w} D uC K k).map (F.map a) ≫ systemLeg ι k =
      systemLeg ι j := by
  have hF : F.map a = ((abelianSheafAdjunction.{v, u, max u v w, max u v w} D a).homEquiv _ _).symm
      ((abelianSheafAdjunction.{v, u, max u v w, max u v w} D a).homEquiv _ _ (F.map a)) :=
    (Equiv.symm_apply_apply _ _).symm
  rw [hF]
  refine pullback_leg_compat hu a _ _ _ ?_
  apply Sheaf.hom_ext
  ext V : 2
  have hc := congrArg (fun q => q.app V) (hι a)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app] at hc
  let := D.continuous a
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app, NatTrans.comp_app]
  show (ι j).app V = _
  rw [hc, colimitPushforwardCompIso, sheafPushforwardContinuousComp'_hom_app_app, eqToHom_map]
  rfl

variable (D uC K) in
/-- **The first variable of the `Ext` colimit**, over the arrows into an index `i`, in
direct-image form: abelian sheaves `𝒜_A` on the levels below `i`, with transitions
`𝒜_B ⟶ f_{*} 𝒜_A` along the arrows `f : A ⟶ B` of `Over i` satisfying the identity and
composition laws, whose transposes `f⁻¹ 𝒜_B ⟶ 𝒜_A` are invertible; together with an abelian sheaf
`𝒜_∞` on the colimit site and compatible legs `𝒜_A ⟶ u_{A,*} 𝒜_∞` with invertible transposes. -/
structure FirstVariable (i : D.I) where
  /-- The sheaf at an arrow `A : Over i`. -/
  obj : ∀ A : Over i, Sheaf (D.J A.left) Ab.{max u v w}
  /-- The transition along an arrow of `Over i`, in direct-image form. -/
  φ : ∀ {A B : Over i} (f : A ⟶ B),
    obj B ⟶ (abelianSheafPushforward.{v, u, max u v w, max u v w} D f.left).obj (obj A)
  /-- The transition along an identity is the identity comparison of direct images. -/
  φ_id : ∀ A : Over i,
    φ (𝟙 A) = (abelianSheafPushforwardIdIso.{v, u, max u v w, max u v w} D A.left).hom.app (obj A)
  /-- The transition along a composite is the composite of the transitions. -/
  φ_comp : ∀ {A B E : Over i} (f : A ⟶ B) (g : B ⟶ E),
    φ (f ≫ g) = φ g ≫ (abelianSheafPushforward.{v, u, max u v w, max u v w} D g.left).map (φ f) ≫
      (abelianSheafPushforwardCompIso.{v, u, max u v w, max u v w} D f.left g.left).hom.app
        (obj A)
  /-- The transpose `f⁻¹ 𝒜_B ⟶ 𝒜_A` of each transition is invertible. -/
  isIso_φ : ∀ {A B : Over i} (f : A ⟶ B),
    IsIso (((abelianSheafAdjunction.{v, u, max u v w, max u v w} D f.left).homEquiv _ _).symm (φ f))
  /-- The sheaf on the colimit site. -/
  top : Sheaf K.toGrothendieck Ab.{max u v w}
  /-- The leg at an arrow `A : Over i`, in direct-image form. -/
  lg : ∀ A : Over i, obj A ⟶ (colimitPushforward.{v, u, w} D uC K A.left).obj top
  /-- The legs are compatible with the transitions. -/
  lg_comp : ∀ {A B : Over i} (f : A ⟶ B),
    lg B = φ f ≫ (abelianSheafPushforward.{v, u, max u v w, max u v w} D f.left).map (lg A) ≫
      (colimitPushforwardCompIso.{v, u, w} D uC hu K f.left).hom.app top
  /-- The transpose `u_A⁻¹ 𝒜_A ⟶ 𝒜_∞` of each leg is invertible. -/
  isIso_lg : ∀ A : Over i, IsIso (((colimitAdj.{v, u, w} D uC K A.left).homEquiv _ _).symm (lg A))

namespace FirstVariable

variable {hu} {i : D.I} (𝒜 : FirstVariable.{v, u, w} D uC hu K i)

/-- The transition of a first variable in inverse-image form, `f⁻¹ 𝒜_B ⟶ 𝒜_A`. -/
def ψ {A B : Over i} (f : A ⟶ B) : (pb.{v, u, w} D f.left).obj (𝒜.obj B) ⟶ 𝒜.obj A :=
  ((abelianSheafAdjunction.{v, u, max u v w, max u v w} D f.left).homEquiv _ _).symm (𝒜.φ f)

/-- The transition `ψ f` is an isomorphism. -/
instance {A B : Over i} (f : A ⟶ B) : IsIso (𝒜.ψ f) := 𝒜.isIso_φ f

/-- The comparison map `𝒜_A ⟶ f⁻¹ 𝒜_B`, the inverse of `ψ`. -/
def map {A B : Over i} (f : A ⟶ B) : 𝒜.obj A ⟶ (pb.{v, u, w} D f.left).obj (𝒜.obj B) :=
  inv (𝒜.ψ f)

/-- The inverse-image transition along an identity is the identity comparison of inverse images. -/
theorem ψ_id (A : Over i) :
    𝒜.ψ (𝟙 A) = (abelianSheafPullbackIdIso.{v, u, max u v w, max u v w} D A.left).hom.app
      (𝒜.obj A) := by
  rw [ψ, Equiv.symm_apply_eq, 𝒜.φ_id]
  symm
  exact Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ _

/-- The inverse-image transition along `f ≫ g` is `ψ g` and `ψ f` composed through the comparison
`(f ≫ g)⁻¹ ≅ f⁻¹ ∘ g⁻¹`. -/
theorem ψ_comp {A B E : Over i} (f : A ⟶ B) (g : B ⟶ E) :
    (abelianSheafPullbackCompIso.{v, u, max u v w, max u v w} D f.left g.left).inv.app
        (𝒜.obj E) ≫ (pb.{v, u, w} D f.left).map (𝒜.ψ g) ≫ 𝒜.ψ f = 𝒜.ψ (f ≫ g) := by
  show _ = ((abelianSheafAdjunction.{v, u, max u v w, max u v w} D (f.left ≫ g.left)).homEquiv
    _ _).symm (𝒜.φ (f ≫ g))
  apply (abelianSheafAdjunction.{v, u, max u v w, max u v w} D (f.left ≫ g.left)).homEquiv _ _
    |>.injective
  rw [Equiv.apply_symm_apply]
  dsimp only [abelianSheafPullbackCompIso]
  rw [Adjunction.homEquiv_leftAdjointUniq_inv_app_comp, Adjunction.homEquiv_ofNatIsoRight_apply,
    Adjunction.comp_homEquiv]
  show ((abelianSheafAdjunction.{v, u, max u v w, max u v w} D g.left).homEquiv _ _)
    (((abelianSheafAdjunction.{v, u, max u v w, max u v w} D f.left).homEquiv _ _)
      ((pb.{v, u, w} D f.left).map (𝒜.ψ g) ≫ 𝒜.ψ f)) ≫
      (abelianSheafPushforwardCompIso.{v, u, max u v w, max u v w} D f.left g.left).hom.app
        (𝒜.obj A) = _
  have e1 : (abelianSheafAdjunction.{v, u, max u v w, max u v w} D f.left).homEquiv _ _
      (𝒜.ψ f) = 𝒜.φ f := Equiv.apply_symm_apply _ _
  have e2 : (abelianSheafAdjunction.{v, u, max u v w, max u v w} D g.left).homEquiv _ _
      (𝒜.ψ g) = 𝒜.φ g := Equiv.apply_symm_apply _ _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right, e2, e1]
  exact (𝒜.φ_comp f g).symm

/-- The comparison map along an identity, followed by `id⁻¹ ≅ 𝟭`, is the identity. -/
theorem map_id (A : Over i) :
    𝒜.map (𝟙 A) ≫ (abelianSheafPullbackIdIso.{v, u, max u v w, max u v w} D A.left).hom.app
      (𝒜.obj A) = 𝟙 _ := by
  rw [map, IsIso.inv_comp_eq, Category.comp_id, ψ_id]

/-- The comparison map along `f ≫ g`, read through `(f ≫ g)⁻¹ ≅ f⁻¹ ∘ g⁻¹`, is `map f` followed by
`f⁻¹ (map g)`. -/
theorem map_comp {A B E : Over i} (f : A ⟶ B) (g : B ⟶ E) :
    𝒜.map (f ≫ g) ≫
        (abelianSheafPullbackCompIso.{v, u, max u v w, max u v w} D f.left g.left).inv.app
          (𝒜.obj E) =
      𝒜.map f ≫ (pb.{v, u, w} D f.left).map (𝒜.map g) := by
  rw [map, map, map, IsIso.inv_comp_eq, ← 𝒜.ψ_comp f g]
  simp

/-- The leg of a first variable in inverse-image form, `u_A⁻¹ 𝒜_A ⟶ 𝒜_∞`. -/
def legInv (A : Over i) : (colimitPullback.{v, u, w} D uC K A.left).obj (𝒜.obj A) ⟶ 𝒜.top :=
  ((colimitAdj.{v, u, w} D uC K A.left).homEquiv _ _).symm (𝒜.lg A)

/-- The leg `legInv A` is an isomorphism. -/
instance (A : Over i) : IsIso (𝒜.legInv A) := 𝒜.isIso_lg A

/-- The comparison map `𝒜_∞ ⟶ u_A⁻¹ 𝒜_A`, the inverse of `legInv`. -/
def leg (A : Over i) : 𝒜.top ⟶ (colimitPullback.{v, u, w} D uC K A.left).obj (𝒜.obj A) :=
  inv (𝒜.legInv A)

/-- The comparison legs `𝒜_∞ ⟶ u_A⁻¹ 𝒜_A` are compatible with the comparison maps of `𝒜`, through
`f⁻¹ ⋙ u_A⁻¹ ≅ u_B⁻¹`. -/
theorem leg_map {A B : Over i} (f : A ⟶ B) :
    𝒜.leg A ≫ (colimitPullback.{v, u, w} D uC K A.left).map (𝒜.map f) =
      𝒜.leg B ≫ (colimitPullbackCompIso.{v, u, w} D uC hu K f.left).inv.app (𝒜.obj B) := by
  have h := pullback_leg_compat hu f.left (𝒜.φ f) (𝒜.lg A) (𝒜.lg B) (𝒜.lg_comp f)
  change _ ≫ _ ≫ 𝒜.legInv A = 𝒜.legInv B at h
  rw [leg, leg, map, eq_comm, IsIso.inv_comp_eq, ← h]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  show _ = _ ≫ (colimitPullback.{v, u, w} D uC K A.left).map (𝒜.ψ f) ≫
    (colimitPullback.{v, u, w} D uC K A.left).map (inv (𝒜.ψ f))
  rw [← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]

end FirstVariable

variable {hu} [∀ j, PreservesFiniteLimits (colimitPullback.{v, u, w} D uC K j)]
  [∀ j, EnoughInjectives (Sheaf (D.J j) Ab.{max u v w})]
  [∀ j, HasExt.{max u v w} (Sheaf (D.J j) Ab.{max u v w})]

/-- Inverse image from a level to the colimit site preserves finite colimits. -/
instance colimitPullback_preservesFiniteColimits (j : D.I) :
    PreservesFiniteColimits (colimitPullback.{v, u, w} D uC K j) :=
  have := (colimitAdj.{v, u, w} D uC K j).leftAdjoint_preservesColimits
  inferInstance

/-- Inverse image from a level to the colimit site is additive. -/
instance colimitPullback_additive (j : D.I) : (colimitPullback.{v, u, w} D uC K j).Additive :=
  Functor.additive_of_preserves_binary_products _

variable [HasExt.{max u v w} (Sheaf K.toGrothendieck Ab.{max u v w})]

variable {i : D.I} (𝒜 : FirstVariable.{v, u, w} D uC hu K i)
  (F : AbelianSheafSystem.{v, u, max u v w, max u v w} D)
  {𝒢 : Sheaf K.toGrothendieck Ab.{max u v w}} (ι : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ 𝒢.obj)
  (n : ℕ)

/-- The transition of the `Ext` diagram along an arrow `f : A ⟶ B` of `Over i`: `Ext` along the
exact inverse image `f⁻¹`, conjugated by the comparison map of `𝒜` and the transition of `F`. -/
def extTransition {A B : Over i} (f : A ⟶ B) :
    Ext.{max u v w} (𝒜.obj B) (F.obj B.left) n →+ Ext.{max u v w} (𝒜.obj A) (F.obj A.left) n :=
  (extConjHom (𝒜.map f) (F.map f.left) n).comp ((pb.{v, u, w} D f.left).mapExtAddHom _ _ n)

omit [∀ j, PreservesFiniteLimits (colimitPullback.{v, u, w} D uC K j)]
  [∀ j, EnoughInjectives (Sheaf (D.J j) Ab.{max u v w})]
  [HasExt.{max u v w} (Sheaf K.toGrothendieck Ab.{max u v w})] in
/-- `extTransition` is `Ext` along `f⁻¹` followed by conjugation by `𝒜.map f` and
`F.map f.left`. -/
theorem extTransition_apply {A B : Over i} (f : A ⟶ B)
    (x : Ext.{max u v w} (𝒜.obj B) (F.obj B.left) n) :
    extTransition 𝒜 F n f x =
      extConj (𝒜.map f) (F.map f.left)
        (x.mapExactFunctor (pb.{v, u, w} D f.left) :
          Ext.{max u v w} ((pb.{v, u, w} D f.left).obj (𝒜.obj B))
            ((pb.{v, u, w} D f.left).obj (F.obj B.left)) n) := rfl

omit [∀ j, PreservesFiniteLimits (colimitPullback.{v, u, w} D uC K j)]
  [HasExt.{max u v w} (Sheaf K.toGrothendieck Ab.{max u v w})] in
/-- The transition of the `Ext` diagram along an identity is the identity. -/
theorem extTransition_id (A : Over i) (x : Ext.{max u v w} (𝒜.obj A) (F.obj A.left) n) :
    extTransition 𝒜 F n (𝟙 A) x = x := by
  rw [extTransition_apply]
  let α : pb.{v, u, w} D (Over.Hom.left (𝟙 A)) ≅ 𝟭 _ :=
    abelianSheafPullbackIdIso.{v, u, max u v w, max u v w} D A.left
  have h := ext_mapExactFunctor_of_iso' (pb.{v, u, w} D (Over.Hom.left (𝟙 A))) (𝟭 _) α x
  rw [ext_mapExactFunctor_id] at h
  have h' : (x.mapExactFunctor (pb.{v, u, w} D (Over.Hom.left (𝟙 A))) :
      Ext.{max u v w} ((pb.{v, u, w} D (Over.Hom.left (𝟙 A))).obj (𝒜.obj A))
        ((pb.{v, u, w} D (Over.Hom.left (𝟙 A))).obj (F.obj A.left)) n) =
      extConj (α.hom.app _) (α.inv.app _) x := by
    conv_rhs => rw [h]
    rw [extConj_extConj]
    simp [extConj_id]
  have hF : α.inv.app (F.obj A.left) ≫ F.map (Over.Hom.left (𝟙 A)) = 𝟙 _ := F.map_id A.left
  rw [h', extConj_extConj, 𝒜.map_id, hF, extConj_id]

omit [∀ j, PreservesFiniteLimits (colimitPullback.{v, u, w} D uC K j)]
  [HasExt.{max u v w} (Sheaf K.toGrothendieck Ab.{max u v w})] in
/-- The transition of the `Ext` diagram along `f ≫ g` is the composite of the transitions. -/
theorem extTransition_comp {A B E : Over i} (f : A ⟶ B) (g : B ⟶ E)
    (x : Ext.{max u v w} (𝒜.obj E) (F.obj E.left) n) :
    extTransition 𝒜 F n (f ≫ g) x = extTransition 𝒜 F n f (extTransition 𝒜 F n g x) := by
  simp only [extTransition_apply, extConj_mapExactFunctor]
  rw [← ext_mapExactFunctor_comp_functor (pb.{v, u, w} D g.left) (pb.{v, u, w} D f.left),
    extConj_extConj]
  show extConj (𝒜.map (f ≫ g)) (F.map (f.left ≫ g.left))
    (x.mapExactFunctor (pb.{v, u, w} D (f.left ≫ g.left))) = _
  rw [ext_mapExactFunctor_of_iso' (pb.{v, u, w} D g.left ⋙ pb.{v, u, w} D f.left)
    (pb.{v, u, w} D (f.left ≫ g.left))
    (abelianSheafPullbackCompIso.{v, u, max u v w, max u v w} D f.left g.left) x,
    extConj_extConj, 𝒜.map_comp, ← F.map_comp]
  simp

/-- **The `Ext` diagram** `A ↦ Ext^n(𝒜_A, F_{A.left})` over the arrows into `i`. -/
def extDiagram : (Over i)ᵒᵖ ⥤ Ab.{max u v w} where
  obj A := AddCommGrpCat.of (Ext.{max u v w} (𝒜.obj A.unop) (F.obj A.unop.left) n)
  map f := AddCommGrpCat.ofHom (extTransition 𝒜 F n f.unop)
  map_id A := by
    ext x
    exact extTransition_id 𝒜 F n A.unop x
  map_comp f g := by
    ext x
    exact extTransition_comp 𝒜 F n g.unop f.unop x

omit [∀ j, PreservesFiniteLimits (colimitPullback.{v, u, w} D uC K j)]
  [HasExt.{max u v w} (Sheaf K.toGrothendieck Ab.{max u v w})] in
/-- The maps of `extDiagram` are the transitions `extTransition`. -/
theorem extDiagram_map_apply {A B : (Over i)ᵒᵖ} (f : A ⟶ B)
    (x : Ext.{max u v w} (𝒜.obj A.unop) (F.obj A.unop.left) n) :
    (extDiagram 𝒜 F n).map f x = extTransition 𝒜 F n f.unop x := rfl

/-- The leg of the `Ext` cocone at an arrow `A : Over i`: `Ext` along the exact inverse image to
the colimit site, conjugated by the leg of `𝒜` and the leg of the presentation. -/
def extLeg (A : Over i) :
    Ext.{max u v w} (𝒜.obj A) (F.obj A.left) n →+ Ext.{max u v w} 𝒜.top 𝒢 n :=
  (extConjHom (𝒜.leg A) (systemLeg ι A.left) n).comp
    ((colimitPullback.{v, u, w} D uC K A.left).mapExtAddHom _ _ n)

omit [∀ j, EnoughInjectives (Sheaf (D.J j) Ab.{max u v w})] in
/-- `extLeg` is `Ext` along `u_A⁻¹` followed by conjugation by `𝒜.leg A` and
`systemLeg ι A.left`. -/
theorem extLeg_apply (A : Over i) (x : Ext.{max u v w} (𝒜.obj A) (F.obj A.left) n) :
    extLeg 𝒜 F ι n A x =
      extConj (𝒜.leg A) (systemLeg ι A.left)
        (x.mapExactFunctor (colimitPullback.{v, u, w} D uC K A.left) :
          Ext.{max u v w} ((colimitPullback.{v, u, w} D uC K A.left).obj (𝒜.obj A))
            ((colimitPullback.{v, u, w} D uC K A.left).obj (F.obj A.left)) n) := rfl

variable {F} in
/-- For a compatible family `ι`, the legs of the `Ext` cocone are compatible with its
transitions. -/
theorem extLeg_transition (hι : IsCompatible.{v, u, max u v w, max u v w} D uC hu F 𝒢.obj ι)
    {A B : Over i} (f : A ⟶ B) (x : Ext.{max u v w} (𝒜.obj B) (F.obj B.left) n) :
    extLeg 𝒜 F ι n A (extTransition 𝒜 F n f x) = extLeg 𝒜 F ι n B x := by
  rw [extLeg_apply, extTransition_apply, extConj_mapExactFunctor, extConj_extConj,
    ← ext_mapExactFunctor_comp_functor (pb.{v, u, w} D f.left)
      (colimitPullback.{v, u, w} D uC K A.left), extLeg_apply,
    ext_mapExactFunctor_of_iso' (pb.{v, u, w} D f.left ⋙ colimitPullback.{v, u, w} D uC K A.left)
      (colimitPullback.{v, u, w} D uC K B.left)
      (colimitPullbackCompIso.{v, u, w} D uC hu K f.left) x, extConj_extConj]
  congr 1
  · exact 𝒜.leg_map f
  · rw [← systemLeg_compat hu ι hι f.left, Iso.hom_inv_id_app_assoc]

/-- **The `Ext` cocone** at `Ext^n(𝒜_∞, 𝒢)`. -/
def extCocone (hι : IsCompatible.{v, u, max u v w, max u v w} D uC hu F 𝒢.obj ι) :
    Cocone (extDiagram 𝒜 F n) where
  pt := AddCommGrpCat.of (Ext.{max u v w} 𝒜.top 𝒢 n)
  ι :=
    { app A := AddCommGrpCat.ofHom (extLeg 𝒜 F ι n A.unop)
      naturality A B f := by
        ext x
        exact extLeg_transition 𝒜 ι n hι f.unop x }

section Naturality

variable {𝒜} {F F' : AbelianSheafSystem.{v, u, max u v w, max u v w} D}
  {𝒢 𝒢' : Sheaf K.toGrothendieck Ab.{max u v w}}
  {ι : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ 𝒢.obj} {ι' : ∀ j, (F'.obj j).obj ⟶ (uC j).op ⋙ 𝒢'.obj}

omit [∀ j, PreservesFiniteLimits (colimitPullback.{v, u, w} D uC K j)]
  [∀ j, EnoughInjectives (Sheaf (D.J j) Ab.{max u v w})]
  [HasExt.{max u v w} (Sheaf K.toGrothendieck Ab.{max u v w})] in
/-- The transitions of the `Ext` diagram are natural in the system. -/
theorem extTransition_postcomp (φ : AbelianSheafSystem.Hom F F') {A B : Over i} (f : A ⟶ B)
    (x : Ext.{max u v w} (𝒜.obj B) (F.obj B.left) n) :
    extTransition 𝒜 F' n f (extConj (𝟙 _) (φ.app B.left) x) =
      extConj (𝟙 _) (φ.app A.left) (extTransition 𝒜 F n f x) := by
  rw [extTransition_apply, extTransition_apply, extConj_mapExactFunctor, extConj_extConj,
    extConj_extConj, CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp,
    φ.naturality]

omit [∀ j, EnoughInjectives (Sheaf (D.J j) Ab.{max u v w})] in
/-- The legs of the `Ext` cocone are natural in the system, for a map of colimit sheaves
compatible with the legs. -/
theorem extLeg_postcomp (φ : AbelianSheafSystem.Hom F F') (ψ : 𝒢 ⟶ 𝒢')
    (hψ : ∀ j, systemLeg ι j ≫ ψ =
      (colimitPullback.{v, u, w} D uC K j).map (φ.app j) ≫ systemLeg ι' j)
    (A : Over i) (x : Ext.{max u v w} (𝒜.obj A) (F.obj A.left) n) :
    extLeg 𝒜 F' ι' n A (extConj (𝟙 _) (φ.app A.left) x) =
      extConj (𝟙 _) ψ (extLeg 𝒜 F ι n A x) := by
  rw [extLeg_apply, extLeg_apply, extConj_mapExactFunctor, extConj_extConj,
    extConj_extConj, CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp, hψ]

variable {Q : AbelianSheafSystem.{v, u, max u v w, max u v w} D}
  {𝒬 : Sheaf K.toGrothendieck Ab.{max u v w}} {κ : ∀ j, (Q.obj j).obj ⟶ (uC j).op ⋙ 𝒬.obj}

/-- The connecting class of a short exact sequence is natural for exact functors: a map
`τ : S.map G ⟶ S'` into a short exact sequence carries `x.comp (hS.extClass)` along `G` to the
composite of the image of `x` with `hS'.extClass`, up to conjugation. -/
private theorem extConj_mapExactFunctor_comp_extClass {C₁ C₂ : Type*} [Category C₁] [Category C₂]
    [Abelian C₁] [Abelian C₂] [HasExt.{a} C₁] [HasExt.{a} C₂]
    (G : C₁ ⥤ C₂) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {S : ShortComplex C₁} (hS : S.ShortExact) {S' : ShortComplex C₂} (hS' : S'.ShortExact)
    (τ : S.map G ⟶ S') {X : C₁} {X' : C₂} (a : X' ⟶ G.obj X) {n : ℕ}
    (x : Ext.{a} X S.X₃ n) :
    extConj a τ.τ₁ (((x.comp hS.extClass rfl).mapExactFunctor G :
        Ext.{a} (G.obj X) (G.obj S.X₁) (n + 1))) =
      (extConj a τ.τ₃ (x.mapExactFunctor G : Ext.{a} (G.obj X) (G.obj S.X₃) n)).comp
        hS'.extClass rfl := by
  have hnat := ShortComplex.ShortExact.extClass_naturality (hS.map_of_exact G) hS' τ
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
  simp only [extConj, Ext.comp_assoc_of_third_deg_zero]
  rw [hnat, ← Ext.comp_assoc_of_second_deg_zero]
  exact (Ext.comp_assoc _ _ _ (zero_add n) rfl (by lia)).symm

omit [∀ j, PreservesFiniteLimits (colimitPullback.{v, u, w} D uC K j)]
  [∀ j, EnoughInjectives (Sheaf (D.J j) Ab.{max u v w})]
  [HasExt.{max u v w} (Sheaf K.toGrothendieck Ab.{max u v w})] in
/-- **The transitions of the `Ext` diagram commute with the connecting maps** of a short exact
sequence of systems `F ⟶ F' ⟶ Q`. -/
theorem extTransition_delta (φ : AbelianSheafSystem.Hom F F') (π : AbelianSheafSystem.Hom F' Q)
    (w : ∀ j, φ.app j ≫ π.app j = 0)
    (hS : ∀ j, (ShortComplex.mk (φ.app j) (π.app j) (w j)).ShortExact)
    {A B : Over i} (f : A ⟶ B) (x : Ext.{max u v w} (𝒜.obj B) (Q.obj B.left) n) :
    extTransition 𝒜 F (n + 1) f (x.comp (hS B.left).extClass rfl) =
      (extTransition 𝒜 Q n f x).comp (hS A.left).extClass rfl := by
  let τ : (ShortComplex.mk (φ.app B.left) (π.app B.left) (w B.left)).map (pb.{v, u, w} D f.left) ⟶
      ShortComplex.mk (φ.app A.left) (π.app A.left) (w A.left) :=
    { τ₁ := F.map f.left
      τ₂ := F'.map f.left
      τ₃ := Q.map f.left
      comm₁₂ := (φ.naturality f.left).symm
      comm₂₃ := (π.naturality f.left).symm }
  rw [extTransition_apply, extTransition_apply]
  exact extConj_mapExactFunctor_comp_extClass (C₁ := Sheaf (D.J B.left) Ab.{max u v w})
    (C₂ := Sheaf (D.J A.left) Ab.{max u v w}) (pb.{v, u, w} D f.left) (hS B.left) (hS A.left) τ
    (𝒜.map f) x

omit [∀ j, EnoughInjectives (Sheaf (D.J j) Ab.{max u v w})] in
/-- **The legs of the `Ext` cocone commute with the connecting maps** of a short exact sequence of
systems and a short exact sequence of colimit sheaves compatible with it. -/
theorem extLeg_delta (φ : AbelianSheafSystem.Hom F F') (π : AbelianSheafSystem.Hom F' Q)
    (w : ∀ j, φ.app j ≫ π.app j = 0)
    (hS : ∀ j, (ShortComplex.mk (φ.app j) (π.app j) (w j)).ShortExact)
    (ψ : 𝒢 ⟶ 𝒢') (ϖ : 𝒢' ⟶ 𝒬) (w' : ψ ≫ ϖ = 0) (hS' : (ShortComplex.mk ψ ϖ w').ShortExact)
    (hψ : ∀ j, systemLeg ι j ≫ ψ =
      (colimitPullback.{v, u, w} D uC K j).map (φ.app j) ≫ systemLeg ι' j)
    (hϖ : ∀ j, systemLeg ι' j ≫ ϖ =
      (colimitPullback.{v, u, w} D uC K j).map (π.app j) ≫ systemLeg κ j)
    (A : Over i) (x : Ext.{max u v w} (𝒜.obj A) (Q.obj A.left) n) :
    extLeg 𝒜 F ι (n + 1) A (x.comp (hS A.left).extClass rfl) =
      (extLeg 𝒜 Q κ n A x).comp hS'.extClass rfl := by
  let τ : (ShortComplex.mk (φ.app A.left) (π.app A.left) (w A.left)).map
      (colimitPullback.{v, u, w} D uC K A.left) ⟶ ShortComplex.mk ψ ϖ w' :=
    { τ₁ := systemLeg ι A.left
      τ₂ := systemLeg ι' A.left
      τ₃ := systemLeg κ A.left
      comm₁₂ := hψ A.left
      comm₂₃ := hϖ A.left }
  rw [extLeg_apply, extLeg_apply]
  exact extConj_mapExactFunctor_comp_extClass (C₁ := Sheaf (D.J A.left) Ab.{max u v w})
    (C₂ := Sheaf K.toGrothendieck Ab.{max u v w}) (colimitPullback.{v, u, w} D uC K A.left)
    (hS A.left) hS' τ (𝒜.leg A) x

omit [∀ j, PreservesFiniteLimits (colimitPullback.{v, u, w} D uC K j)]
  [∀ j, EnoughInjectives (Sheaf (D.J j) Ab.{max u v w})]
  [HasExt.{max u v w} (Sheaf K.toGrothendieck Ab.{max u v w})] in
omit [∀ j, PreservesFiniteLimits (colimitPullback.{v, u, w} D uC K j)]
  [∀ j, EnoughInjectives (Sheaf (D.J j) Ab.{max u v w})]
  [HasExt.{max u v w} (Sheaf K.toGrothendieck Ab.{max u v w})] in
/-- Equal classes have equal images under the connecting map of a short exact sequence of
systems. -/
theorem comp_extClass_congr (φ : AbelianSheafSystem.Hom F F')
    (π : AbelianSheafSystem.Hom F' Q) (w : ∀ j, φ.app j ≫ π.app j = 0)
    (hS : ∀ j, (ShortComplex.mk (φ.app j) (π.app j) (w j)).ShortExact) (j : D.I)
    {X : Sheaf (D.J j) Ab.{max u v w}} {y y' : Ext.{max u v w} X (Q.obj j) n} (h : y = y') :
    y.comp (hS j).extClass rfl = y'.comp (hS j).extClass rfl := by
  rw [h]

omit [∀ j, PreservesFiniteLimits (colimitPullback.{v, u, w} D uC K j)]
  [∀ j, EnoughInjectives (Sheaf (D.J j) Ab.{max u v w})]
  [HasExt.{max u v w} (Sheaf K.toGrothendieck Ab.{max u v w})] in
/-- A class pushed along the epimorphism of a short exact sequence of systems dies under the
connecting map of that sequence. -/
theorem extConj_comp_extClass_eq_zero (φ : AbelianSheafSystem.Hom F F')
    (π : AbelianSheafSystem.Hom F' Q) (w : ∀ j, φ.app j ≫ π.app j = 0)
    (hS : ∀ j, (ShortComplex.mk (φ.app j) (π.app j) (w j)).ShortExact) (j : D.I)
    {X : Sheaf (D.J j) Ab.{max u v w}} (y : Ext.{max u v w} X (F'.obj j) n) :
    (extConj (𝟙 X) (π.app j) y).comp (hS j).extClass rfl = 0 := by
  rw [extConj_id_left, Ext.comp_assoc_of_second_deg_zero,
    show (Ext.mk₀ (π.app j)).comp (hS j).extClass (zero_add 1) = 0 from (hS j).comp_extClass,
    Ext.comp_zero]

omit [∀ j, PreservesFiniteLimits (colimitPullback.{v, u, w} D uC K j)]
  [HasExt.{max u v w} (Sheaf K.toGrothendieck Ab.{max u v w})] in
/-- **The vanishing step of dimension shifting**, on the levels: for a short exact sequence
`F ⟶ F' ⟶ Q` of systems, if the transitions of `zA` and of the image of `wB` agree along `g`,
then the connecting image of `zA` dies along `g ≫ fA`. -/
theorem extTransition_extClass_eq_zero (φ : AbelianSheafSystem.Hom F F')
    (π : AbelianSheafSystem.Hom F' Q) (w : ∀ j, φ.app j ≫ π.app j = 0)
    (hS : ∀ j, (ShortComplex.mk (φ.app j) (π.app j) (w j)).ShortExact)
    {A B E E' : Over i} (g : E' ⟶ E) (fA : E ⟶ A) (fB : E ⟶ B)
    (zA : Ext.{max u v w} (𝒜.obj A) (Q.obj A.left) n)
    (wB : Ext.{max u v w} (𝒜.obj B) (F'.obj B.left) n)
    (hg : extTransition 𝒜 Q n g (extTransition 𝒜 Q n fA zA) =
      extTransition 𝒜 Q n g (extConj (𝟙 _) (π.app E.left) (extTransition 𝒜 F' n fB wB))) :
    extTransition 𝒜 F (n + 1) (g ≫ fA) (zA.comp (hS A.left).extClass rfl) = 0 := by
  rw [extTransition_delta n φ π w hS (g ≫ fA) zA, extTransition_comp, hg,
    extTransition_postcomp n π g]
  exact extConj_comp_extClass_eq_zero n φ π w hS E'.left _

end Naturality

section DimensionShifting

variable (hu)

variable (hobj : ∀ Y : C, ∃ (i : D.I) (Z : D.C i), (uC i).obj Z = Y)
  (hhom : ∀ (i : D.I) (Y Z : D.C i) (f : (uC i).obj Y ⟶ (uC i).obj Z),
    ∃ (j : D.I) (a : j ⟶ i) (g : (D.u a).obj Y ⟶ (D.u a).obj Z),
      (uC j).map g =
        eqToHom (Functor.congr_obj (hu a) Y) ≫ f ≫ eqToHom (Functor.congr_obj (hu a) Z).symm)
  (hhom_inj : ∀ (i : D.I) (Y Z : D.C i) (g₁ g₂ : Y ⟶ Z),
    (uC i).map g₁ = (uC i).map g₂ →
      ∃ (j : D.I) (a : j ⟶ i), (D.u a).map g₁ = (D.u a).map g₂)
  (hK : ∀ (Y : C) (R : Presieve Y),
    R ∈ K Y ↔
      ∃ (i : D.I) (Z : D.C i) (h : (uC i).obj Z = Y) (S : Presieve Z),
        S ∈ (D.J i).toPrecoverage Z ∧ S ∈ Precoverage.finite (D.C i) Z ∧
          R = h ▸ S.map (uC i))

/-- The legs of the constructed colimit sheaf of a system. -/
def kanLegs (F : AbelianSheafSystem.{v, u, max u v w, max u v w} D) (j : D.I) :
    (F.obj j).obj ⟶ (uC j).op ⋙ (systemColimitSheaf D uC hu hobj hhom hhom_inj K hK F).obj :=
  systemKanUnit D uC hu F j

omit [∀ i, (uC i).IsContinuous (D.J i) K.toGrothendieck]
  [∀ j, PreservesFiniteLimits (colimitPullback.{v, u, w} D uC K j)]
  [∀ j, EnoughInjectives (Sheaf (D.J j) Ab.{max u v w})]
  [∀ j, HasExt.{max u v w} (Sheaf (D.J j) Ab.{max u v w})]
  [HasExt.{max u v w} (Sheaf K.toGrothendieck Ab.{max u v w})] in
/-- The legs of the constructed colimit sheaf of a system form a compatible family. -/
theorem kanLegs_compatible (F : AbelianSheafSystem.{v, u, max u v w, max u v w} D) :
    IsCompatible.{v, u, max u v w, max u v w} D uC hu F
      (systemColimitSheaf D uC hu hobj hhom hhom_inj K hK F).obj
      (kanLegs hu hobj hhom hhom_inj hK F) :=
  (systemColimitSheaf_isColimitPresentation D uC hu hobj hhom hhom_inj K hK F).1

variable {i : D.I} (𝒜 : FirstVariable.{v, u, w} D uC hu K i)

/-- The `Ext` cocone of a system at its constructed colimit sheaf. -/
abbrev stdCocone (n : ℕ) (F : AbelianSheafSystem.{v, u, max u v w, max u v w} D) :
    Cocone (extDiagram 𝒜 F n) :=
  extCocone 𝒜 F (kanLegs hu hobj hhom hhom_inj hK F) n
    (kanLegs_compatible hu hobj hhom hhom_inj hK F)

omit [∀ j, PreservesFiniteLimits (colimitPullback.{v, u, w} D uC K j)]
  [∀ j, EnoughInjectives (Sheaf (D.J j) Ab.{max u v w})]
  [∀ j, HasExt.{max u v w} (Sheaf (D.J j) Ab.{max u v w})]
  [HasExt.{max u v w} (Sheaf K.toGrothendieck Ab.{max u v w})] in
/-- A map of colimit sheaves compatible with the structure maps, on presheaves, is compatible with
the legs in inverse-image form. -/
theorem systemLeg_comp_of_fac {F G : AbelianSheafSystem.{v, u, max u v w, max u v w} D}
    (f : AbelianSheafSystem.Hom F G)
    (ψ : systemColimitSheaf D uC hu hobj hhom hhom_inj K hK F ⟶
      systemColimitSheaf D uC hu hobj hhom hhom_inj K hK G)
    (hψ : ∀ j, systemKanUnit D uC hu F j ≫ Functor.whiskerLeft (uC j).op ψ.hom =
      (f.app j).hom ≫ systemKanUnit D uC hu G j) (j : D.I) :
    systemLeg (kanLegs hu hobj hhom hhom_inj hK F) j ≫ ψ =
      (colimitPullback.{v, u, w} D uC K j).map (f.app j) ≫
        systemLeg (kanLegs hu hobj hhom hhom_inj hK G) j := by
  have hF : (colimitAdj.{v, u, w} D uC K j).homEquiv _ _
      (systemLeg (kanLegs hu hobj hhom hhom_inj hK F) j) = ⟨kanLegs hu hobj hhom hhom_inj hK F j⟩ :=
    Equiv.apply_symm_apply _ _
  have hG : (colimitAdj.{v, u, w} D uC K j).homEquiv _ _
      (systemLeg (kanLegs hu hobj hhom hhom_inj hK G) j) = ⟨kanLegs hu hobj hhom hhom_inj hK G j⟩ :=
    Equiv.apply_symm_apply _ _
  apply ((colimitAdj.{v, u, w} D uC K j).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left, hF, hG]
  exact Sheaf.hom_ext (hψ j)

variable {hu 𝒜 hobj hhom hhom_inj hK} in
/-- If `stdCocone` is a colimit, every class in `Ext^n(𝒜_∞, 𝒢)` is the image of a class at some
level. -/
theorem exists_leg_eq {n : ℕ} {F : AbelianSheafSystem.{v, u, max u v w, max u v w} D}
    (hc : IsColimit (stdCocone hu hobj hhom hhom_inj hK 𝒜 n F))
    (y : Ext.{max u v w} 𝒜.top (systemColimitSheaf D uC hu hobj hhom hhom_inj K hK F) n) :
    ∃ (A : Over i) (x : Ext.{max u v w} (𝒜.obj A) (F.obj A.left) n),
      extLeg 𝒜 F (kanLegs hu hobj hhom hhom_inj hK F) n A x = y := by
  have : PreservesFilteredColimitsOfSize.{v, max u v} (forget Ab.{max u v w}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max u v w, max u v w} _
  obtain ⟨A, x, hx⟩ := Concrete.isColimit_exists_rep _ hc y
  exact ⟨A.unop, x, hx⟩

variable {hu 𝒜 hobj hhom hhom_inj hK} in
/-- If `stdCocone` is a colimit, a class at a level whose leg vanishes vanishes along some
transition. -/
theorem exists_transition_eq_zero {n : ℕ} {F : AbelianSheafSystem.{v, u, max u v w, max u v w} D}
    (hc : IsColimit (stdCocone hu hobj hhom hhom_inj hK 𝒜 n F)) {A : Over i}
    (x : Ext.{max u v w} (𝒜.obj A) (F.obj A.left) n)
    (hx : extLeg 𝒜 F (kanLegs hu hobj hhom hhom_inj hK F) n A x = 0) :
    ∃ (E : (Over i)ᵒᵖ) (f : op A ⟶ E), extTransition 𝒜 F n f.unop x = 0 := by
  have : PreservesFilteredColimitsOfSize.{v, max u v} (forget Ab.{max u v w}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max u v w, max u v w} _
  obtain ⟨E, f, g, h⟩ := Concrete.isColimit_exists_of_rep_eq _ (i := op A) (j := op A) hc x 0
    (by
      show extLeg 𝒜 F _ n A x = extLeg 𝒜 F _ n A 0
      rw [hx, map_zero])
  refine ⟨E, f, ?_⟩
  change extTransition 𝒜 F n f.unop x = extTransition 𝒜 F n g.unop 0 at h
  rw [h, map_zero]

variable {hu 𝒜 hobj hhom hhom_inj hK} in
/-- If `stdCocone` is a colimit, a class at an object of `(Over i)ᵒᵖ` whose leg vanishes vanishes
along some map of `(Over i)ᵒᵖ`. -/
theorem exists_map_eq_zero {n : ℕ} {F : AbelianSheafSystem.{v, u, max u v w, max u v w} D}
    (hc : IsColimit (stdCocone hu hobj hhom hhom_inj hK 𝒜 n F)) {A : (Over i)ᵒᵖ}
    (x : Ext.{max u v w} (𝒜.obj A.unop) (F.obj A.unop.left) n)
    (hx : extLeg 𝒜 F (kanLegs hu hobj hhom hhom_inj hK F) n A.unop x = 0) :
    ∃ (E : (Over i)ᵒᵖ) (f : A ⟶ E), extTransition 𝒜 F n f.unop x = 0 :=
  exists_transition_eq_zero hc (A := A.unop) x hx

variable {hu 𝒜 hobj hhom hhom_inj hK} in
/-- If `stdCocone` is a colimit, two classes at a level with equal legs agree along some
transition. -/
theorem exists_map_eq {n : ℕ} {F : AbelianSheafSystem.{v, u, max u v w, max u v w} D}
    (hc : IsColimit (stdCocone hu hobj hhom hhom_inj hK 𝒜 n F)) {A : Over i}
    (x y : Ext.{max u v w} (𝒜.obj A) (F.obj A.left) n)
    (hxy : extLeg 𝒜 F (kanLegs hu hobj hhom hhom_inj hK F) n A x =
      extLeg 𝒜 F (kanLegs hu hobj hhom hhom_inj hK F) n A y) :
    ∃ (E : (Over i)ᵒᵖ) (f : op A ⟶ E),
      extTransition 𝒜 F n f.unop x = extTransition 𝒜 F n f.unop y := by
  have hx : extLeg 𝒜 F (kanLegs hu hobj hhom hhom_inj hK F) n A (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨E, f, hf⟩ := exists_transition_eq_zero hc (x - y) hx
  exact ⟨E, f, sub_eq_zero.mp ((map_sub _ x y).symm.trans hf)⟩

variable {hu 𝒜 hobj hhom hhom_inj hK} in
/-- **The induction step of dimension shifting**, for a short exact sequence `F ⟶ I ⟶ Q` of
systems with `I` pointwise injective and a compatible short exact sequence of colimit sheaves
whose middle term has no `Ext` from `𝒜_∞` in degree `n + 1`. -/
theorem nonempty_isColimit_succ_of_shortExact (n : ℕ)
    {F I Q : AbelianSheafSystem.{v, u, max u v w, max u v w} D}
    (ιF : AbelianSheafSystem.Hom F I) (π : AbelianSheafSystem.Hom I Q)
    (w : ∀ j, ιF.app j ≫ π.app j = 0)
    (hS : ∀ j, (ShortComplex.mk (ιF.app j) (π.app j) (w j)).ShortExact)
    (hinjI : ∀ j, Injective (I.obj j))
    (ψ : systemColimitSheaf D uC hu hobj hhom hhom_inj K hK F ⟶
      systemColimitSheaf D uC hu hobj hhom hhom_inj K hK I)
    (ϖ : systemColimitSheaf D uC hu hobj hhom hhom_inj K hK I ⟶
      systemColimitSheaf D uC hu hobj hhom hhom_inj K hK Q)
    (w' : ψ ≫ ϖ = 0) (hS' : (ShortComplex.mk ψ ϖ w').ShortExact)
    (hψ : ∀ j, systemLeg (kanLegs hu hobj hhom hhom_inj hK F) j ≫ ψ =
      (colimitPullback.{v, u, w} D uC K j).map (ιF.app j) ≫
        systemLeg (kanLegs hu hobj hhom hhom_inj hK I) j)
    (hϖ : ∀ j, systemLeg (kanLegs hu hobj hhom hhom_inj hK I) j ≫ ϖ =
      (colimitPullback.{v, u, w} D uC K j).map (π.app j) ≫
        systemLeg (kanLegs hu hobj hhom hhom_inj hK Q) j)
    (hcI : IsColimit (stdCocone hu hobj hhom hhom_inj hK 𝒜 n I))
    (hcQ : IsColimit (stdCocone hu hobj hhom hhom_inj hK 𝒜 n Q))
    (hvan : ∀ y : Ext.{max u v w} 𝒜.top (systemColimitSheaf D uC hu hobj hhom hhom_inj K hK I)
      (n + 1), y = 0) :
    Nonempty (IsColimit (stdCocone hu hobj hhom hhom_inj hK 𝒜 (n + 1) F)) := by
  have : PreservesFilteredColimitsOfSize.{v, max u v} (forget Ab.{max u v w}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max u v w, max u v w} _
  refine ⟨isColimitOfElementwise _ (fun y => ?_) (fun A x hx => ?_)⟩
  · obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₁ 𝒜.top hS' y (hvan _) rfl
    obtain ⟨A, zA, rfl⟩ := exists_leg_eq hcQ z
    refine ⟨op A, zA.comp (hS A.left).extClass rfl, ?_⟩
    show extLeg 𝒜 F _ (n + 1) A _ = y
    rw [extLeg_delta n ιF π w hS ψ ϖ w' hS' hψ hϖ A zA, hz]
  · change extLeg 𝒜 F _ (n + 1) A.unop x = 0 at hx
    have := hinjI A.unop.left
    obtain ⟨zA, rfl⟩ := Ext.covariant_sequence_exact₁ _ (hS A.unop.left) x
      (Ext.eq_zero_of_injective _) rfl
    rw [extLeg_delta n ιF π w hS ψ ϖ w' hS' hψ hϖ A.unop zA] at hx
    obtain ⟨wI, hwI⟩ := Ext.covariant_sequence_exact₃ 𝒜.top hS' _ rfl hx
    obtain ⟨B, wB, rfl⟩ := exists_leg_eq hcI wI
    obtain ⟨E, fA, fB, -⟩ : ∃ (E : Over i) (_ : E ⟶ A.unop) (_ : E ⟶ B), True :=
      ⟨_, IsCofiltered.minToLeft A.unop B, IsCofiltered.minToRight A.unop B, trivial⟩
    have h1 := extLeg_transition 𝒜 (kanLegs hu hobj hhom hhom_inj hK Q) n
      (kanLegs_compatible hu hobj hhom hhom_inj hK Q) fA zA
    have h2 := extLeg_transition 𝒜 (kanLegs hu hobj hhom hhom_inj hK I) n
      (kanLegs_compatible hu hobj hhom hhom_inj hK I) fB wB
    have h3 := extLeg_postcomp (𝒜 := 𝒜) n π ϖ hϖ E (extTransition 𝒜 I n fB wB)
    have hd : extLeg 𝒜 Q (kanLegs hu hobj hhom hhom_inj hK Q) n E
        (extTransition 𝒜 Q n fA zA) = extLeg 𝒜 Q (kanLegs hu hobj hhom hhom_inj hK Q) n E
          (extConj (𝟙 _) (π.app E.left) (extTransition 𝒜 I n fB wB)) := by
      rw [h3, h1, h2, extConj_id_left, hwI]
    obtain ⟨E', g, hg⟩ := exists_map_eq (A := E) hcQ _ _ hd
    exact ⟨E', fA.op ≫ g, extTransition_extClass_eq_zero n ιF π w hS g.unop fA fB zA wB hg⟩

variable [∀ j, (uC j).IsContinuous (D.J j) K.toGrothendieck] in
/-- **Dimension shifting for the `Ext` colimit.** If the `Ext` cocone in degree zero is a colimit
for every system, and `Ext` out of `𝒜_∞` into the colimit sheaf of a pointwise injective system
vanishes in positive degrees, then the `Ext` cocone is a colimit in every degree, for every
system. -/
theorem nonempty_isColimit_stdCocone
    (H0 : ∀ F, Nonempty (IsColimit (stdCocone hu hobj hhom hhom_inj hK 𝒜 0 F)))
    (Hinj : ∀ F : AbelianSheafSystem.{v, u, max u v w, max u v w} D, (∀ j, Injective (F.obj j)) →
      ∀ (n : ℕ) (y : Ext.{max u v w} 𝒜.top
        (systemColimitSheaf D uC hu hobj hhom hhom_inj K hK F) (n + 1)), y = 0) :
    ∀ (n : ℕ) (F : AbelianSheafSystem.{v, u, max u v w, max u v w} D),
      Nonempty (IsColimit (stdCocone hu hobj hhom hhom_inj hK 𝒜 n F)) := by
  intro n
  induction n with
  | zero => exact H0
  | succ n ih =>
    intro F
    obtain ⟨I, Q, ιF, π, w, hS, hinjI, ψ, ϖ, w', hS', hψ, hϖ⟩ :=
      exists_shortExact_pointwiseInjective_colimit D uC hu hobj hhom hhom_inj K hK F
    obtain ⟨hcI⟩ := ih I
    obtain ⟨hcQ⟩ := ih Q
    exact nonempty_isColimit_succ_of_shortExact n ιF π w hS hinjI ψ ϖ w' hS'
      (systemLeg_comp_of_fac hu hobj hhom hhom_inj hK ιF ψ hψ)
      (systemLeg_comp_of_fac hu hobj hhom hhom_inj hK π ϖ hϖ) hcI hcQ (Hinj I hinjI n)

end DimensionShifting

section PullbackFirstVariable

omit [∀ i, (uC i).IsContinuous (D.J i) K.toGrothendieck] in
private theorem eqToHom_three {𝒞 : Type*} [Category 𝒞] {X Y Z W : 𝒞} (h₁ : X = Y) (h₂ : Y = Z)
    (h₃ : Z = W) (h : X = W) : eqToHom h = eqToHom h₁ ≫ eqToHom h₂ ≫ eqToHom h₃ := by
  subst h₁ h₂ h₃
  simp

variable {i : D.I} (P : Sheaf (D.J i) Ab.{max u v w})

variable (D) in
/-- The comparison `f_{*} ⋙ (B.hom)_{*} ≅ (A.hom)_{*}` along an arrow `f : A ⟶ B` of `Over i`. -/
def overPushforwardIso {A B : Over i} (f : A ⟶ B) :
    abelianSheafPushforward.{v, u, max u v w, max u v w} D f.left ⋙
        abelianSheafPushforward.{v, u, max u v w, max u v w} D B.hom ≅
      abelianSheafPushforward.{v, u, max u v w, max u v w} D A.hom :=
  abelianSheafPushforwardCompIso.{v, u, max u v w, max u v w} D f.left B.hom ≪≫
    eqToIso (congrArg (abelianSheafPushforward.{v, u, max u v w, max u v w} D) (Over.w f))

omit [∀ i, (uC i).IsContinuous (D.J i) K.toGrothendieck]
  [∀ j, EnoughInjectives (Sheaf (D.J j) Ab.{max u v w})]
  [∀ j, HasExt.{max u v w} (Sheaf (D.J j) Ab.{max u v w})] in
/-- The components of the inverse of `overPushforwardIso D f` are restriction maps along equalities
of objects. -/
theorem overPushforwardIso_inv_app_app {A B : Over i} (f : A ⟶ B)
    (Z : Sheaf (D.J A.left) Ab.{max u v w}) (V : (D.C i)ᵒᵖ) :
    ((overPushforwardIso D f).inv.app Z).hom.app V =
      Z.obj.map (eqToHom (by rw [← Over.w f, D.comp]; rfl)) := by
  let := D.continuous f.left
  let := D.continuous B.hom
  let := D.continuous (f.left ≫ B.hom)
  rw [overPushforwardIso, Iso.trans_inv, NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app, eqToIso.inv, eqToHom_app, sheafEqToHom_hom_app,
    abelianSheafPushforwardCompIso_inv_app_hom_app, eqToHom_map, eqToHom_map]
  exact eqToHom_trans _ _

variable (D) in
/-- The arrows of `Over i` with the direct images along their left components, as a cocone of
direct images on the sheaves of the level `i`. -/
def overTransition {A B : Over i} (f : A ⟶ B) :
    (pb.{v, u, w} D B.hom).obj P ⟶
      (abelianSheafPushforward.{v, u, max u v w, max u v w} D f.left).obj
        ((pb.{v, u, w} D A.hom).obj P) :=
  CategoryTheory.PushforwardCocone.transitionPushforward
    (P := fun {A B : Over i} (f : A ⟶ B) =>
      abelianSheafPushforward.{v, u, max u v w, max u v w} D f.left)
    (fun A => abelianSheafAdjunction.{v, u, max u v w, max u v w} D A.hom)
    (fun f => overPushforwardIso D f) P f

omit [∀ i, (uC i).IsContinuous (D.J i) K.toGrothendieck]
  [∀ j, EnoughInjectives (Sheaf (D.J j) Ab.{max u v w})]
  [∀ j, HasExt.{max u v w} (Sheaf (D.J j) Ab.{max u v w})] in
/-- The transition `overTransition` along an identity is the identity comparison of direct
images. -/
theorem overTransition_id (A : Over i) :
    overTransition D P (𝟙 A) =
      (abelianSheafPushforwardIdIso.{v, u, max u v w, max u v w} D A.left).hom.app
        ((pb.{v, u, w} D A.hom).obj P) := by
  refine CategoryTheory.PushforwardCocone.transitionPushforward_id
    (P := fun {A B : Over i} (f : A ⟶ B) =>
      abelianSheafPushforward.{v, u, max u v w, max u v w} D f.left)
    (fun A => abelianSheafAdjunction.{v, u, max u v w, max u v w} D A.hom)
    (fun A => abelianSheafPushforwardIdIso.{v, u, max u v w, max u v w} D A.left)
    (fun f => overPushforwardIso D f) (fun A Z => ?_) P A
  apply Sheaf.hom_ext
  ext V : 2
  rw [overPushforwardIso_inv_app_app]
  let := D.continuous A.hom
  show _ = ((abelianSheafPushforwardIdIso.{v, u, max u v w, max u v w} D A.left).hom.app
    Z).hom.app _
  rw [abelianSheafPushforwardIdIso_hom_app_hom_app, eqToHom_map]

omit [∀ i, (uC i).IsContinuous (D.J i) K.toGrothendieck]
  [∀ j, EnoughInjectives (Sheaf (D.J j) Ab.{max u v w})]
  [∀ j, HasExt.{max u v w} (Sheaf (D.J j) Ab.{max u v w})] in
/-- The transition `overTransition` along a composite is the composite of the transitions. -/
theorem overTransition_comp {A B E : Over i} (f : A ⟶ B) (g : B ⟶ E) :
    overTransition D P (f ≫ g) =
      overTransition D P g ≫
        (abelianSheafPushforward.{v, u, max u v w, max u v w} D g.left).map
          (overTransition D P f) ≫
        (abelianSheafPushforwardCompIso.{v, u, max u v w, max u v w} D f.left g.left).hom.app
          ((pb.{v, u, w} D A.hom).obj P) := by
  refine CategoryTheory.PushforwardCocone.transitionPushforward_comp
    (P := fun {A B : Over i} (f : A ⟶ B) =>
      abelianSheafPushforward.{v, u, max u v w, max u v w} D f.left)
    (fun A => abelianSheafAdjunction.{v, u, max u v w, max u v w} D A.hom)
    (fun f g => abelianSheafPushforwardCompIso.{v, u, max u v w, max u v w} D f.left g.left)
    (fun f => overPushforwardIso D f) (fun f g Z => ?_) P f g
  apply Sheaf.hom_ext
  ext V : 2
  let := D.continuous E.hom
  let := D.continuous g.left
  let := D.continuous f.left
  let := D.continuous (f.left ≫ g.left)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  rw [overPushforwardIso_inv_app_app, overPushforwardIso_inv_app_app,
    overPushforwardIso_inv_app_app, abelianSheafPushforward_map_hom, Functor.whiskerLeft_app,
    abelianSheafPushforwardCompIso_hom_app_hom_app]
  simp only [eqToHom_map]
  exact eqToHom_three _ _ _ _

variable (D uC hu K) in
/-- The leg `(A.hom)⁻¹ P ⟶ u_{A,*} u_i⁻¹ P` of the pullback first variable, in direct-image
form: the transpose of the unit of `u_i⁻¹ ⊣ u_{i,*}` read through
`u_{A,*} ⋙ (A.hom)_* ≅ u_{i,*}`. -/
def overLeg (A : Over i) :
    (pb.{v, u, w} D A.hom).obj P ⟶
      (colimitPushforward.{v, u, w} D uC K A.left).obj
        ((colimitPullback.{v, u, w} D uC K i).obj P) :=
  ((abelianSheafAdjunction.{v, u, max u v w, max u v w} D A.hom).homEquiv _ _).symm
    ((colimitAdj.{v, u, w} D uC K i).unit.app P ≫
      (colimitPushforwardCompIso.{v, u, w} D uC hu K A.hom).inv.app _)

omit [∀ j, PreservesFiniteLimits (colimitPullback.{v, u, w} D uC K j)]
  [∀ j, EnoughInjectives (Sheaf (D.J j) Ab.{max u v w})]
  [∀ j, HasExt.{max u v w} (Sheaf (D.J j) Ab.{max u v w})]
  [HasExt.{max u v w} (Sheaf K.toGrothendieck Ab.{max u v w})] in
/-- The legs `overLeg` are compatible with the transitions `overTransition`. -/
theorem overLeg_comp {A B : Over i} (f : A ⟶ B) :
    overLeg D uC hu K P B = overTransition D P f ≫
      (abelianSheafPushforward.{v, u, max u v w, max u v w} D f.left).map (overLeg D uC hu K P A) ≫
      (colimitPushforwardCompIso.{v, u, w} D uC hu K f.left).hom.app _ := by
  have hunit : (abelianSheafAdjunction.{v, u, max u v w, max u v w} D A.hom).homEquiv _ _
      (overLeg D uC hu K P A) = (colimitAdj.{v, u, w} D uC K i).unit.app P ≫
        (colimitPushforwardCompIso.{v, u, w} D uC hu K A.hom).inv.app _ :=
    Equiv.apply_symm_apply _ _
  have htr : (abelianSheafAdjunction.{v, u, max u v w, max u v w} D B.hom).homEquiv _ _
      (overTransition D P f) =
        (abelianSheafAdjunction.{v, u, max u v w, max u v w} D A.hom).unit.app P ≫
          (overPushforwardIso D f).inv.app _ :=
    CategoryTheory.PushforwardCocone.homEquiv_transitionPushforward
      (P := fun {A B : Over i} (f : A ⟶ B) =>
        abelianSheafPushforward.{v, u, max u v w, max u v w} D f.left)
      (fun A => abelianSheafAdjunction.{v, u, max u v w, max u v w} D A.hom)
      (fun f => overPushforwardIso D f) P f
  rw [Adjunction.homEquiv_unit] at hunit
  refine ((abelianSheafAdjunction.{v, u, max u v w, max u v w} D B.hom).homEquiv _ _).injective ?_
  have hn := (overPushforwardIso D f).inv.naturality (overLeg D uC hu K P A)
  dsimp only [Functor.comp_map] at hn
  rw [overLeg, Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_right, htr,
    Functor.map_comp, Category.assoc, ← reassoc_of% hn, ← Category.assoc, hunit,
    Category.assoc]
  congr 1
  apply Sheaf.hom_ext
  ext V : 2
  let := D.continuous A.hom
  let := D.continuous B.hom
  let := D.continuous f.left
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  rw [overPushforwardIso_inv_app_app, abelianSheafPushforward_map_hom, Functor.whiskerLeft_app]
  dsimp only [colimitPushforwardCompIso]
  rw [sheafPushforwardContinuousComp'_inv_app_app, sheafPushforwardContinuousComp'_inv_app_app,
    sheafPushforwardContinuousComp'_hom_app_app]
  simp only [eqToHom_map]
  exact eqToHom_three _ _ _ _

variable (D uC hu K) in
/-- **The pullback first variable** of an abelian sheaf `P` on the level `i`: the sheaves
`(A.hom)⁻¹ P` on the levels below `i`, with the comparisons of inverse images as transitions, and
`u_i⁻¹ P` on the colimit site. -/
def pullbackFirstVariable : FirstVariable.{v, u, w} D uC hu K i where
  obj A := (pb.{v, u, w} D A.hom).obj P
  φ f := overTransition D P f
  φ_id A := overTransition_id P A
  φ_comp f g := overTransition_comp P f g
  isIso_φ f := isIso_transpose_transition
    (abelianSheafAdjunction.{v, u, max u v w, max u v w} D _)
    (abelianSheafAdjunction.{v, u, max u v w, max u v w} D _)
    (abelianSheafAdjunction.{v, u, max u v w, max u v w} D f.left) (overPushforwardIso D f) P
  top := (colimitPullback.{v, u, w} D uC K i).obj P
  lg A := overLeg D uC hu K P A
  lg_comp f := overLeg_comp P f
  isIso_lg A := isIso_transpose_transition
    (abelianSheafAdjunction.{v, u, max u v w, max u v w} D A.hom) (colimitAdj.{v, u, w} D uC K i)
    (colimitAdj.{v, u, w} D uC K A.left) (colimitPushforwardCompIso.{v, u, w} D uC hu K A.hom) P

end PullbackFirstVariable

end ColimitSite

end Stacks.WeakSites.ExtColimit

end
