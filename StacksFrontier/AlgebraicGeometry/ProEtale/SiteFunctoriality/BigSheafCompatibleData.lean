module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.Limits
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.SmallBaseChange
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.SmallToBigTopos
public import StacksCore.Tactic.StacksAttribute

/-!
# Sheaves on the big pro-étale site as compatible small-site data

Let `S` be a scheme contained in a chosen big pro-étale site. A sheaf on the big pro-étale
site over `S` is the same thing as a family of sheaves `F T` on the small pro-étale site of
each `T / S`, together with transition maps `f⁻¹ (F T) ⟶ F T'` for every `f : T' ⟶ T` which
compose correctly and which are isomorphisms whenever `f` is weakly étale.

## Main definitions

* `AlgebraicGeometry.ProEtale.smallProetaleInverseImage`,
  `AlgebraicGeometry.ProEtale.smallProetalePushforward` and
  `AlgebraicGeometry.ProEtale.smallProetalePullbackAdjunction` are inverse image, direct
  image and their adjunction between small pro-étale sheaf categories, induced by small-site
  base change.
* `AlgebraicGeometry.ProEtale.smallProetaleBaseChange_compIso` and
  `AlgebraicGeometry.ProEtale.smallProetaleInverseImageCompIso` are the canonical
  comparisons of successive base changes and of successive inverse images.
* `AlgebraicGeometry.ProEtale.BigProetaleSheafData` is the category of compatible families of
  small pro-étale sheaves over `S`, with
  `AlgebraicGeometry.ProEtale.BigProetaleSheafData.eval` the evaluation at an object over `S`.
* `AlgebraicGeometry.ProEtale.smallRestriction` restricts a sheaf on the big pro-étale site
  over `S` to the small pro-étale site of an object over `S`.
* `AlgebraicGeometry.ProEtale.smallProetaleBaseChangeProjection` is the projection from a
  small-site base change, viewed as a morphism over `S`.

## Main results

* `AlgebraicGeometry.ProEtale.characterizeSheafBigProetale` identifies sheaves on the big
  pro-étale site over `S` with compatible families of small pro-étale sheaves, naturally on
  each small site and compatibly with the transition maps.

## Implementation notes

Condition (a) of the source is expressed with the canonical comparison
`smallProetaleInverseImageCompIso` of successive inverse images, obtained from the
corresponding comparison of direct images by conjugating the adjunctions. The equivalence is
built by restricting a big sheaf to each small site; its inverse evaluates a compatible family
at the identity object of each small site and checks the sheaf condition by comparing with the
given small-site sheaves. The resulting identification carries the transition map of a
restricted sheaf to restriction along the projection from the fibre product, which is the last
clause of `characterizeSheafBigProetale`.

The direct image here is the one induced by `smallProetaleBaseChange` on sheaves of types in
`Type (max (u + 1) v)`; at `v = u + 1` it is the direct image of the geometric morphism
`AlgebraicGeometry.ProEtale.smallProetaleMorphism`, and the extra universe parameter is kept
because the big-site sheaves of interest live in that larger universe.

## References

* [Stacks Project, Tag 098V](https://stacks.math.columbia.edu/tag/098V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.ProEtale

variable (B : BigProetaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Inverse image `f_small⁻¹` of small pro-étale sheaves along `f`, the left adjoint of the
direct image induced by small-site base change. -/
public abbrev smallProetaleInverseImage {T T' : B.Scheme} (f : T' ⟶ T) :=
  (smallProetaleBaseChange B T' T f).sheafPullback
    (Type (max (u + 1) v))
    (SmallProetale.topology B T.obj T.property)
    (SmallProetale.topology B T'.obj T'.property)

/-- Direct image `f_{small, *}` of small pro-étale sheaves along `f`, obtained from small-site
base change. -/
public abbrev smallProetalePushforward {T T' : B.Scheme} (f : T' ⟶ T) :=
  (smallProetaleBaseChange B T' T f).sheafPushforwardContinuous
    (Type (max (u + 1) v))
    (SmallProetale.topology B T.obj T.property)
    (SmallProetale.topology B T'.obj T'.property)

/-- Inverse image is left adjoint to direct image on small pro-étale sheaves. -/
public def smallProetalePullbackAdjunction {T T' : B.Scheme} (f : T' ⟶ T) :
    smallProetaleInverseImage.{u, v} B f ⊣ smallProetalePushforward.{u, v} B f :=
  (smallProetaleBaseChange B T' T f).sheafAdjunctionContinuous
    (Type (max (u + 1) v))
    (SmallProetale.topology B T.obj T.property)
    (SmallProetale.topology B T'.obj T'.property)

/-- Base change along `f` followed by base change along `g` is canonically base change along
`g ≫ f`. -/
public def smallProetaleBaseChange_compIso {T T' T'' : B.Scheme}
    (f : T' ⟶ T) (g : T'' ⟶ T') :
    smallProetaleBaseChange B T' T f ⋙
      smallProetaleBaseChange B T'' T' g ≅
      smallProetaleBaseChange B T'' T (g ≫ f) := by
  refine NatIso.ofComponents
    (fun U => (IsWeaklyEtaleOver B T''.obj T''.property).isoMk
      ((Over.pullbackComp g f).symm.app U.obj)) ?_
  intro X Y h
  apply (SmallProetale.inclusion B T''.obj T''.property).map_injective
  exact (Over.pullbackComp g f).symm.hom.naturality h.hom

/-- The canonical comparison `f_small⁻¹ ∘ g_small⁻¹ ≅ (g ≫ f)_small⁻¹` of successive inverse
images, conjugate to the comparison of successive direct images. -/
public def smallProetaleInverseImageCompIso {T T' T'' : B.Scheme}
    (f : T' ⟶ T) (g : T'' ⟶ T') :
    smallProetaleInverseImage.{u, v} B f ⋙ smallProetaleInverseImage.{u, v} B g ≅
      smallProetaleInverseImage.{u, v} B (g ≫ f) :=
  Adjunction.leftAdjointCompIso
    (smallProetalePullbackAdjunction B f) (smallProetalePullbackAdjunction B g)
    (smallProetalePullbackAdjunction B (g ≫ f))
    (Functor.sheafPushforwardContinuousComp'
      (smallProetaleBaseChange_compIso B f g)
      (Type (max (u + 1) v))
      (SmallProetale.topology B T.obj T.property)
      (SmallProetale.topology B T'.obj T'.property)
      (SmallProetale.topology B T''.obj T''.property))

/-- The data of a sheaf on the big pro-étale site over `S`, presented on the small sites: a
sheaf on the small pro-étale site of every `T / S`, transition maps between their inverse
images, subject to the cocycle condition and to invertibility along weakly étale maps.
See [Stacks Project, Tag 098V](https://stacks.math.columbia.edu/tag/098V). -/
@[stacks 098V "the compatible data"]
public structure BigProetaleSheafData where
  /-- The sheaf on the small pro-étale site of an object over `S`. -/
  sheaf (T : BigProetaleOver B S hS) :
    Sheaf (SmallProetale.topology B T.left.obj T.left.property)
      (Type (max (u + 1) v))
  /-- The transition map `c_f` attached to a morphism `f` over `S`. -/
  pullback {T T' : BigProetaleOver B S hS} (f : T' ⟶ T) :
    (smallProetaleInverseImage.{u, v} B f.left).obj (sheaf T) ⟶ sheaf T'
  /-- The transition maps compose, up to the canonical comparison of successive inverse
  images. -/
  pullback_comp {T T' T'' : BigProetaleOver B S hS}
      (f : T' ⟶ T) (g : T'' ⟶ T') :
    (smallProetaleInverseImage.{u, v} B g.left).map (pullback f) ≫ pullback g =
      (smallProetaleInverseImageCompIso B f.left g.left).hom.app (sheaf T) ≫
        pullback (g ≫ f)
  /-- The transition map along a weakly étale morphism is an isomorphism. -/
  isIso_pullback {T T' : BigProetaleOver B S hS} (f : T' ⟶ T)
      [WeaklyEtale (B.inclusion.map f.left)] : IsIso (pullback f)

/-- A morphism of compatible families of small pro-étale sheaves: a morphism on each small
site, commuting with the transition maps. -/
public structure BigProetaleSheafData.Hom
    (D E : BigProetaleSheafData.{u, v} B S hS) where
  /-- The component on the small pro-étale site of an object over `S`. -/
  app (T : BigProetaleOver B S hS) : D.sheaf T ⟶ E.sheaf T
  /-- The components commute with the transition maps. -/
  naturality {T T' : BigProetaleOver B S hS} (f : T' ⟶ T) :
    (smallProetaleInverseImage.{u, v} B f.left).map (app T) ≫ E.pullback f =
      D.pullback f ≫ app T'

/-- Two morphisms of compatible families agree as soon as all their components do. -/
@[ext] public theorem BigProetaleSheafData.Hom.ext
    {D E : BigProetaleSheafData.{u, v} B S hS}
    {φ ψ : BigProetaleSheafData.Hom B S hS D E}
    (h : ∀ T, φ.app T = ψ.app T) : φ = ψ := by
  cases φ with
  | mk φ _ =>
    cases ψ with
    | mk ψ _ =>
      congr 1
      funext T
      exact h T

/-- Compatible families of small pro-étale sheaves over `S` form a category. -/
public instance : Category (BigProetaleSheafData.{u, v} B S hS) where
  Hom := BigProetaleSheafData.Hom B S hS
  id D := ⟨fun T => 𝟙 _, by intro T T' f; simp⟩
  comp φ ψ := ⟨fun T => φ.app T ≫ ψ.app T, by
    intro T T' f
    simp only [Functor.map_comp]
    rw [Category.assoc, ψ.naturality f, ← Category.assoc, φ.naturality f,
      Category.assoc]⟩
  id_comp := by
    intro X Y f
    apply BigProetaleSheafData.Hom.ext
    intro T
    simp
  comp_id := by
    intro X Y f
    apply BigProetaleSheafData.Hom.ext
    intro T
    simp
  assoc := by
    intro W X Y Z f g h
    apply BigProetaleSheafData.Hom.ext
    intro T
    simp only [Category.assoc]

/-- Evaluation of a compatible family at a fixed object over `S`, as a functor to sheaves on
its small pro-étale site. -/
public def BigProetaleSheafData.eval (T : BigProetaleOver B S hS) :
    BigProetaleSheafData.{u, v} B S hS ⥤
      Sheaf (SmallProetale.topology B T.left.obj T.left.property)
        (Type (max (u + 1) v)) where
  obj D := D.sheaf T
  map φ := φ.app T

/-- Restriction of a sheaf on the big pro-étale site over `S` to the small pro-étale site of
an object `T` over `S`; it is the direct image along composition with the structure morphism
of `T`. -/
public def smallRestriction (T : BigProetaleOver B S hS) :
    Sheaf (BigProetaleOver.topology B S hS) (Type (max (u + 1) v)) ⥤
      Sheaf (SmallProetale.topology B T.left.obj T.left.property)
        (Type (max (u + 1) v)) := by
  letI := smallProetaleToBigProetaleFunctor_isContinuous B
    T.left (⟨S, hS⟩ : B.Scheme) T.hom
  exact Functor.sheafPushforwardContinuous
    (smallProetaleToBigProetaleFunctor B
      T.left (⟨S, hS⟩ : B.Scheme) T.hom)
    (Type (max (u + 1) v))
    (SmallProetale.topology B T.left.obj T.left.property)
    (BigProetaleOver.topology B S hS)

/-- The projection `U ×_T T' ⟶ U` out of a small-site base change, read as a morphism of the
big pro-étale site over `S`. -/
public def smallProetaleBaseChangeProjection {T T' : BigProetaleOver B S hS} (f : T' ⟶ T)
    (U : SmallProetale B T.left.obj T.left.property) :
    (smallProetaleToBigProetaleFunctor B T'.left
      (⟨S, hS⟩ : B.Scheme) T'.hom).obj
        ((smallProetaleBaseChange B T'.left T.left f.left).obj U) ⟶
      (smallProetaleToBigProetaleFunctor B T.left
        (⟨S, hS⟩ : B.Scheme) T.hom).obj U :=
  Over.homMk (pullback.fst U.obj.hom f.left) (by
    change pullback.fst U.obj.hom f.left ≫ (U.obj.hom ≫ T.hom) =
      pullback.snd U.obj.hom f.left ≫ T'.hom
    rw [← Category.assoc, pullback.condition, Category.assoc, Over.w f])

section

-- The identity object of a small pro-étale site and the sheaf functors attached to base
-- change unfold only at default transparency, which the elaborator does not do by itself
-- inside the rewriting below.
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private abbrev smallProetaleIdentity (T : B.Scheme) :
    SmallProetale B T.obj T.property :=
  smallIdentity B T.obj T.property

private def smallProetaleLift {T T' : B.Scheme} (f : T' ⟶ T)
    (U : SmallProetale B T.obj T.property) (V : SmallProetale B T'.obj T'.property)
    (k : V.obj.left ⟶ U.obj.left) (hk : k ≫ U.obj.hom = V.obj.hom ≫ f) :
    V ⟶ (smallProetaleBaseChange B T' T f).obj U :=
  ⟨Over.homMk (pullback.lift k V.obj.hom hk) (by
    change pullback.lift k V.obj.hom hk ≫ pullback.snd U.obj.hom f = _
    simp)⟩

private theorem smallProetaleLift_comp
    {T T' T'' : B.Scheme} (f : T' ⟶ T) (g : T'' ⟶ T')
    (U : SmallProetale B T.obj T.property) (V : SmallProetale B T'.obj T'.property)
    (W : SmallProetale B T''.obj T''.property)
    (k : V.obj.left ⟶ U.obj.left) (hk : k ≫ U.obj.hom = V.obj.hom ≫ f)
    (l : W.obj.left ⟶ V.obj.left) (hl : l ≫ V.obj.hom = W.obj.hom ≫ g) :
    smallProetaleLift B (g ≫ f) U W (l ≫ k)
        (by rw [Category.assoc, hk, ← Category.assoc, hl, Category.assoc]) ≫
      (smallProetaleBaseChange_compIso B f g).inv.app U =
    smallProetaleLift B g V W l hl ≫
      (smallProetaleBaseChange B T'' T' g).map
        (smallProetaleLift B f U V k hk) := by
  apply (SmallProetale.inclusion B T''.obj T''.property).map_injective
  apply (Over.forget _).map_injective
  apply pullback.hom_ext
  · apply pullback.hom_ext <;>
      simp [smallProetaleLift, smallProetaleBaseChange_compIso,
        smallProetaleBaseChange, Over.pullbackComp,
        conjugateIsoEquiv, conjugateEquiv, Over.mapPullbackAdj, Over.mapComp,
        Over.pullback, Category.assoc, hl]
  · simp [smallProetaleLift, smallProetaleBaseChange_compIso,
      smallProetaleBaseChange, Over.pullbackComp,
      conjugateIsoEquiv, conjugateEquiv, Over.mapPullbackAdj, Over.mapComp,
      Over.pullback, Category.assoc]

private noncomputable def smallProetaleBaseChangeIdentityIso
    {T T' : B.Scheme} (f : T' ⟶ T) :
    (smallProetaleBaseChange B T' T f).obj
      (smallProetaleIdentity B T) ≅ smallProetaleIdentity B T' := by
  apply ObjectProperty.isoMk
  change Over.mk (pullback.snd (𝟙 T) f) ≅ Over.mk (𝟙 T')
  refine Over.isoMk
    { hom := pullback.snd (𝟙 T) f
      inv := pullback.lift f (𝟙 T') (by simp)
      hom_inv_id := by
        apply pullback.hom_ext
        · simpa using (pullback.condition (f := 𝟙 T) (g := f)).symm
        · simp
      inv_hom_id := by simp } ?_
  simp

private noncomputable def systemPullbackAdjoint
    (D : BigProetaleSheafData.{u, v} B S hS)
    {T T' : BigProetaleOver B S hS} (f : T' ⟶ T) :
    D.sheaf T ⟶ (smallProetalePushforward.{u, v} B f.left).obj (D.sheaf T') :=
  (smallProetalePullbackAdjunction B f.left).homEquiv _ _ (D.pullback f)

private theorem systemPullbackAdjoint_naturality
    {D E : BigProetaleSheafData.{u, v} B S hS}
    (φ : BigProetaleSheafData.Hom B S hS D E)
    {T T' : BigProetaleOver B S hS} (f : T' ⟶ T) :
    φ.app T ≫ systemPullbackAdjoint B S hS E f =
      systemPullbackAdjoint B S hS D f ≫
        (smallProetalePushforward.{u, v} B f.left).map (φ.app T') := by
  let adj := smallProetalePullbackAdjunction B f.left
  show φ.app T ≫ adj.homEquiv _ _ (E.pullback f) =
    adj.homEquiv _ _ (D.pullback f) ≫ (smallProetalePushforward B f.left).map (φ.app T')
  calc
    φ.app T ≫ adj.homEquiv (E.sheaf T) (E.sheaf T') (E.pullback f) =
        adj.homEquiv (D.sheaf T) (E.sheaf T')
          ((smallProetaleInverseImage B f.left).map (φ.app T) ≫ E.pullback f) := by
      rw [adj.homEquiv_naturality_left]
    _ = adj.homEquiv (D.sheaf T) (E.sheaf T')
          (D.pullback f ≫ φ.app T') := by rw [φ.naturality f]
    _ = adj.homEquiv (D.sheaf T) (D.sheaf T') (D.pullback f) ≫
          (smallProetalePushforward B f.left).map (φ.app T') := by
      rw [adj.homEquiv_naturality_right]

/-- Naturality of the transition maps, followed by restriction along a map into a base change. -/
private theorem systemPullbackAdjoint_naturality_app
    {D E : BigProetaleSheafData.{u, v} B S hS}
    (φ : BigProetaleSheafData.Hom B S hS D E)
    {T T' : BigProetaleOver B S hS} (f : T' ⟶ T)
    {U : SmallProetale B T.left.obj T.left.property}
    {V : SmallProetale B T'.left.obj T'.left.property}
    (p : V ⟶ (smallProetaleBaseChange B T'.left T.left f.left).obj U) :
    (φ.app T).hom.app (op U) ≫
        ((systemPullbackAdjoint B S hS E f).hom.app (op U) ≫ (E.sheaf T').obj.map p.op) =
      ((systemPullbackAdjoint B S hS D f).hom.app (op U) ≫ (D.sheaf T').obj.map p.op) ≫
        (φ.app T').hom.app (op V) := by
  have hn := congrArg (fun q => q.hom.app (op U))
    (systemPullbackAdjoint_naturality B S hS φ f)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Functor.sheafPushforwardContinuous_map_hom_app] at hn
  rw [← Category.assoc, hn, Category.assoc, ← (φ.app T').hom.naturality]
  simp only [Category.assoc]

private noncomputable def smallProetalePushforwardCompIso
    {T T' T'' : B.Scheme} (f : T' ⟶ T) (g : T'' ⟶ T') :
    smallProetalePushforward.{u, v} B g ⋙ smallProetalePushforward.{u, v} B f ≅
      smallProetalePushforward.{u, v} B (g ≫ f) :=
  Functor.sheafPushforwardContinuousComp'
    (smallProetaleBaseChange_compIso B f g)
    (Type (max (u + 1) v))
    (SmallProetale.topology B T.obj T.property)
    (SmallProetale.topology B T'.obj T'.property)
    (SmallProetale.topology B T''.obj T''.property)

private theorem homEquiv_comp_map
    {C₀ : Type*} {C₁ : Type*} {C₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    {L₁ : C₀ ⥤ C₁} {R₁ : C₁ ⥤ C₀}
    {L₂ : C₁ ⥤ C₂} {R₂ : C₂ ⥤ C₁}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    {X : C₀} {Y : C₁} {Z : C₂} (c : L₁.obj X ⟶ Y) (d : L₂.obj Y ⟶ Z) :
    (a₁.comp a₂).homEquiv _ _ (L₂.map c ≫ d) =
      a₁.homEquiv _ _ c ≫ R₁.map (a₂.homEquiv _ _ d) := by
  have hn := a₂.unit.naturality c
  simp only [Functor.id_map, Functor.comp_map] at hn
  simp only [Adjunction.homEquiv_unit, Adjunction.comp_unit_app,
    Functor.comp_map, Functor.map_comp, Category.assoc]
  rw [← R₁.map_comp, ← R₁.map_comp]
  rw [← Category.assoc, ← hn]
  simp only [Functor.map_comp, Category.assoc]

private theorem systemPullbackAdjoint_comp_map
    (D : BigProetaleSheafData.{u, v} B S hS)
    {T T' T'' : BigProetaleOver B S hS}
    (f : T' ⟶ T) (g : T'' ⟶ T') :
    ((smallProetalePullbackAdjunction B f.left).comp
      (smallProetalePullbackAdjunction B g.left)).homEquiv
        (D.sheaf T) (D.sheaf T'')
        ((smallProetaleInverseImage B g.left).map (D.pullback f) ≫ D.pullback g) =
      systemPullbackAdjoint B S hS D f ≫
        (smallProetalePushforward B f.left).map (systemPullbackAdjoint B S hS D g) :=
  homEquiv_comp_map (smallProetalePullbackAdjunction B f.left)
    (smallProetalePullbackAdjunction B g.left) (D.pullback f) (D.pullback g)

private theorem homEquiv_comp_leftAdjointCompIso
    {C₀ : Type*} {C₁ : Type*} {C₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    {L₁ : C₀ ⥤ C₁} {R₁ : C₁ ⥤ C₀}
    {L₂ : C₁ ⥤ C₂} {R₂ : C₂ ⥤ C₁}
    {L₃ : C₀ ⥤ C₂} {R₃ : C₂ ⥤ C₀}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)
    (e : R₂ ⋙ R₁ ≅ R₃) {X : C₀} {Z : C₂} (c : L₃.obj X ⟶ Z) :
    (a₁.comp a₂).homEquiv _ _
        ((a₁.leftAdjointCompIso a₂ a₃ e).hom.app X ≫ c) =
      a₃.homEquiv _ _ c ≫ e.inv.app Z := by
  have hc : conjugateEquiv a₃ (a₁.comp a₂)
      (a₁.leftAdjointCompIso a₂ a₃ e).hom = e.inv := by
    simp [Adjunction.leftAdjointCompIso]
  have hu := unit_conjugateEquiv a₃ (a₁.comp a₂)
    (a₁.leftAdjointCompIso a₂ a₃ e).hom X
  rw [hc] at hu
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  rw [← hu]
  simp only [Category.assoc]
  rw [← e.inv.naturality c]

private theorem systemPullbackAdjoint_comp
    (D : BigProetaleSheafData.{u, v} B S hS)
    {T T' T'' : BigProetaleOver B S hS}
    (f : T' ⟶ T) (g : T'' ⟶ T') :
    systemPullbackAdjoint B S hS D (g ≫ f) =
      systemPullbackAdjoint B S hS D f ≫
        (smallProetalePushforward B f.left).map (systemPullbackAdjoint B S hS D g) ≫
          (smallProetalePushforwardCompIso B f.left g.left).hom.app (D.sheaf T'') := by
  let e := smallProetalePushforwardCompIso B f.left g.left
  have h := homEquiv_comp_leftAdjointCompIso
    (smallProetalePullbackAdjunction B f.left) (smallProetalePullbackAdjunction B g.left)
    (smallProetalePullbackAdjunction B (g.left ≫ f.left)) e (D.pullback (g ≫ f))
  change ((smallProetalePullbackAdjunction B f.left).comp
    (smallProetalePullbackAdjunction B g.left)).homEquiv _ _
      ((smallProetaleInverseImageCompIso B f.left g.left).hom.app (D.sheaf T) ≫
        D.pullback (g ≫ f)) =
      systemPullbackAdjoint B S hS D (g ≫ f) ≫ e.inv.app (D.sheaf T'') at h
  rw [← D.pullback_comp f g, systemPullbackAdjoint_comp_map B S hS D f g] at h
  calc
    _ = (systemPullbackAdjoint B S hS D (g ≫ f) ≫ e.inv.app (D.sheaf T'')) ≫
          e.hom.app (D.sheaf T'') := by simp
    _ = _ := by rw [← h, Category.assoc]

/-- Composition of two transition maps, expressed through compatible maps into base changes. -/
private theorem systemPullbackAdjoint_comp_app
    (D : BigProetaleSheafData.{u, v} B S hS)
    {T T' T'' : BigProetaleOver B S hS} (f : T' ⟶ T) (g : T'' ⟶ T')
    {U : SmallProetale B T.left.obj T.left.property}
    {V : SmallProetale B T'.left.obj T'.left.property}
    {W : SmallProetale B T''.left.obj T''.left.property}
    (p : V ⟶ (smallProetaleBaseChange B T'.left T.left f.left).obj U)
    (q : W ⟶ (smallProetaleBaseChange B T''.left T'.left g.left).obj V)
    (r : W ⟶ (smallProetaleBaseChange B T''.left T.left (g.left ≫ f.left)).obj U)
    (he : r ≫ (smallProetaleBaseChange_compIso B f.left g.left).inv.app U =
      q ≫ (smallProetaleBaseChange B T''.left T'.left g.left).map p) :
    (systemPullbackAdjoint B S hS D (g ≫ f)).hom.app (op U) ≫ (D.sheaf T'').obj.map r.op =
      ((systemPullbackAdjoint B S hS D f).hom.app (op U) ≫ (D.sheaf T').obj.map p.op) ≫
        ((systemPullbackAdjoint B S hS D g).hom.app (op V) ≫ (D.sheaf T'').obj.map q.op) := by
  have hc := congrArg (fun q => q.hom.app (op U))
    (systemPullbackAdjoint_comp B S hS D f g)
  have hn := (systemPullbackAdjoint B S hS D g).hom.naturality p.op
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Functor.sheafPushforwardContinuous_map_hom_app] at hc
  rw [hc]
  change ((systemPullbackAdjoint B S hS D f).hom.app (op U) ≫
    (systemPullbackAdjoint B S hS D g).hom.app
      (op ((smallProetaleBaseChange B T'.left T.left f.left).obj U)) ≫
    (D.sheaf T'').obj.map ((smallProetaleBaseChange_compIso B f.left g.left).inv.app U).op) ≫
    (D.sheaf T'').obj.map r.op = _
  simp only [Category.assoc, ← Functor.map_comp, ← op_comp, he]
  simp only [op_comp, Functor.map_comp]
  congr 1
  dsimp [smallProetalePushforward, Functor.sheafPushforwardContinuous] at hn ⊢
  simpa only [Category.assoc] using
    (congrArg (fun q' => q' ≫ (D.sheaf T'').obj.map q.op) hn).symm

private noncomputable def systemRestrictionAtIdentity
    (D : BigProetaleSheafData.{u, v} B S hS)
    {T T' : BigProetaleOver B S hS} (f : T' ⟶ T) :
    (D.sheaf T).obj.obj (op (smallProetaleIdentity B T.left)) ⟶
      (D.sheaf T').obj.obj (op (smallProetaleIdentity B T'.left)) :=
  (systemPullbackAdjoint B S hS D f).hom.app (op (smallProetaleIdentity B T.left)) ≫
    (D.sheaf T').obj.map (smallProetaleBaseChangeIdentityIso B f.left).inv.op

private theorem systemRestrictionAtIdentity_naturality
    {D E : BigProetaleSheafData.{u, v} B S hS}
    (φ : BigProetaleSheafData.Hom B S hS D E)
    {T T' : BigProetaleOver B S hS} (f : T' ⟶ T)
    (x : (D.sheaf T).obj.obj (op (smallProetaleIdentity B T.left))) :
    systemRestrictionAtIdentity B S hS E f
        ((φ.app T).hom.app (op (smallProetaleIdentity B T.left)) x) =
      (φ.app T').hom.app (op (smallProetaleIdentity B T'.left))
        (systemRestrictionAtIdentity B S hS D f x) := by
  exact ConcreteCategory.congr_hom
    (systemPullbackAdjoint_naturality_app B S hS φ f
      (smallProetaleBaseChangeIdentityIso B f.left).inv) x

private theorem systemRestrictionAtIdentity_comp
    (D : BigProetaleSheafData.{u, v} B S hS)
    {T T' T'' : BigProetaleOver B S hS} (f : T' ⟶ T) (g : T'' ⟶ T') :
    systemRestrictionAtIdentity B S hS D (g ≫ f) =
      systemRestrictionAtIdentity B S hS D f ≫
        systemRestrictionAtIdentity B S hS D g := by
  unfold systemRestrictionAtIdentity
  exact systemPullbackAdjoint_comp_app B S hS D f g _ _ _
    (smallProetaleLift_comp B f.left g.left (smallProetaleIdentity B T.left)
      (smallProetaleIdentity B T'.left) (smallProetaleIdentity B T''.left) f.left
      (by simp [smallIdentity]) g.left (by simp [smallIdentity]))

private noncomputable def smallProetaleBaseChangeIdIso (T : B.Scheme) :
    smallProetaleBaseChange B T T (𝟙 T) ≅ 𝟭 _ := by
  refine NatIso.ofComponents
    (fun U => (IsWeaklyEtaleOver B T.obj T.property).isoMk (Over.pullbackId.app U.obj)) ?_
  intro X Y h
  apply (SmallProetale.inclusion B T.obj T.property).map_injective
  exact Over.pullbackId.hom.naturality h.hom

private theorem systemRestrictionAtIdentity_id
    (D : BigProetaleSheafData.{u, v} B S hS)
    (T : BigProetaleOver B S hS) :
    systemRestrictionAtIdentity B S hS D (𝟙 T) = 𝟙 _ := by
  have hw : WeaklyEtale (B.inclusion.map (𝟙 T : T ⟶ T).left) := by
    show WeaklyEtale (B.inclusion.map (𝟙 T.left))
    rw [CategoryTheory.Functor.map_id]
    infer_instance
  have hp := D.isIso_pullback (𝟙 T)
  let eR : smallProetalePushforward.{u, v} B (𝟙 T.left) ≅ 𝟭 _ :=
    Functor.sheafPushforwardContinuousId' (smallProetaleBaseChangeIdIso B T.left)
      (Type (max (u + 1) v)) (SmallProetale.topology B T.left.obj T.left.property)
  have heR : (smallProetalePushforward.{u, v} B (𝟙 T.left)).IsEquivalence :=
    (Functor.isEquivalence_iff_of_iso eR).mpr inferInstance
  have hα : IsIso (systemPullbackAdjoint B S hS D (𝟙 T)) := by
    show IsIso ((smallProetalePullbackAdjunction B (𝟙 T.left)).unit.app (D.sheaf T) ≫
      (smallProetalePushforward B (𝟙 T.left)).map (D.pullback (𝟙 T)))
    infer_instance
  have hr : IsIso (systemRestrictionAtIdentity B S hS D (𝟙 T)) := by
    unfold systemRestrictionAtIdentity
    infer_instance
  apply (cancel_mono (systemRestrictionAtIdentity B S hS D (𝟙 T))).mp
  simpa only [Category.id_comp, Category.id_comp (𝟙 T)] using
    (systemRestrictionAtIdentity_comp B S hS D (𝟙 T) (𝟙 T)).symm

private noncomputable def systemPresheaf
    (D : BigProetaleSheafData.{u, v} B S hS) :
    (BigProetaleOver B S hS)ᵒᵖ ⥤ Type (max (u + 1) v) where
  obj T := (D.sheaf T.unop).obj.obj (op (smallProetaleIdentity B T.unop.left))
  map f := systemRestrictionAtIdentity B S hS D f.unop
  map_id T := systemRestrictionAtIdentity_id B S hS D T.unop
  map_comp f g := systemRestrictionAtIdentity_comp B S hS D f.unop g.unop

private noncomputable def systemPresheafFunctor :
    BigProetaleSheafData.{u, v} B S hS ⥤
      ((BigProetaleOver B S hS)ᵒᵖ ⥤ Type (max (u + 1) v)) where
  obj D := systemPresheaf B S hS D
  map φ :=
    { app T := (φ.app T.unop).hom.app (op (smallProetaleIdentity B T.unop.left))
      naturality T T' f := by
        ext x
        exact (systemRestrictionAtIdentity_naturality B S hS φ f.unop x).symm }
  map_id D := by ext T; rfl
  map_comp φ ψ := by ext T; rfl

private theorem smallProetaleBaseChangeProjection_naturality
    {T T' : BigProetaleOver B S hS} (f : T' ⟶ T)
    {U V : SmallProetale B T.left.obj T.left.property} (h : U ⟶ V) :
    (smallProetaleToBigProetaleFunctor B T'.left
        (⟨S, hS⟩ : B.Scheme) T'.hom).map
        ((smallProetaleBaseChange B T'.left T.left f.left).map h) ≫
      smallProetaleBaseChangeProjection B S hS f V =
    smallProetaleBaseChangeProjection B S hS f U ≫
      (smallProetaleToBigProetaleFunctor B T.left
        (⟨S, hS⟩ : B.Scheme) T.hom).map h := by
  apply (Over.forget _).map_injective
  simp [smallProetaleBaseChangeProjection, smallProetaleToBigProetaleFunctor,
    smallProetaleBaseChange, Over.pullback]

private noncomputable def restrictionTransitionAdjoint
    (F : Sheaf (BigProetaleOver.topology B S hS) (Type (max (u + 1) v)))
    {T T' : BigProetaleOver B S hS} (f : T' ⟶ T) :
    (smallRestriction B S hS T).obj F ⟶
      (smallProetalePushforward.{u, v} B f.left).obj ((smallRestriction B S hS T').obj F) where
  hom :=
    { app U := F.obj.map (smallProetaleBaseChangeProjection B S hS f U.unop).op
      naturality U V h := by
        change F.obj.map _ ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
        simp only [Functor.op_map]
        rw [← F.obj.map_comp, ← F.obj.map_comp, ← op_comp, ← op_comp]
        exact congrArg (fun q => F.obj.map q.op)
          (smallProetaleBaseChangeProjection_naturality B S hS f h.unop).symm }

private theorem restrictionTransitionAdjoint_naturality
    {F G : Sheaf (BigProetaleOver.topology B S hS) (Type (max (u + 1) v))}
    (φ : F ⟶ G) {T T' : BigProetaleOver B S hS} (f : T' ⟶ T) :
    (smallRestriction B S hS T).map φ ≫ restrictionTransitionAdjoint B S hS G f =
      restrictionTransitionAdjoint B S hS F f ≫
        (smallProetalePushforward.{u, v} B f.left).map ((smallRestriction B S hS T').map φ) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  exact (φ.hom.naturality (smallProetaleBaseChangeProjection B S hS f U.unop).op).symm

private noncomputable def smallProetaleInverseImageRestrictionIso {T T' : B.Scheme} (f : T' ⟶ T)
    [WeaklyEtale (B.inclusion.map f)] :
    smallProetaleInverseImage.{u, v} B f ≅
      letI := smallProetaleMap_isContinuous B f
      (smallProetaleMap B f).sheafPushforwardContinuous (Type (max (u + 1) v))
        (SmallProetale.topology B T'.obj T'.property)
        (SmallProetale.topology B T.obj T.property) := by
  letI := smallProetaleMap_isContinuous B f
  exact (smallProetalePullbackAdjunction B f).leftAdjointUniq
    ((smallProetaleMapPullbackAdjunction B f).sheafPushforwardContinuous
      (E := Type (max (u + 1) v))
      (SmallProetale.topology B T'.obj T'.property)
      (SmallProetale.topology B T.obj T.property))

private def systemTransport (D : BigProetaleSheafData.{u, v} B S hS)
    {T T' : BigProetaleOver B S hS} (f : T' ⟶ T)
    (U : SmallProetale B T.left.obj T.left.property)
    (V : SmallProetale B T'.left.obj T'.left.property)
    (k : V.obj.left ⟶ U.obj.left) (hk : k ≫ U.obj.hom = V.obj.hom ≫ f.left) :
    (D.sheaf T).obj.obj (op U) ⟶ (D.sheaf T').obj.obj (op V) :=
  (systemPullbackAdjoint B S hS D f).hom.app (op U) ≫
    (D.sheaf T').obj.map (smallProetaleLift B f.left U V k hk).op

private theorem systemTransport_comp
    (D : BigProetaleSheafData.{u, v} B S hS)
    {T T' T'' : BigProetaleOver B S hS} (f : T' ⟶ T) (g : T'' ⟶ T')
    (U : SmallProetale B T.left.obj T.left.property)
    (V : SmallProetale B T'.left.obj T'.left.property)
    (W : SmallProetale B T''.left.obj T''.left.property)
    (k : V.obj.left ⟶ U.obj.left) (hk : k ≫ U.obj.hom = V.obj.hom ≫ f.left)
    (l : W.obj.left ⟶ V.obj.left) (hl : l ≫ V.obj.hom = W.obj.hom ≫ g.left) :
    systemTransport B S hS D (g ≫ f) U W (l ≫ k)
        (by change _ = _ ≫ (g.left ≫ f.left)
            rw [Category.assoc, hk, ← Category.assoc, hl, Category.assoc]) =
      systemTransport B S hS D f U V k hk ≫
        systemTransport B S hS D g V W l hl := by
  unfold systemTransport
  exact systemPullbackAdjoint_comp_app B S hS D f g _ _ _
    (smallProetaleLift_comp B f.left g.left U V W k hk l hl)

private def systemSmallRestriction (D : BigProetaleSheafData.{u, v} B S hS)
    {T T' : BigProetaleOver B S hS} (f : T' ⟶ T)
    [WeaklyEtale (B.inclusion.map f.left)] :
    letI := smallProetaleMap_isContinuous B f.left
    ((smallProetaleMap B f.left).sheafPushforwardContinuous
      (Type (max (u + 1) v)) (SmallProetale.topology B T'.left.obj T'.left.property)
      (SmallProetale.topology B T.left.obj T.left.property)).obj (D.sheaf T) ⟶ D.sheaf T' :=
  (smallProetaleInverseImageRestrictionIso B f.left).inv.app (D.sheaf T) ≫ D.pullback f

private theorem systemSmallRestriction_isIso (D : BigProetaleSheafData.{u, v} B S hS)
    {T T' : BigProetaleOver B S hS} (f : T' ⟶ T)
    [WeaklyEtale (B.inclusion.map f.left)] : IsIso (systemSmallRestriction B S hS D f) := by
  have := D.isIso_pullback f
  unfold systemSmallRestriction
  infer_instance

private theorem systemSmallRestriction_eq_adjoint
    (D : BigProetaleSheafData.{u, v} B S hS)
    {T T' : BigProetaleOver B S hS} (f : T' ⟶ T)
    [WeaklyEtale (B.inclusion.map f.left)] :
    letI := smallProetaleMap_isContinuous B f.left
    systemSmallRestriction B S hS D f =
      (((smallProetaleMapPullbackAdjunction B f.left).sheafPushforwardContinuous
        (E := Type (max (u + 1) v))
        (SmallProetale.topology B T'.left.obj T'.left.property)
        (SmallProetale.topology B T.left.obj T.left.property)).homEquiv _ _).symm
          (systemPullbackAdjoint B S hS D f) := by
  have := smallProetaleMap_isContinuous B f.left
  let adj := smallProetalePullbackAdjunction.{u, v} B f.left
  let adj' := (smallProetaleMapPullbackAdjunction B f.left).sheafPushforwardContinuous
    (E := Type (max (u + 1) v))
    (SmallProetale.topology B T'.left.obj T'.left.property)
    (SmallProetale.topology B T.left.obj T.left.property)
  show _ = (adj'.homEquiv _ _).symm _
  apply (adj'.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply]
  show adj'.unit.app (D.sheaf T) ≫
    (smallProetalePushforward B f.left).map
      ((adj.leftAdjointUniq adj').inv.app (D.sheaf T) ≫ D.pullback f) =
    adj.unit.app (D.sheaf T) ≫ (smallProetalePushforward B f.left).map (D.pullback f)
  rw [← adj.unit_leftAdjointUniq_hom_app adj' (D.sheaf T)]
  rw [Category.assoc, ← (smallProetalePushforward B f.left).map_comp]
  simp only [Iso.hom_inv_id_app_assoc]

private theorem systemSmallRestriction_app
    (D : BigProetaleSheafData.{u, v} B S hS)
    {T T' : BigProetaleOver B S hS} (f : T' ⟶ T)
    [WeaklyEtale (B.inclusion.map f.left)]
    (V : SmallProetale B T'.left.obj T'.left.property) :
    (systemSmallRestriction B S hS D f).hom.app (op V) =
      systemTransport B S hS D f ((smallProetaleMap B f.left).obj V) V (𝟙 V.obj.left)
        (by simp [smallProetaleMap]) := by
  rw [systemSmallRestriction_eq_adjoint, Adjunction.homEquiv_counit]
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  show (systemPullbackAdjoint B S hS D f).hom.app
      (op ((smallProetaleMap B f.left).obj V)) ≫ _ = _
  congr 1
  show (D.sheaf T').obj.map ((smallProetaleMapPullbackAdjunction B f.left).unit.app V).op = _
  apply congrArg (fun q : V ⟶
    (smallProetaleBaseChange B T'.left T.left f.left).obj
      ((smallProetaleMap B f.left).obj V) => (D.sheaf T').obj.map q.op)
  apply (SmallProetale.inclusion B T'.left.obj T'.left.property).map_injective
  unfold smallProetaleMapPullbackAdjunction
  rw [Adjunction.map_restrictFullyFaithful_unit_app]
  simp [smallProetaleLift, Over.mapPullbackAdj_unit_app]
  rfl

private def smallProetaleMapHom {T T' : B.Scheme} (f : T' ⟶ T)
    [WeaklyEtale (B.inclusion.map f)]
    (U : SmallProetale B T.obj T.property) (V : SmallProetale B T'.obj T'.property)
    (k : V.obj.left ⟶ U.obj.left) (hk : k ≫ U.obj.hom = V.obj.hom ≫ f) :
    (smallProetaleMap B f).obj V ⟶ U :=
  ⟨Over.homMk k hk⟩

private theorem systemTransport_eq_restriction
    (D : BigProetaleSheafData.{u, v} B S hS)
    {T T' : BigProetaleOver B S hS} (f : T' ⟶ T)
    [WeaklyEtale (B.inclusion.map f.left)]
    (U : SmallProetale B T.left.obj T.left.property)
    (V : SmallProetale B T'.left.obj T'.left.property)
    (k : V.obj.left ⟶ U.obj.left) (hk : k ≫ U.obj.hom = V.obj.hom ≫ f.left) :
    systemTransport B S hS D f U V k hk =
      (D.sheaf T).obj.map (smallProetaleMapHom B f.left U V k hk).op ≫
        (systemSmallRestriction B S hS D f).hom.app (op V) := by
  let h : (smallProetaleMap B f.left).obj V ⟶ U := smallProetaleMapHom B f.left U V k hk
  have hl : smallProetaleLift B f.left U V k hk =
      smallProetaleLift B f.left ((smallProetaleMap B f.left).obj V) V (𝟙 V.obj.left)
        (by simp [smallProetaleMap]) ≫
      (smallProetaleBaseChange B T'.left T.left f.left).map h := by
    apply (SmallProetale.inclusion B T'.left.obj T'.left.property).map_injective
    apply (Over.forget _).map_injective
    apply pullback.hom_ext <;>
      simp [smallProetaleLift, smallProetaleBaseChange,
        Over.pullback, h, smallProetaleMapHom]
  have hn := (systemPullbackAdjoint B S hS D f).hom.naturality h.op
  rw [systemSmallRestriction_app]
  unfold systemTransport
  rw [hl, op_comp, Functor.map_comp]
  dsimp [smallProetalePushforward, Functor.sheafPushforwardContinuous] at hn ⊢
  simpa only [Category.assoc] using
    (congrArg (fun q => q ≫ (D.sheaf T').obj.map
      (smallProetaleLift B f.left ((smallProetaleMap B f.left).obj V) V (𝟙 V.obj.left)
        (by simp [smallProetaleMap])).op) hn).symm

private theorem systemTransport_isIso
    (D : BigProetaleSheafData.{u, v} B S hS)
    {T T' : BigProetaleOver B S hS} (f : T' ⟶ T)
    [WeaklyEtale (B.inclusion.map f.left)]
    (U : SmallProetale B T.left.obj T.left.property)
    (V : SmallProetale B T'.left.obj T'.left.property)
    (k : V.obj.left ⟶ U.obj.left) [IsIso k]
    (hk : k ≫ U.obj.hom = V.obj.hom ≫ f.left) :
    IsIso (systemTransport B S hS D f U V k hk) := by
  have hh : IsIso (smallProetaleMapHom B f.left U V k hk) := by
    let e : (smallProetaleMap B f.left).obj V ≅ U :=
      (IsWeaklyEtaleOver B T.left.obj T.left.property).isoMk
        (Over.isoMk (asIso k) hk)
    show IsIso e.hom
    infer_instance
  have := systemSmallRestriction_isIso B S hS D f
  rw [systemTransport_eq_restriction]
  infer_instance

private theorem systemTransport_id
    (D : BigProetaleSheafData.{u, v} B S hS)
    (T : BigProetaleOver B S hS)
    (U : SmallProetale B T.left.obj T.left.property) :
    systemTransport B S hS D (𝟙 T) U U (𝟙 U.obj.left) (by simp) = 𝟙 _ := by
  have hw : WeaklyEtale (B.inclusion.map (𝟙 T : T ⟶ T).left) := by
    show WeaklyEtale (B.inclusion.map (𝟙 T.left))
    rw [CategoryTheory.Functor.map_id]
    infer_instance
  have := systemTransport_isIso B S hS D (𝟙 T) U U (𝟙 U.obj.left) (by simp)
  apply (cancel_mono (systemTransport B S hS D (𝟙 T) U U (𝟙 U.obj.left) (by simp))).mp
  simpa only [Category.id_comp] using
    (systemTransport_comp B S hS D (𝟙 T) (𝟙 T) U U U
      (𝟙 U.obj.left) (by simp) (𝟙 U.obj.left) (by simp)).symm

private theorem systemTransport_precomp
    (D : BigProetaleSheafData.{u, v} B S hS)
    {T T' : BigProetaleOver B S hS} (f : T' ⟶ T)
    (U : SmallProetale B T.left.obj T.left.property)
    {V W : SmallProetale B T'.left.obj T'.left.property} (h : W ⟶ V)
    (k : V.obj.left ⟶ U.obj.left) (hk : k ≫ U.obj.hom = V.obj.hom ≫ f.left) :
    systemTransport B S hS D f U W (h.hom.left ≫ k)
        (by rw [Category.assoc, hk, ← Category.assoc, Over.w h.hom]) =
      systemTransport B S hS D f U V k hk ≫ (D.sheaf T').obj.map h.op := by
  have hl : smallProetaleLift B f.left U W (h.hom.left ≫ k)
      (by rw [Category.assoc, hk, ← Category.assoc, Over.w h.hom]) =
      h ≫ smallProetaleLift B f.left U V k hk := by
    apply (SmallProetale.inclusion B T'.left.obj T'.left.property).map_injective
    apply (Over.forget _).map_injective
    apply pullback.hom_ext <;> simp [smallProetaleLift]
  simp only [systemTransport, hl, op_comp, Functor.map_comp, Category.assoc]

private theorem systemTransport_vertical
    (D : BigProetaleSheafData.{u, v} B S hS)
    (T : BigProetaleOver B S hS)
    {U V : SmallProetale B T.left.obj T.left.property} (h : V ⟶ U) :
    systemTransport B S hS D (𝟙 T) U V h.hom.left (by simp) =
      (D.sheaf T).obj.map h.op := by
  simpa only [Category.comp_id, systemTransport_id, Category.id_comp] using
    systemTransport_precomp B S hS D (𝟙 T) U h (𝟙 U.obj.left) (by simp)

private def smallObjectStructure (T : BigProetaleOver B S hS)
    (U : SmallProetale B T.left.obj T.left.property) :
    (smallProetaleToBigProetaleFunctor B T.left
      (⟨S, hS⟩ : B.Scheme) T.hom).obj U ⟶ T :=
  Over.homMk U.obj.hom rfl

private def systemComparisonApp (D : BigProetaleSheafData.{u, v} B S hS)
    (T : BigProetaleOver B S hS) (U : SmallProetale B T.left.obj T.left.property) :
    (D.sheaf T).obj.obj (op U) ⟶
      (systemPresheaf B S hS D).obj
        (op ((smallProetaleToBigProetaleFunctor B T.left
          (⟨S, hS⟩ : B.Scheme) T.hom).obj U)) :=
  systemTransport B S hS D (smallObjectStructure B S hS T U) U
    (smallProetaleIdentity B U.obj.left) (𝟙 U.obj.left)
    (by simp [smallIdentity, smallObjectStructure])

private theorem systemComparisonApp_isIso (D : BigProetaleSheafData.{u, v} B S hS)
    (T : BigProetaleOver B S hS) (U : SmallProetale B T.left.obj T.left.property) :
    IsIso (systemComparisonApp B S hS D T U) := by
  have hw : WeaklyEtale (B.inclusion.map (smallObjectStructure B S hS T U).left) := U.property
  have hi : IsIso (C := B.Scheme) (𝟙 U.obj.left) := inferInstance
  exact systemTransport_isIso B S hS D (smallObjectStructure B S hS T U) U
    (smallProetaleIdentity B U.obj.left) (𝟙 U.obj.left) _

private theorem systemRestrictionAtIdentity_eq_transport
    (D : BigProetaleSheafData.{u, v} B S hS)
    {T T' : BigProetaleOver B S hS} (f : T' ⟶ T) :
    systemRestrictionAtIdentity B S hS D f =
      systemTransport B S hS D f (smallProetaleIdentity B T.left)
        (smallProetaleIdentity B T'.left) f.left
        ((Category.comp_id f.left).trans (Category.id_comp f.left).symm) := rfl

private theorem systemComparisonApp_naturality
    (D : BigProetaleSheafData.{u, v} B S hS)
    (T : BigProetaleOver B S hS)
    {U V : SmallProetale B T.left.obj T.left.property} (h : V ⟶ U) :
    (D.sheaf T).obj.map h.op ≫ systemComparisonApp B S hS D T V =
      systemComparisonApp B S hS D T U ≫
        (systemPresheaf B S hS D).map
          ((smallProetaleToBigProetaleFunctor B T.left
            (⟨S, hS⟩ : B.Scheme) T.hom).map h).op := by
  let i := smallProetaleToBigProetaleFunctor B T.left
    (⟨S, hS⟩ : B.Scheme) T.hom
  have hf : i.map h ≫ smallObjectStructure B S hS T U =
      smallObjectStructure B S hS T V := by
    apply (Over.forget _).map_injective
    exact Over.w h.hom
  have h₁ := systemTransport_comp B S hS D (smallObjectStructure B S hS T U) (i.map h)
    U (smallProetaleIdentity B U.obj.left) (smallProetaleIdentity B V.obj.left)
    (𝟙 U.obj.left) (by simp [smallIdentity, smallObjectStructure])
    h.hom.left (by simp [smallIdentity, i,
      smallProetaleToBigProetaleFunctor])
  have h₂ := systemTransport_comp B S hS D (𝟙 T) (smallObjectStructure B S hS T V)
    U V (smallProetaleIdentity B V.obj.left) h.hom.left (by simp)
    (𝟙 V.obj.left) (by simp [smallIdentity, smallObjectStructure])
  simp only [hf, Category.comp_id, systemTransport_vertical] at h₁ h₂
  show (D.sheaf T).obj.map h.op ≫ systemComparisonApp B S hS D T V =
    systemComparisonApp B S hS D T U ≫ systemRestrictionAtIdentity B S hS D (i.map h)
  rw [systemRestrictionAtIdentity_eq_transport]
  exact h₂.symm.trans h₁

private noncomputable def systemPresheafRestrictionIso
    (D : BigProetaleSheafData.{u, v} B S hS) (T : BigProetaleOver B S hS) :
    (D.sheaf T).obj ≅
      (smallProetaleToBigProetaleFunctor B T.left
        (⟨S, hS⟩ : B.Scheme) T.hom).op ⋙ systemPresheaf B S hS D := by
  have := fun U => systemComparisonApp_isIso B S hS D T U
  exact NatIso.ofComponents (fun U => asIso (systemComparisonApp B S hS D T U.unop))
    (fun h => systemComparisonApp_naturality B S hS D T h.unop)

private theorem systemPresheaf_isSheaf (D : BigProetaleSheafData.{u, v} B S hS) :
    Presheaf.IsSheaf (BigProetaleOver.topology B S hS) (systemPresheaf B S hS D) := by
  let J := BigProetaleOver.topology B S hS
  let P := systemPresheaf B S hS D
  let η := toSheafify J P
  have hη : ∀ T, IsIso (η.app T) := by
    intro T
    let i := smallProetaleToBigProetaleFunctor B T.unop.left
      (⟨S, hS⟩ : B.Scheme) T.unop.hom
    let K := SmallProetale.topology B T.unop.left.obj T.unop.left.property
    have hs : Presheaf.IsSheaf K (i.op ⋙ P) :=
      (Presheaf.isSheaf_of_iso_iff (systemPresheafRestrictionIso B S hS D T.unop)).mp
        (D.sheaf T.unop).property
    have hu := isIso_toSheafify K hs
    have hic : i.IsCocontinuous K J :=
      smallProetaleToBigProetaleFunctor_isCocontinuous B T.unop.left
        (⟨S, hS⟩ : B.Scheme) T.unop.hom
    have hiCont : i.IsContinuous K J :=
      smallProetaleToBigProetaleFunctor_isContinuous B T.unop.left
        (⟨S, hS⟩ : B.Scheme) T.unop.hom
    have hi : IsIso (Functor.whiskerLeft i.op η) := by
      rw [← i.toSheafify_pullbackSheafificationCompatibility (Type (max (u + 1) v)) K J P]
      infer_instance
    have hI : i.obj (smallProetaleIdentity B T.unop.left) = T.unop := by
      show Over.mk (𝟙 T.unop.left ≫ T.unop.hom) = T.unop
      rw [Category.id_comp]
      rfl
    have h := NatIso.isIso_app_of_isIso (Functor.whiskerLeft i.op η)
      (op (smallProetaleIdentity B T.unop.left))
    change IsIso (η.app (op (i.obj (smallProetaleIdentity B T.unop.left)))) at h
    exact Eq.mp (congrArg (fun X => IsIso (η.app (op X))) hI) h
  have : IsIso η := NatIso.isIso_of_isIso_app η
  exact (Presheaf.isSheaf_of_iso_iff (asIso η)).mpr
    ((presheafToSheaf J (Type (max (u + 1) v))).obj P).property

private noncomputable def systemSheafFunctor :
    BigProetaleSheafData.{u, v} B S hS ⥤
      Sheaf (BigProetaleOver.topology B S hS) (Type (max (u + 1) v)) :=
  ObjectProperty.lift _ (systemPresheafFunctor B S hS) (systemPresheaf_isSheaf B S hS)

private theorem smallProetaleBaseChangeProjection_comp
    {T T' T'' : BigProetaleOver B S hS} (f : T' ⟶ T) (g : T'' ⟶ T')
    (U : SmallProetale B T.left.obj T.left.property) :
    (smallProetaleToBigProetaleFunctor B T''.left
        (⟨S, hS⟩ : B.Scheme) T''.hom).map
        ((smallProetaleBaseChange_compIso B f.left g.left).inv.app U) ≫
      smallProetaleBaseChangeProjection B S hS g
        ((smallProetaleBaseChange B T'.left T.left f.left).obj U) ≫
      smallProetaleBaseChangeProjection B S hS f U =
      smallProetaleBaseChangeProjection B S hS (g ≫ f) U := by
  apply (Over.forget _).map_injective
  simp [smallProetaleBaseChangeProjection, smallProetaleBaseChange_compIso,
    smallProetaleToBigProetaleFunctor, smallProetaleBaseChange,
    Over.pullbackComp, conjugateIsoEquiv, conjugateEquiv, Over.mapPullbackAdj,
    Over.mapComp, Over.pullback, Category.assoc]

private theorem restrictionTransitionAdjoint_comp
    (F : Sheaf (BigProetaleOver.topology B S hS) (Type (max (u + 1) v)))
    {T T' T'' : BigProetaleOver B S hS} (f : T' ⟶ T) (g : T'' ⟶ T') :
    restrictionTransitionAdjoint B S hS F (g ≫ f) =
      restrictionTransitionAdjoint B S hS F f ≫
        (smallProetalePushforward B f.left).map (restrictionTransitionAdjoint B S hS F g) ≫
          (smallProetalePushforwardCompIso B f.left g.left).hom.app
            ((smallRestriction B S hS T'').obj F) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  show F.obj.map _ = F.obj.map _ ≫ F.obj.map _ ≫ F.obj.map _
  simp only [Functor.op_map, NatTrans.op_app]
  rw [← F.obj.map_comp, ← F.obj.map_comp, ← op_comp, ← op_comp]
  exact congrArg (fun q => F.obj.map q.op)
    (smallProetaleBaseChangeProjection_comp B S hS f g U.unop).symm

private def restrictionTransition
    (F : Sheaf (BigProetaleOver.topology B S hS) (Type (max (u + 1) v)))
    {T T' : BigProetaleOver B S hS} (f : T' ⟶ T) :
    (smallProetaleInverseImage B f.left).obj ((smallRestriction B S hS T).obj F) ⟶
      (smallRestriction B S hS T').obj F :=
  ((smallProetalePullbackAdjunction B f.left).homEquiv _ _).symm
    (restrictionTransitionAdjoint B S hS F f)

private theorem restrictionTransition_comp
    (F : Sheaf (BigProetaleOver.topology B S hS) (Type (max (u + 1) v)))
    {T T' T'' : BigProetaleOver B S hS} (f : T' ⟶ T) (g : T'' ⟶ T') :
    (smallProetaleInverseImage B g.left).map (restrictionTransition B S hS F f) ≫
        restrictionTransition B S hS F g =
      (smallProetaleInverseImageCompIso B f.left g.left).hom.app
        ((smallRestriction B S hS T).obj F) ≫ restrictionTransition B S hS F (g ≫ f) := by
  apply (((smallProetalePullbackAdjunction B f.left).comp
    (smallProetalePullbackAdjunction B g.left)).homEquiv _ _).injective
  rw [homEquiv_comp_map]
  rw [show smallProetaleInverseImageCompIso B f.left g.left =
      (smallProetalePullbackAdjunction B f.left).leftAdjointCompIso
        (smallProetalePullbackAdjunction B g.left)
        (smallProetalePullbackAdjunction B (g.left ≫ f.left))
        (smallProetalePushforwardCompIso B f.left g.left) from rfl]
  rw [homEquiv_comp_leftAdjointCompIso]
  simp only [restrictionTransition, Equiv.apply_symm_apply]
  rw [restrictionTransitionAdjoint_comp]
  simp

private theorem restrictionTransition_isIso
    (F : Sheaf (BigProetaleOver.topology B S hS) (Type (max (u + 1) v)))
    {T T' : BigProetaleOver B S hS} (f : T' ⟶ T)
    [WeaklyEtale (B.inclusion.map f.left)] :
    IsIso (restrictionTransition B S hS F f) := by
  have := smallProetaleMap_isContinuous B f.left
  let adj := smallProetalePullbackAdjunction.{u, v} B f.left
  let adj' := (smallProetaleMapPullbackAdjunction B f.left).sheafPushforwardContinuous
    (E := Type (max (u + 1) v))
    (SmallProetale.topology B T'.left.obj T'.left.property)
    (SmallProetale.topology B T.left.obj T.left.property)
  let β := (adj'.homEquiv _ _).symm (restrictionTransitionAdjoint B S hS F f)
  have hβapp : ∀ V, IsIso (β.hom.app V) := by
    intro V
    show IsIso (((adj'.homEquiv _ _).symm
      (restrictionTransitionAdjoint B S hS F f)).hom.app V)
    rw [Adjunction.homEquiv_counit]
    show IsIso (F.obj.map _ ≫ F.obj.map _)
    simp only [Functor.op_map]
    rw [← F.obj.map_comp, ← op_comp]
    let k := (smallProetaleToBigProetaleFunctor B T'.left
      (⟨S, hS⟩ : B.Scheme) T'.hom).map
        ((smallProetaleMapPullbackAdjunction B f.left).unit.app V.unop) ≫
      smallProetaleBaseChangeProjection B S hS f ((smallProetaleMap B f.left).obj V.unop)
    have hkleft : IsIso ((Over.forget _).map k) := by
      show IsIso (((SmallProetale.inclusion B T'.left.obj T'.left.property).map
        ((smallProetaleMapPullbackAdjunction B f.left).unit.app V.unop)).left ≫ _)
      unfold smallProetaleMapPullbackAdjunction
      rw [Adjunction.map_restrictFullyFaithful_unit_app]
      dsimp [smallProetaleMap, SmallProetale.inclusion]
      simpa [Over.mapPullbackAdj_unit_app, smallProetaleBaseChangeProjection] using
        (inferInstance : IsIso (𝟙 V.unop.obj.left))
    have hk : IsIso k := isIso_of_reflects_iso k (Over.forget _)
    exact inferInstanceAs (IsIso (F.obj.map k.op))
  have hβhom : IsIso β.hom := NatIso.isIso_of_isIso_app β.hom
  have hβmap : IsIso ((sheafToPresheaf
      (SmallProetale.topology B T'.left.obj T'.left.property)
      (Type (max (u + 1) v))).map β) := hβhom
  have hβ : IsIso β := isIso_of_reflects_iso β (sheafToPresheaf _ _)
  have he : restrictionTransition B S hS F f =
      (adj.leftAdjointUniq adj').hom.app ((smallRestriction B S hS T).obj F) ≫ β := by
    apply (adj.homEquiv _ _).injective
    rw [adj.homEquiv_naturality_right, adj.homEquiv_leftAdjointUniq_hom_app]
    show (adj.homEquiv _ _) ((adj.homEquiv _ _).symm _) =
      (adj'.homEquiv _ _) β
    simp only [β, Equiv.apply_symm_apply]
  rw [he]
  infer_instance

private def restrictionSheafData
    (F : Sheaf (BigProetaleOver.topology B S hS) (Type (max (u + 1) v))) :
    BigProetaleSheafData.{u, v} B S hS where
  sheaf T := (smallRestriction B S hS T).obj F
  pullback f := restrictionTransition B S hS F f
  pullback_comp := restrictionTransition_comp B S hS F
  isIso_pullback := restrictionTransition_isIso B S hS F

private def restrictionSheafDataFunctor :
    Sheaf (BigProetaleOver.topology B S hS) (Type (max (u + 1) v)) ⥤
      BigProetaleSheafData.{u, v} B S hS where
  obj F := restrictionSheafData B S hS F
  map φ :=
    { app T := (smallRestriction B S hS T).map φ
      naturality f := by
        apply ((smallProetalePullbackAdjunction B f.left).homEquiv _ _).injective
        rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
        simp only [restrictionSheafData, restrictionTransition, Equiv.apply_symm_apply]
        exact restrictionTransitionAdjoint_naturality B S hS φ f }
  map_id F := BigProetaleSheafData.Hom.ext (h := fun T => (smallRestriction B S hS T).map_id F)
  map_comp φ ψ :=
    BigProetaleSheafData.Hom.ext (h := fun T => (smallRestriction B S hS T).map_comp φ ψ)

private theorem restrictionSheafData_adjoint
    (F : Sheaf (BigProetaleOver.topology B S hS) (Type (max (u + 1) v)))
    {T T' : BigProetaleOver B S hS} (f : T' ⟶ T) :
    systemPullbackAdjoint B S hS (restrictionSheafData B S hS F) f =
      restrictionTransitionAdjoint B S hS F f :=
  ((smallProetalePullbackAdjunction B f.left).homEquiv _ _).apply_symm_apply _

private def bigSmallIdentityIso (T : BigProetaleOver B S hS) :
    (smallProetaleToBigProetaleFunctor B T.left
      (⟨S, hS⟩ : B.Scheme) T.hom).obj (smallProetaleIdentity B T.left) ≅ T :=
  Over.isoMk (Iso.refl _) rfl

private def reconstructionRestrictionIso
    (F : Sheaf (BigProetaleOver.topology B S hS) (Type (max (u + 1) v))) :
    (systemSheafFunctor B S hS).obj ((restrictionSheafDataFunctor B S hS).obj F) ≅ F := by
  apply ObjectProperty.isoMk
  refine NatIso.ofComponents (fun T => F.obj.mapIso (bigSmallIdentityIso B S hS T.unop).op) ?_
  intro T T' f
  change systemRestrictionAtIdentity B S hS (restrictionSheafData B S hS F) f.unop ≫
    F.obj.map _ = F.obj.map _ ≫ F.obj.map f
  unfold systemRestrictionAtIdentity
  rw [restrictionSheafData_adjoint]
  change (F.obj.map _ ≫ F.obj.map _) ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
  simp only [Functor.op_map, ← F.obj.map_comp, ← op_comp]
  apply congrArg F.obj.map
  apply Quiver.Hom.unop_inj
  apply (Over.forget _).map_injective
  simp [bigSmallIdentityIso, smallProetaleBaseChangeProjection, smallProetaleBaseChangeIdentityIso,
    smallProetaleToBigProetaleFunctor, smallIdentity]

private def reconstructionRestrictionNatIso :
    restrictionSheafDataFunctor.{u, v} B S hS ⋙ systemSheafFunctor B S hS ≅ 𝟭 _ := by
  refine NatIso.ofComponents (reconstructionRestrictionIso B S hS) ?_
  intro F G φ
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext T
  exact (φ.hom.naturality (bigSmallIdentityIso B S hS T.unop).inv.op).symm

private def systemComponentIso
    (D : BigProetaleSheafData.{u, v} B S hS) (T : BigProetaleOver B S hS) :
    D.sheaf T ≅ (smallRestriction B S hS T).obj ((systemSheafFunctor B S hS).obj D) :=
  ObjectProperty.isoMk _ (systemPresheafRestrictionIso B S hS D T)

private theorem systemTransport_baseChange
    (D : BigProetaleSheafData.{u, v} B S hS)
    {T T' : BigProetaleOver B S hS} (f : T' ⟶ T)
    (U : SmallProetale B T.left.obj T.left.property) :
    systemTransport B S hS D f U
        ((smallProetaleBaseChange B T'.left T.left f.left).obj U)
        (pullback.fst U.obj.hom f.left) (pullback.condition) =
      (systemPullbackAdjoint B S hS D f).hom.app (op U) := by
  have h : smallProetaleLift B f.left U
      ((smallProetaleBaseChange B T'.left T.left f.left).obj U)
      (pullback.fst U.obj.hom f.left) (pullback.condition) = 𝟙 _ := by
    apply (SmallProetale.inclusion B T'.left.obj T'.left.property).map_injective
    apply (Over.forget _).map_injective
    apply pullback.hom_ext <;> simp [smallProetaleLift, smallProetaleBaseChange]
  simp only [systemTransport, h, op_id]
  dsimp [smallProetalePushforward, Functor.sheafPushforwardContinuous]
  rw [(D.sheaf T').obj.map_id, Category.comp_id]

private theorem systemComponentIso_adjoint
    (D : BigProetaleSheafData.{u, v} B S hS)
    {T T' : BigProetaleOver B S hS} (f : T' ⟶ T) :
    (systemComponentIso B S hS D T).hom ≫
        restrictionTransitionAdjoint B S hS ((systemSheafFunctor B S hS).obj D) f =
      systemPullbackAdjoint B S hS D f ≫
        (smallProetalePushforward B f.left).map (systemComponentIso B S hS D T').hom := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  let V := (smallProetaleBaseChange B T'.left T.left f.left).obj U.unop
  let p := smallProetaleBaseChangeProjection B S hS f U.unop
  have hp : p ≫ smallObjectStructure B S hS T U.unop =
      smallObjectStructure B S hS T' V ≫ f := by
    apply (Over.forget _).map_injective
    exact pullback.condition
  have h₁ := systemTransport_comp B S hS D
    (smallObjectStructure B S hS T U.unop) p U.unop
    (smallProetaleIdentity B U.unop.obj.left) (smallProetaleIdentity B V.obj.left)
    (𝟙 U.unop.obj.left) (by simp [smallIdentity, smallObjectStructure])
    p.left (by simp [smallIdentity])
  have h₂ := systemTransport_comp B S hS D f (smallObjectStructure B S hS T' V)
    U.unop V (smallProetaleIdentity B V.obj.left)
    (pullback.fst U.unop.obj.hom f.left) (pullback.condition)
    (𝟙 V.obj.left) (by simp [smallIdentity, smallObjectStructure])
  simp only [hp] at h₁ h₂
  show systemComparisonApp B S hS D T U.unop ≫
      systemRestrictionAtIdentity B S hS D p =
    (systemPullbackAdjoint B S hS D f).hom.app U ≫ systemComparisonApp B S hS D T' V
  rw [systemRestrictionAtIdentity_eq_transport]
  rw [systemTransport_baseChange] at h₂
  exact h₁.symm.trans h₂

private def systemUnitHom (D : BigProetaleSheafData.{u, v} B S hS) :
    D ⟶ (restrictionSheafDataFunctor B S hS).obj ((systemSheafFunctor B S hS).obj D) where
  app T := (systemComponentIso B S hS D T).hom
  naturality f := by
    apply ((smallProetalePullbackAdjunction B f.left).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    change (systemComponentIso B S hS D _).hom ≫
      systemPullbackAdjoint B S hS (restrictionSheafData B S hS _) f =
      systemPullbackAdjoint B S hS D f ≫ _
    rw [restrictionSheafData_adjoint]
    exact systemComponentIso_adjoint B S hS D f

private def systemUnitIso (D : BigProetaleSheafData.{u, v} B S hS) :
    D ≅ (restrictionSheafDataFunctor B S hS).obj ((systemSheafFunctor B S hS).obj D) where
  hom := systemUnitHom B S hS D
  inv :=
    { app T := (systemComponentIso B S hS D T).inv
      naturality := by
        intro T T' f
        apply (cancel_mono (systemComponentIso B S hS D T').hom).mp
        dsimp only [restrictionSheafDataFunctor, restrictionSheafData]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        have hn := (systemUnitHom B S hS D).naturality f
        change (smallProetaleInverseImage B f.left).map (systemComponentIso B S hS D T).hom ≫ _ =
          D.pullback f ≫ (systemComponentIso B S hS D T').hom at hn
        dsimp only [restrictionSheafDataFunctor, restrictionSheafData] at hn
        rw [← hn, ← Category.assoc, ← Functor.map_comp]
        simp }
  hom_inv_id :=
    BigProetaleSheafData.Hom.ext (h := fun T => (systemComponentIso B S hS D T).hom_inv_id)
  inv_hom_id :=
    BigProetaleSheafData.Hom.ext (h := fun T => (systemComponentIso B S hS D T).inv_hom_id)

private theorem systemTransport_naturality
    {D E : BigProetaleSheafData.{u, v} B S hS} (φ : D ⟶ E)
    {T T' : BigProetaleOver B S hS} (f : T' ⟶ T)
    (U : SmallProetale B T.left.obj T.left.property)
    (V : SmallProetale B T'.left.obj T'.left.property)
    (k : V.obj.left ⟶ U.obj.left) (hk : k ≫ U.obj.hom = V.obj.hom ≫ f.left) :
    (φ.app T).hom.app (op U) ≫ systemTransport B S hS E f U V k hk =
      systemTransport B S hS D f U V k hk ≫ (φ.app T').hom.app (op V) := by
  unfold systemTransport
  exact systemPullbackAdjoint_naturality_app B S hS φ f _

private def systemUnitNatIso :
    𝟭 (BigProetaleSheafData.{u, v} B S hS) ≅
      systemSheafFunctor B S hS ⋙ restrictionSheafDataFunctor B S hS := by
  refine NatIso.ofComponents (systemUnitIso B S hS) ?_
  intro D E φ
  apply BigProetaleSheafData.Hom.ext
  intro T
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  exact systemTransport_naturality B S hS φ (smallObjectStructure B S hS T U.unop)
    U.unop (smallProetaleIdentity B U.unop.obj.left) (𝟙 U.unop.obj.left) _

private def bigProetaleSheafEquivalence :
    Sheaf (BigProetaleOver.topology B S hS) (Type (max (u + 1) v)) ≌
      BigProetaleSheafData.{u, v} B S hS :=
  CategoryTheory.Equivalence.mk (restrictionSheafDataFunctor B S hS)
    (systemSheafFunctor B S hS) (reconstructionRestrictionNatIso B S hS).symm
    (systemUnitNatIso B S hS).symm

private def bigProetaleSheafEquivalenceComponent (T : BigProetaleOver B S hS) :
    (bigProetaleSheafEquivalence.{u, v} B S hS).functor ⋙
        BigProetaleSheafData.eval B S hS T ≅ smallRestriction B S hS T :=
  Iso.refl _

end

/-- **Stacks 098V.** Sheaves on the big pro-étale site over `S` are the same thing as
compatible families of small pro-étale sheaves: there is an equivalence of categories whose
component at every object over `S` is restriction to its small pro-étale site, and which
carries the transition map of a sheaf to restriction along the projection out of the fibre
product. -/
@[stacks 098V "equivalence with big pro-étale sheaves"]
public theorem characterizeSheafBigProetale :
    ∃ (e : Sheaf (BigProetaleOver.topology B S hS) (Type (max (u + 1) v)) ≌
        BigProetaleSheafData.{u, v} B S hS)
      (ι : ∀ T : BigProetaleOver B S hS,
        e.functor ⋙ BigProetaleSheafData.eval B S hS T ≅
          smallRestriction B S hS T),
      ∀ (F : Sheaf (BigProetaleOver.topology B S hS) (Type (max (u + 1) v)))
        {T T' : BigProetaleOver B S hS} (f : T' ⟶ T)
        (U : SmallProetale B T.left.obj T.left.property),
        (((smallProetalePullbackAdjunction B f.left).homEquiv _ _
          ((e.functor.obj F).pullback f)).hom.app (op U)) ≫
            ((ι T').hom.app F).hom.app
              (op ((smallProetaleBaseChange B T'.left T.left f.left).obj U)) =
          ((ι T).hom.app F).hom.app (op U) ≫
            F.obj.map (smallProetaleBaseChangeProjection B S hS f U).op := by
  refine ⟨bigProetaleSheafEquivalence B S hS,
    bigProetaleSheafEquivalenceComponent B S hS, ?_⟩
  intro F T T' f U
  show (((smallProetalePullbackAdjunction B f.left).homEquiv _ _
    (restrictionTransition B S hS F f)).hom.app (op U)) ≫ 𝟙 _ =
      𝟙 _ ≫ F.obj.map (smallProetaleBaseChangeProjection B S hS f U).op
  simp only [restrictionTransition, Equiv.apply_symm_apply,
    Category.comp_id, Category.id_comp]
  rfl
end AlgebraicGeometry.ProEtale

end
