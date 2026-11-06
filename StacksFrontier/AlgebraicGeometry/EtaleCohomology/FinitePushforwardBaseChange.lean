module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkIsomorphismCriterion
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality

/-!
# Étale base change for the direct image along a finite morphism

Consider a cartesian square
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
of schemes of a big étale site with `f` finite, and a sheaf of sets `F` on the small étale site
of `X`. Then the canonical comparison `g⁻¹ f_* F ⟶ f'_* (g')⁻¹ F` is an isomorphism. At a
geometric point `y` of `Y'` both stalks are the product of the stalks of `F` over the lifts of
`y`. A map of sheaves of sets on the small étale site which is bijective on every stalk at a
geometric point is an isomorphism.

## Main definitions

* `AlgebraicGeometry.cartesianLiftEquiv` — composition with `g'` as a bijection from the lifts
  of a geometric point of `Y'` through `f'` to the lifts of its image through `f`.
* `AlgebraicGeometry.smallEtaleBaseChangeNatTrans` — the canonical comparison
  `g⁻¹ f_* ⟶ f'_* (g')⁻¹` for a commuting square, as an adjunction mate.
* `AlgebraicGeometry.finiteBaseChangeStalkEquiv` — a bijection between the stalks of
  `f'_* (g')⁻¹ F` and `g⁻¹ f_* F` at a geometric point of `Y'`.
* `AlgebraicGeometry.smallEtaleBaseChangeMate` — the identification of the two composite direct
  images around the square, whose mate is the canonical comparison.

## Main results

* `AlgebraicGeometry.isIso_of_bijective_etaleStalkMap` — a map of sheaves of sets on the small
  étale site which is bijective on every stalk at a geometric point is an isomorphism.
* `AlgebraicGeometry.pushforwardEtaleStalkComponent_unit` — the canonical map out of the stalk of
  a direct image, evaluated on the adjunction unit, is the stalk comparison of an inverse image.
* `AlgebraicGeometry.isIso_smallEtaleBaseChangeNatTrans_of_stalkMap_eq` — the canonical
  comparison is an isomorphism at a sheaf whose stalk maps are given by
  `AlgebraicGeometry.finiteBaseChangeStalkEquiv`.
* `AlgebraicGeometry.pushforwardEtaleStalkComponent_comp` — the canonical stalk map of a direct
  image is multiplicative in the morphism.
* `AlgebraicGeometry.isIso_smallEtaleBaseChangeNatTrans` — for `f` finite, the canonical
  comparison `g⁻¹ f_* F ⟶ f'_* (g')⁻¹ F` is an isomorphism.

## References

* [Stacks Project, Tag 0959](https://stacks.math.columbia.edu/tag/0959)
* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ u

namespace CategoryTheory

/-- A 2-cell between right adjoints and its mate, compared through the two units: the unit of
the upper adjunction followed by the 2-cell is the unit of the lower adjunction followed by the
right adjoint of the mate. -/
theorem unit_mateEquiv_symm' {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
    {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : TwoSquare R₁ H G R₂) (c : C) :
    G.map (adj₁.unit.app c) ≫ α.app (L₁.obj c) =
      adj₂.unit.app (G.obj c) ≫ R₂.map (((mateEquiv adj₁ adj₂).symm α).app c) :=
  unit_mateEquiv_symm adj₁ adj₂ α c

end CategoryTheory

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u})

section CartesianLifts

variable {X' X Y' Y : B.Scheme} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- For a cartesian square, composing with `g'` is a bijection from the lifts of a geometric
point of `Y'` through `f'` to the lifts of its image in `Y` through `f`. -/
public def cartesianLiftEquiv
    (sq : IsPullback (B.inclusion.map g') (B.inclusion.map f') (B.inclusion.map f)
      (B.inclusion.map g))
    (y : GeometricPoint Y'.1) :
    {p : y.source ⟶ X'.1 // p ≫ B.inclusion.map f' = y.hom} ≃
      {q : y.source ⟶ X.1 //
        q ≫ B.inclusion.map f = (y.map (B.inclusion.map g)).hom} where
  toFun p := ⟨p.1 ≫ B.inclusion.map g', by
    rw [Category.assoc, sq.w, ← Category.assoc, p.2]
    rfl⟩
  invFun q := ⟨sq.lift q.1 y.hom q.2, sq.lift_snd _ _ _⟩
  left_inv p := Subtype.ext (sq.hom_ext (sq.lift_fst _ _ _) ((sq.lift_snd _ _ _).trans p.2.symm))
  right_inv q := Subtype.ext (sq.lift_fst _ _ _)

/-- The canonical base-change comparison `g⁻¹ f_* ⟶ f'_* (g')⁻¹` for sheaves of sets on the
small étale sites attached to a commuting square `g' ≫ f = f' ≫ g` of a big étale site. It is
the mate, along the inverse-image/direct-image adjunctions of `g` and `g'`, of the canonical
identification of the two composite direct images around the square. -/
public def smallEtaleBaseChangeNatTrans (h : g' ≫ f = f' ≫ g) :
    B.smallPushforward f (Type (u + 1)) ⋙ B.smallInverseImage g (Type (u + 1)) ⟶
      B.smallInverseImage g' (Type (u + 1)) ⋙ B.smallPushforward f' (Type (u + 1)) :=
  (mateEquiv (B.smallPullbackAdjunction g' (Type (u + 1)))
      (B.smallPullbackAdjunction g (Type (u + 1)))).symm
    ((smallEtaleSheafPushforwardCompIso B X' X Y g' f (Type (u + 1))).hom ≫
      (eqToIso (congrArg
        (fun k : X' ⟶ Y => B.smallPushforward k (Type (u + 1))) h)).hom ≫
      (smallEtaleSheafPushforwardCompIso B X' Y' Y f' g (Type (u + 1))).inv)

end CartesianLifts

section Conservativity

variable (X : Scheme.{u}) (hX : B.Contains X)
variable {F G : Sheaf (SmallEtale.topology B X hX) (Type (u + 1))}

/-- Local surjectivity of a morphism of sheaves of sets from surjectivity on all stalks at
geometric points. -/
public theorem isLocallySurjective_of_surjective_etaleStalkMap_type (α : F ⟶ G)
    (h : ∀ s : GeometricPoint X, Function.Surjective
      ((etaleStalkPresheafFunctor B X hX s (Type (u + 1))).map α.hom)) :
    Presheaf.IsLocallySurjective (SmallEtale.topology B X hX) α.hom := by
  constructor
  intro V b
  apply SmallEtale.mem_topology_of_jointlySurjective
  intro x
  let s := geometricPointOfEtalePoint B X hX V x
  let Φ := geometricPointSitePoint B X hX s
  let p : Φ.fiber.obj V := geometricPointOfEtalePointLift B X hX V x
  obtain ⟨z, hz⟩ := h s (Φ.toPresheafFiber V p G.obj b)
  obtain ⟨W, y, c, rfl⟩ := Φ.toPresheafFiber_jointly_surjective (P := F.obj) z
  replace hz : (Φ.presheafFiber.map α.hom) (Φ.toPresheafFiber W y F.obj c) =
      Φ.toPresheafFiber V p G.obj b := hz
  rw [Φ.toPresheafFiber_naturality_apply α.hom] at hz
  let ZW : Φ.fiber.Elements := ⟨y⟩
  let ZV : Φ.fiber.Elements := ⟨p⟩
  let Z : Φ.fiber.Elements := IsCofiltered.min ZW ZV
  let l : Z ⟶ ZW := IsCofiltered.minToLeft ZW ZV
  let r : Z ⟶ ZV := IsCofiltered.minToRight ZW ZV
  have hl : Φ.toPresheafFiber Z.1 Z.2 G.obj (G.obj.map l.1.op (α.hom.app (op W) c)) =
      Φ.toPresheafFiber W y G.obj (α.hom.app (op W) c) := by
    have := ConcreteCategory.congr_hom (Φ.toPresheafFiber_w l.1 Z.2 G.obj)
      (α.hom.app (op W) c)
    rw [l.2] at this
    exact this
  have hr : Φ.toPresheafFiber Z.1 Z.2 G.obj (G.obj.map r.1.op b) =
      Φ.toPresheafFiber V p G.obj b := by
    have := ConcreteCategory.congr_hom (Φ.toPresheafFiber_w r.1 Z.2 G.obj) b
    rw [r.2] at this
    exact this
  obtain ⟨Y, k, y', hy', heq⟩ :=
    (Φ.toPresheafFiber_eq_iff' (P := G.obj) Z.1 Z.2 (G.obj.map l.1.op (α.hom.app (op W) c))
      (G.obj.map r.1.op b)).1 (hl.trans (hz.trans hr.symm))
  refine ⟨Y, k ≫ r.1, ⟨F.obj.map (k ≫ l.1).op c, ?_⟩, ?_⟩
  · rw [NatTrans.naturality_apply, op_comp, op_comp, G.obj.map_comp, G.obj.map_comp,
      types_comp_apply, types_comp_apply]
    exact heq
  · have h1 : y'.1 ≫ (SmallEtale.toScheme B X hX).map k = Z.2.1 := congrArg Subtype.val hy'
    have h2 : Z.2.1 ≫ (SmallEtale.toScheme B X hX).map r.1 = p.1 := congrArg Subtype.val r.2
    refine ⟨y'.1 default, ?_⟩
    have hfac : y'.1 ≫ (SmallEtale.toScheme B X hX).map (k ≫ r.1) = p.1 := by
      rw [Functor.map_comp, ← Category.assoc, h1, h2]
    rw [← geometricPointOfEtalePointLift_base B X hX V x, ← hfac]
    rfl

/-- Local injectivity of a morphism of sheaves of sets from injectivity on all stalks at
geometric points. -/
public theorem isLocallyInjective_of_injective_etaleStalkMap_type (α : F ⟶ G)
    (h : ∀ s : GeometricPoint X, Function.Injective
      ((etaleStalkPresheafFunctor B X hX s (Type (u + 1))).map α.hom)) :
    Presheaf.IsLocallyInjective (SmallEtale.topology B X hX) α.hom := by
  constructor
  intro V a₁ a₂ ha
  obtain ⟨V⟩ := V
  apply SmallEtale.mem_topology_of_jointlySurjective
  intro x
  let s := geometricPointOfEtalePoint B X hX V x
  let Φ := geometricPointSitePoint B X hX s
  let p : Φ.fiber.obj V := geometricPointOfEtalePointLift B X hX V x
  have hgerm : Φ.toPresheafFiber V p F.obj a₁ = Φ.toPresheafFiber V p F.obj a₂ := by
    apply h s
    show (Φ.presheafFiber.map α.hom) (Φ.toPresheafFiber V p F.obj a₁) =
      (Φ.presheafFiber.map α.hom) (Φ.toPresheafFiber V p F.obj a₂)
    rw [Φ.toPresheafFiber_naturality_apply α.hom, Φ.toPresheafFiber_naturality_apply α.hom]
    exact congrArg (Φ.toPresheafFiber V p G.obj) ha
  obtain ⟨Y, k, y', hy', heq⟩ := (Φ.toPresheafFiber_eq_iff' (P := F.obj) V p a₁ a₂).1 hgerm
  refine ⟨Y, k, heq, ⟨y'.1 default, ?_⟩⟩
  have h1 : y'.1 ≫ (SmallEtale.toScheme B X hX).map k = p.1 := congrArg Subtype.val hy'
  rw [← geometricPointOfEtalePointLift_base B X hX V x, ← h1]
  rfl

/-- A morphism of sheaves of sets on the small étale site of `X` which is bijective on the stalk
at every geometric point of `X` is an isomorphism. -/
@[stacks 03PU "sheaves of sets, the isomorphism case"]
public theorem isIso_of_bijective_etaleStalkMap (α : F ⟶ G)
    (h : ∀ s : GeometricPoint X, Function.Bijective
      ((etaleStalkFunctor.{u, u + 1} B X hX s).map α)) :
    IsIso α :=
  (Sheaf.isLocallyBijective_iff_isIso α).1
    ⟨isLocallyInjective_of_injective_etaleStalkMap_type B X hX α fun s ↦ (h s).1,
      isLocallySurjective_of_surjective_etaleStalkMap_type B X hX α fun s ↦ (h s).2⟩

end Conservativity

section UnitComponent

variable {S T : B.Scheme} (k : T ⟶ S)

/-- The canonical map from the stalk of a direct image to the stalk at a point of the source,
evaluated on the unit of inverse and direct image, is the stalk comparison of the inverse image:
for a geometric point `x` of `T` and a sheaf `A` on the small étale site of `S`, the germ at
`x ∘ k` of a section of `A`, pushed into `k_* k⁻¹ A` and then read at `x`, is its germ in the
stalk of `k⁻¹ A`. -/
public theorem pushforwardEtaleStalkComponent_unit (x : GeometricPoint T.1)
    (A : Sheaf (SmallEtale.topology B S.1 S.property) (Type (u + 1)))
    (z : etaleStalk B S.1 S.property (x.map (B.inclusion.map k)) A.obj) :
    pushforwardEtaleStalkComponent B k x (x.map (B.inclusion.map k)) rfl
        ((B.smallInverseImage k (Type (u + 1))).obj A)
        ((etaleStalkFunctor.{u, u + 1} B S.1 S.property (x.map (B.inclusion.map k))).map
          ((B.smallPullbackAdjunction k (Type (u + 1))).unit.app A) z) =
      (smallEtalePullbackStalkIso B k x).inv.app A z := by
  let adj := B.smallPullbackAdjunction k (Type (u + 1))
  let L := B.smallInverseImage k (Type (u + 1))
  let R := B.smallPushforward k (Type (u + 1))
  let SS := etaleStalkFunctor.{u, u + 1} B S.1 S.property (x.map (B.inclusion.map k))
  let ST := etaleStalkFunctor.{u, u + 1} B T.1 T.property x
  let iso := smallEtalePullbackStalkIso B k x
  have key : SS.map (adj.unit.app A) ≫ iso.inv.app (R.obj (L.obj A)) ≫
      ST.map (adj.counit.app (L.obj A)) = iso.inv.app A := by
    have hnat : SS.map (adj.unit.app A) ≫ iso.inv.app (R.obj (L.obj A)) =
        iso.inv.app A ≫ ST.map (L.map (adj.unit.app A)) :=
      iso.inv.naturality (adj.unit.app A)
    rw [← Category.assoc, hnat, Category.assoc, ← Functor.map_comp,
      adj.left_triangle_components, ST.map_id]
    exact Category.comp_id _
  exact congrArg (fun m => m z) key

end UnitComponent

section StalkBaseChange

variable {X' X Y' Y : B.Scheme} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- For a cartesian square with `f` finite and a geometric point `y` of `Y'`, the bijection
between the stalk of `f'_* (g')⁻¹ F` at `y` and the stalk of `g⁻¹ f_* F` at `y`, through the
products of the stalks of `F` over the lifts of `y` through `f'` and over the lifts of `g ∘ y`
through `f`, the two sets of lifts being matched by composition with `g'`. -/
public def finiteBaseChangeStalkEquiv
    (sq : IsPullback (B.inclusion.map g') (B.inclusion.map f') (B.inclusion.map f)
      (B.inclusion.map g))
    [IsFinite (B.inclusion.map f)] (y : GeometricPoint Y'.1)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1))) :
    etaleStalk B Y'.1 Y'.property y
        (((B.smallPushforward f' (Type (u + 1))).obj
          ((B.smallInverseImage g' (Type (u + 1))).obj F)).obj) ≃
      etaleStalk B Y'.1 Y'.property y
        (((B.smallInverseImage g (Type (u + 1))).obj
          ((B.smallPushforward f (Type (u + 1))).obj F)).obj) :=
  haveI : IsFinite (B.inclusion.map f') := MorphismProperty.of_isPullback sq inferInstance
  (finitePushforwardStalkEquiv B f' y ((B.smallInverseImage g' (Type (u + 1))).obj F)).trans
    (((Equiv.piCongr (cartesianLiftEquiv B g' f' f g sq y) fun p =>
      ((smallEtalePullbackStalkIso B g'
        (geometricPointLift (B.inclusion.map f') y p)).app F).toEquiv).trans
      (finitePushforwardStalkEquiv B f (y.map (B.inclusion.map g)) F).symm).trans
      ((smallEtalePullbackStalkIso B g y).app
        ((B.smallPushforward f (Type (u + 1))).obj F)).toEquiv.symm)

/-- For a cartesian square with `f` finite, the canonical comparison `g⁻¹ f_* F ⟶ f'_* (g')⁻¹ F`
is an isomorphism as soon as its map on the stalk at every geometric point of `Y'` is the
bijection `AlgebraicGeometry.finiteBaseChangeStalkEquiv`. -/
public theorem isIso_smallEtaleBaseChangeNatTrans_of_stalkMap_eq
    (sq : IsPullback (B.inclusion.map g') (B.inclusion.map f') (B.inclusion.map f)
      (B.inclusion.map g))
    [IsFinite (B.inclusion.map f)]
    (h : g' ≫ f = f' ≫ g)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1)))
    (hstalk : ∀ (y : GeometricPoint Y'.1)
      (z : etaleStalk B Y'.1 Y'.property y
        (((B.smallInverseImage g (Type (u + 1))).obj
          ((B.smallPushforward f (Type (u + 1))).obj F)).obj)),
      (etaleStalkFunctor.{u, u + 1} B Y'.1 Y'.property y).map
          ((smallEtaleBaseChangeNatTrans B g' f' f g h).app F) z =
        (finiteBaseChangeStalkEquiv B g' f' f g sq y F).symm z) :
    IsIso ((smallEtaleBaseChangeNatTrans B g' f' f g h).app F) :=
  isIso_of_bijective_etaleStalkMap B Y'.1 Y'.property _ fun y => by
    have hb := (finiteBaseChangeStalkEquiv B g' f' f g sq y F).symm.bijective
    refine ⟨fun a b hab => hb.1 ?_, fun c => ?_⟩
    · exact ((hstalk y a).symm.trans hab).trans (hstalk y b)
    · obtain ⟨a, ha⟩ := hb.2 c
      exact ⟨a, (hstalk y a).trans ha⟩

end StalkBaseChange

/-- If composing a geometric point `x` of `X` with `f : X ⟶ Y` gives the geometric point `y`,
then `f` carries the morphism of `x` to that of `y`, along the identification of their
sources. -/
theorem GeometricPoint.hom_comp_of_map_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : GeometricPoint X) (y : GeometricPoint Y) (h : x.map f = y) :
    x.hom ≫ f = eqToHom (congrArg (fun q : GeometricPoint Y => q.source) h) ≫ y.hom := by
  subst h; simp

/-- Composing a geometric point with a composite of morphisms is composing it with the two
morphisms in turn. -/
theorem GeometricPoint.map_comp {X Y Z : Scheme.{u}} (x : GeometricPoint X) (a : X ⟶ Y)
    (b : Y ⟶ Z) : x.map (a ≫ b) = (x.map a).map b :=
  congrArg (fun hh : x.source ⟶ Z => (⟨x.residueField, hh⟩ : GeometricPoint Z))
    (Category.assoc x.hom a b).symm

/-- Equal morphisms of sheaves induce the same map on the étale stalk at a geometric point. -/
theorem etaleStalkFunctor_map_congr (B : BigEtaleSite.{u}) (S : B.Scheme)
    (s : GeometricPoint S.1)
    {P Q : Sheaf (SmallEtale.topology B S.1 S.property) (Type (u + 1))} {a b : P ⟶ Q}
    (hab : a = b) (ζ : (etaleStalkFunctor.{u, u + 1} B S.1 S.property s).obj P) :
    (etaleStalkFunctor.{u, u + 1} B S.1 S.property s).map a ζ =
      (etaleStalkFunctor.{u, u + 1} B S.1 S.property s).map b ζ :=
  congrArg (fun m => (etaleStalkFunctor.{u, u + 1} B S.1 S.property s).map m ζ) hab

/-- The map on étale stalks induced by a composite of morphisms of sheaves is the composite of
the induced maps. -/
theorem etaleStalkFunctor_map_comp_apply (B : BigEtaleSite.{u}) (S : B.Scheme)
    (s : GeometricPoint S.1)
    {P Q R : Sheaf (SmallEtale.topology B S.1 S.property) (Type (u + 1))}
    (a : P ⟶ Q) (b : Q ⟶ R)
    (ζ : (etaleStalkFunctor.{u, u + 1} B S.1 S.property s).obj P) :
    (etaleStalkFunctor.{u, u + 1} B S.1 S.property s).map (a ≫ b) ζ =
      (etaleStalkFunctor.{u, u + 1} B S.1 S.property s).map b
        ((etaleStalkFunctor.{u, u + 1} B S.1 S.property s).map a ζ) :=
  ConcreteCategory.congr_hom
    ((etaleStalkFunctor.{u, u + 1} B S.1 S.property s).map_comp a b) ζ

section BaseChangeNeighborhood

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) {x : GeometricPoint X.1}
  {y : GeometricPoint Y.1} (h : x.map (B.inclusion.map f) = y)
  (V : SmallEtale B Y.1 Y.property) (v : (geometricPointFiber B Y.1 Y.property y).obj V)

/-- The base change along `f : X ⟶ Y` of an object `V` of the small étale site of `Y` is a
fibre product of schemes: its two projections form a pullback square over the structure
morphism of `V` and over `f`. -/
theorem isPullback_smallEtaleBaseChange_inclusion :
    IsPullback (B.inclusion.map (pullback.fst V.obj.hom f))
      (B.inclusion.map (pullback.snd V.obj.hom f)) (B.inclusion.map V.obj.hom)
      (B.inclusion.map f) :=
  let := hasPullbacks_bigEtaleSite B
  let := preservesPullbacks_bigEtaleSiteInclusion B
  (IsPullback.of_hasPullback V.obj.hom f).map B.inclusion

/-- The canonical lift of a geometric point `x` of `X` lying over a geometric point `y` of `Y`
to the base change `V ×_Y X` of a pointed étale neighborhood `V` of `y`, obtained from the
universal property of the fibre product. -/
def baseChangeEtalePointHom : x.source ⟶
    (SmallEtale.toScheme B X.1 X.property).obj ((smallEtaleBaseChange B f).obj V) :=
  (isPullback_smallEtaleBaseChange_inclusion B f V).lift
    (eqToHom (congrArg (fun q : GeometricPoint Y.1 => q.source) h) ≫ v.1) x.hom (by
      rw [Category.assoc, v.2]
      exact (GeometricPoint.hom_comp_of_map_eq (B.inclusion.map f) x y h).symm)

/-- The canonical lift to `V ×_Y X` projects to the chosen lift of `y` in `V`. -/
theorem baseChangeEtalePointHom_fst :
    baseChangeEtalePointHom B f h V v ≫ B.inclusion.map (pullback.fst V.obj.hom f) =
      eqToHom (congrArg (fun q : GeometricPoint Y.1 => q.source) h) ≫ v.1 :=
  (isPullback_smallEtaleBaseChange_inclusion B f V).lift_fst _ _ _

/-- The canonical lift to `V ×_Y X` lies over `x`. -/
theorem baseChangeEtalePointHom_snd :
    baseChangeEtalePointHom B f h V v ≫ B.inclusion.map (pullback.snd V.obj.hom f) = x.hom :=
  (isPullback_smallEtaleBaseChange_inclusion B f V).lift_snd _ _ _

/-- The base change `V ×_Y X` of a pointed étale neighborhood of `y`, pointed by the canonical
lift of a geometric point `x` of `X` lying over `y`: an étale neighborhood of `x`. -/
def baseChangeEtalePoint :
    (geometricPointFiber B X.1 X.property x).obj ((smallEtaleBaseChange B f).obj V) :=
  ⟨baseChangeEtalePointHom B f h V v, baseChangeEtalePointHom_snd B f h V v⟩

/-- The germ at `y` of a section of `f_* F` over an étale neighborhood `V` of `y` is sent to the
germ at `x` of the same section, read over the pointed étale neighborhood `V ×_Y X` of `x`. -/
theorem pushforwardEtaleStalkComponent_germ_baseChange
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1)))
    (σ : F.obj.obj (op ((smallEtaleBaseChange B f).obj V))) :
    pushforwardEtaleStalkComponent B f x y h F
        (colimit.ι ((Functor.Elements.π (geometricPointFiber B Y.1 Y.property y)).op ⋙
          ((B.smallPushforward f (Type (u + 1))).obj F).obj) (op ⟨v⟩) σ) =
      colimit.ι ((Functor.Elements.π (geometricPointFiber B X.1 X.property x)).op ⋙ F.obj)
        (op ⟨baseChangeEtalePoint B f h V v⟩) σ := by
  have ht : (baseChangeEtalePoint B f h V v).1 ≫
      (SmallEtale.toScheme B X.1 X.property).map (𝟙 ((smallEtaleBaseChange B f).obj V)) ≫
        B.inclusion.map (pullback.fst V.obj.hom f) =
      eqToHom (congrArg (fun q : GeometricPoint Y.1 => q.source) h) ≫ v.1 := by
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
    exact baseChangeEtalePointHom_fst B f h V v
  refine (pushforwardEtaleStalkComponent_germ B f x y h F ⟨v⟩
    ⟨baseChangeEtalePoint B f h V v⟩ (𝟙 _) ht σ).trans ?_
  exact congrArg (fun z => colimit.ι
      ((Functor.Elements.π (geometricPointFiber B X.1 X.property x)).op ⋙ F.obj)
      (op ⟨baseChangeEtalePoint B f h V v⟩) z)
    (ConcreteCategory.congr_hom (F.obj.map_id (op ((smallEtaleBaseChange B f).obj V))) σ)

end BaseChangeNeighborhood

section Composite

variable (B : BigEtaleSite.{u}) {W T S : B.Scheme} (k : W ⟶ T) (l : T ⟶ S)

/-- The comparison of a two-step base change with the base change along the composite carries
the projection `V ×_S W ⟶ V` to the composite of the projections
`(V ×_S T) ×_T W ⟶ V ×_S T ⟶ V`. -/
theorem smallEtaleBaseChange_compIso_toScheme_fst (V : SmallEtale B S.1 S.property) :
    (SmallEtale.toScheme B W.1 W.property).map
        ((smallEtaleBaseChange_compIso B W T S k l).val.hom.app V) ≫
      B.inclusion.map (pullback.fst V.obj.hom (k ≫ l)) =
      B.inclusion.map (pullback.fst ((smallEtaleBaseChange B l).obj V).obj.hom k) ≫
        B.inclusion.map (pullback.fst V.obj.hom l) := by
  have hl : ((smallEtaleBaseChange_compIso B W T S k l).val.hom.app V).hom.left =
      ((Over.pullbackComp k l).inv.app V.obj).left :=
    congrArg Over.Hom.left (smallEtaleBaseChange_compIso_app B W T S k l V)
  have hbase : ((smallEtaleBaseChange_compIso B W T S k l).val.hom.app V).hom.left ≫
      pullback.fst V.obj.hom (k ≫ l) =
      pullback.fst ((smallEtaleBaseChange B l).obj V).obj.hom k ≫
        pullback.fst V.obj.hom l := by
    rw [hl]
    exact Over.pullbackComp_inv_app_left_fst k l V.obj
  exact ((B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map hbase)).trans
    (B.inclusion.map_comp _ _)

variable {w : GeometricPoint W.1} {t : GeometricPoint T.1} {s : GeometricPoint S.1}
  (hk : w.map (B.inclusion.map k) = t) (hl : t.map (B.inclusion.map l) = s)
  (hm : w.map (B.inclusion.map (k ≫ l)) = s)
  (V : SmallEtale B S.1 S.property) (v : (geometricPointFiber B S.1 S.property s).obj V)

/-- The comparison of a two-step base change with the base change along the composite matches
the canonical lifts of a geometric point: it carries the lift of `w` to `(V ×_S T) ×_T W` to the
lift of `w` to `V ×_S W`. -/
theorem baseChangeEtalePoint_comp :
    (geometricPointFiber B W.1 W.property w).map
        ((smallEtaleBaseChange_compIso B W T S k l).val.hom.app V)
        (baseChangeEtalePoint B k hk ((smallEtaleBaseChange B l).obj V)
          (baseChangeEtalePoint B l hl V v)) =
      baseChangeEtalePoint B (k ≫ l) hm V v := by
  set m := (smallEtaleBaseChange_compIso B W T S k l).val.hom.app V with hmdef
  set p := baseChangeEtalePointHom B k hk ((smallEtaleBaseChange B l).obj V)
    (baseChangeEtalePoint B l hl V v) with hpdef
  set q := baseChangeEtalePointHom B l hl V v with hqdef
  set hk' := congrArg (fun r : GeometricPoint T.1 => r.source) hk with hk'def
  set hl' := congrArg (fun r : GeometricPoint S.1 => r.source) hl with hl'def
  set hm' := congrArg (fun r : GeometricPoint S.1 => r.source) hm with hm'def
  apply Subtype.ext
  refine (isPullback_smallEtaleBaseChange_inclusion B (k ≫ l) V).hom_ext ?_ ?_
  · show (p ≫ (SmallEtale.toScheme B W.1 W.property).map m) ≫
      B.inclusion.map (pullback.fst V.obj.hom (k ≫ l)) =
      baseChangeEtalePointHom B (k ≫ l) hm V v ≫
        B.inclusion.map (pullback.fst V.obj.hom (k ≫ l))
    have s1 : (p ≫ (SmallEtale.toScheme B W.1 W.property).map m) ≫
        B.inclusion.map (pullback.fst V.obj.hom (k ≫ l)) =
        p ≫ B.inclusion.map (pullback.fst ((smallEtaleBaseChange B l).obj V).obj.hom k) ≫
          B.inclusion.map (pullback.fst V.obj.hom l) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun z => p ≫ z) (smallEtaleBaseChange_compIso_toScheme_fst B k l V))
    have s2 : p ≫ B.inclusion.map (pullback.fst ((smallEtaleBaseChange B l).obj V).obj.hom k) ≫
          B.inclusion.map (pullback.fst V.obj.hom l) =
        (eqToHom hk' ≫ q) ≫ B.inclusion.map (pullback.fst V.obj.hom l) :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun z => z ≫ B.inclusion.map (pullback.fst V.obj.hom l))
          (baseChangeEtalePointHom_fst B k hk ((smallEtaleBaseChange B l).obj V)
            (baseChangeEtalePoint B l hl V v)))
    have s3 : (eqToHom hk' ≫ q) ≫ B.inclusion.map (pullback.fst V.obj.hom l) =
        (eqToHom hk' ≫ eqToHom hl') ≫ v.1 :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun z => eqToHom hk' ≫ z) (baseChangeEtalePointHom_fst B l hl V v)).trans
          (Category.assoc _ _ _).symm)
    have s4 : (eqToHom hk' ≫ eqToHom hl') ≫ v.1 = eqToHom hm' ≫ v.1 :=
      congrArg (fun z => z ≫ v.1) (eqToHom_trans hk' hl')
    exact ((s1.trans s2).trans (s3.trans s4)).trans
      (baseChangeEtalePointHom_fst B (k ≫ l) hm V v).symm
  · show (p ≫ (SmallEtale.toScheme B W.1 W.property).map m) ≫
      B.inclusion.map (pullback.snd V.obj.hom (k ≫ l)) =
      baseChangeEtalePointHom B (k ≫ l) hm V v ≫
        B.inclusion.map (pullback.snd V.obj.hom (k ≫ l))
    have s1 : (p ≫ (SmallEtale.toScheme B W.1 W.property).map m) ≫
        B.inclusion.map (pullback.snd V.obj.hom (k ≫ l)) =
        p ≫ B.inclusion.map
          (pullback.snd ((smallEtaleBaseChange B l).obj V).obj.hom k) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun z => p ≫ z) (SmallEtale.toScheme_map_comp B W.1 W.property m))
    exact (s1.trans (baseChangeEtalePointHom_snd B k hk ((smallEtaleBaseChange B l).obj V)
      (baseChangeEtalePoint B l hl V v))).trans
        (baseChangeEtalePointHom_snd B (k ≫ l) hm V v).symm

/-- Let `k : W ⟶ T` and `l : T ⟶ S`, and let `w`, `t`, `s` be geometric points of `W`, `T`, `S`
with `w` over `t` and `t` over `s`. For a sheaf `F` on the small étale site of `W`, the canonical
map from the stalk of `(k ≫ l)_* F` at `s` to the stalk of `F` at `w` is the map for `l` at the
sheaf `k_* F`, followed by the map for `k`, after the identification
`(k ≫ l)_* F = l_* k_* F`. -/
theorem pushforwardEtaleStalkComponent_comp
    (F : Sheaf (SmallEtale.topology B W.1 W.property) (Type (u + 1)))
    (z : etaleStalk B S.1 S.property s
      (((B.smallPushforward (k ≫ l) (Type (u + 1))).obj F).obj)) :
    pushforwardEtaleStalkComponent B (k ≫ l) w s hm F z =
      pushforwardEtaleStalkComponent B k w t hk F
        (pushforwardEtaleStalkComponent B l t s hl
            ((B.smallPushforward k (Type (u + 1))).obj F)
          ((etaleStalkFunctor.{u, u + 1} B S.1 S.property s).map
            ((smallEtaleSheafPushforwardCompIso B W T S k l (Type (u + 1))).inv.app F) z)) := by
  obtain ⟨V, v, σ, hz⟩ :=
    (geometricPointSitePoint B S.1 S.property s).toPresheafFiber_jointly_surjective
      (P := ((B.smallPushforward (k ≫ l) (Type (u + 1))).obj F).obj) z
  have hz' : colimit.ι ((Functor.Elements.π (geometricPointFiber B S.1 S.property s)).op ⋙
      ((B.smallPushforward (k ≫ l) (Type (u + 1))).obj F).obj) (op ⟨v⟩) σ = z := hz
  subst hz'
  have hR1 : (etaleStalkFunctor.{u, u + 1} B S.1 S.property s).map
        ((smallEtaleSheafPushforwardCompIso B W T S k l (Type (u + 1))).inv.app F)
        (colimit.ι ((Functor.Elements.π (geometricPointFiber B S.1 S.property s)).op ⋙
          ((B.smallPushforward (k ≫ l) (Type (u + 1))).obj F).obj) (op ⟨v⟩) σ) =
      colimit.ι ((Functor.Elements.π (geometricPointFiber B S.1 S.property s)).op ⋙
        ((B.smallPushforward l (Type (u + 1))).obj
          ((B.smallPushforward k (Type (u + 1))).obj F)).obj) (op ⟨v⟩)
        (F.obj.map ((smallEtaleBaseChange_compIso B W T S k l).val.hom.app V).op σ) :=
    (geometricPointSitePoint B S.1 S.property s).toPresheafFiber_naturality_apply
      ((smallEtaleSheafPushforwardCompIso B W T S k l (Type (u + 1))).inv.app F).hom V v σ
  have c1 := congrArg (fun a => pushforwardEtaleStalkComponent B k w t hk F
    (pushforwardEtaleStalkComponent B l t s hl
      ((B.smallPushforward k (Type (u + 1))).obj F) a)) hR1
  have c2 := congrArg (pushforwardEtaleStalkComponent B k w t hk F)
    (pushforwardEtaleStalkComponent_germ_baseChange B l hl V v
      ((B.smallPushforward k (Type (u + 1))).obj F)
      (F.obj.map ((smallEtaleBaseChange_compIso B W T S k l).val.hom.app V).op σ))
  have c3 := pushforwardEtaleStalkComponent_germ_baseChange B k hk
    ((smallEtaleBaseChange B l).obj V) (baseChangeEtalePoint B l hl V v) F
    (F.obj.map ((smallEtaleBaseChange_compIso B W T S k l).val.hom.app V).op σ)
  have c4 := (geometricPointSitePoint B W.1 W.property w).toPresheafFiber_w_apply
    ((smallEtaleBaseChange_compIso B W T S k l).val.hom.app V)
    (baseChangeEtalePoint B k hk ((smallEtaleBaseChange B l).obj V)
      (baseChangeEtalePoint B l hl V v)) F.obj σ
  have c5 := congrArg (fun pt => colimit.ι
      ((Functor.Elements.π (geometricPointFiber B W.1 W.property w)).op ⋙ F.obj)
      (op ⟨pt⟩) σ)
    (baseChangeEtalePoint_comp B k l hk hl hm V v)
  exact (pushforwardEtaleStalkComponent_germ_baseChange B (k ≫ l) hm V v F σ).trans
    (((c1.trans c2).trans (c3.trans (c4.trans c5))).symm)

end Composite

section BaseChange

variable (B : BigEtaleSite.{u}) {X' X Y' Y : B.Scheme} (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- The canonical stalk map of a direct image is compatible with transporting the sheaf along an
equality of morphisms. -/
theorem pushforwardEtaleStalkComponent_eqToHom {Z W : B.Scheme} (k k' : Z ⟶ W) (hkk' : k = k')
    (x : GeometricPoint Z.1) (y : GeometricPoint W.1)
    (hc : x.map (B.inclusion.map k) = y) (hc' : x.map (B.inclusion.map k') = y)
    (F : Sheaf (SmallEtale.topology B Z.1 Z.property) (Type (u + 1)))
    (z : etaleStalk B W.1 W.property y (((B.smallPushforward k (Type (u + 1))).obj F).obj)) :
    pushforwardEtaleStalkComponent B k' x y hc' F
        ((etaleStalkFunctor.{u, u + 1} B W.1 W.property y).map
          ((eqToIso (congrArg
            (fun m : Z ⟶ W => B.smallPushforward m (Type (u + 1))) hkk')).hom.app F) z) =
      pushforwardEtaleStalkComponent B k x y hc F z := by
  subst hkk'
  refine congrArg (pushforwardEtaleStalkComponent B k x y hc' F) ?_
  simp
  rfl

/-- The identification `g'_* f_* ⟶ f'_* g_*` of the two composite direct images around a
commuting square `g' ≫ f = f' ≫ g` of a big étale site, through the direct image along the
common composite. -/
def smallEtaleBaseChangeMate (h : g' ≫ f = f' ≫ g) :
    B.smallPushforward g' (Type (u + 1)) ⋙ B.smallPushforward f (Type (u + 1)) ⟶
      B.smallPushforward f' (Type (u + 1)) ⋙ B.smallPushforward g (Type (u + 1)) :=
  (smallEtaleSheafPushforwardCompIso B X' X Y g' f (Type (u + 1))).hom ≫
    (eqToIso (congrArg
      (fun k : X' ⟶ Y => B.smallPushforward k (Type (u + 1))) h)).hom ≫
    (smallEtaleSheafPushforwardCompIso B X' Y' Y f' g (Type (u + 1))).inv

/-- The identification of the two composite direct images is the composite of the two
comparisons of iterated direct images with the transport along the equality of the two
composites. -/
theorem smallEtaleBaseChangeMate_eq (h : g' ≫ f = f' ≫ g) :
    smallEtaleBaseChangeMate B g' f' f g h =
      (smallEtaleSheafPushforwardCompIso B X' X Y g' f (Type (u + 1))).hom ≫
        ((eqToIso (congrArg
            (fun k : X' ⟶ Y => B.smallPushforward k (Type (u + 1))) h)).hom ≫
          (smallEtaleSheafPushforwardCompIso B X' Y' Y f' g (Type (u + 1))).inv) := rfl

/-- The identification of the two composite direct images, evaluated at a sheaf. -/
theorem smallEtaleBaseChangeMate_app (h : g' ≫ f = f' ≫ g)
    (A : Sheaf (SmallEtale.topology B X'.1 X'.property) (Type (u + 1))) :
    (smallEtaleBaseChangeMate B g' f' f g h).app A =
      (smallEtaleSheafPushforwardCompIso B X' X Y g' f (Type (u + 1))).hom.app A ≫
        ((eqToIso (congrArg
            (fun k : X' ⟶ Y => B.smallPushforward k (Type (u + 1))) h)).hom.app A ≫
          (smallEtaleSheafPushforwardCompIso B X' Y' Y f' g (Type (u + 1))).inv.app A) :=
  (congrArg (fun α : B.smallPushforward g' (Type (u + 1)) ⋙
      B.smallPushforward f (Type (u + 1)) ⟶ B.smallPushforward f' (Type (u + 1)) ⋙
        B.smallPushforward g (Type (u + 1)) => α.app A)
    (smallEtaleBaseChangeMate_eq B g' f' f g h)).trans
    ((NatTrans.comp_app
        (smallEtaleSheafPushforwardCompIso B X' X Y g' f (Type (u + 1))).hom
        ((eqToIso (congrArg
            (fun k : X' ⟶ Y => B.smallPushforward k (Type (u + 1))) h)).hom ≫
          (smallEtaleSheafPushforwardCompIso B X' Y' Y f' g (Type (u + 1))).inv) A).trans
      (congrArg (fun z =>
          (smallEtaleSheafPushforwardCompIso B X' X Y g' f (Type (u + 1))).hom.app A ≫ z)
        (NatTrans.comp_app
          (eqToIso (congrArg
            (fun k : X' ⟶ Y => B.smallPushforward k (Type (u + 1))) h)).hom
          (smallEtaleSheafPushforwardCompIso B X' Y' Y f' g (Type (u + 1))).inv A)))

/-- The canonical base-change comparison `g⁻¹ f_* ⟶ f'_* (g')⁻¹` is the mate of the
identification of the two composite direct images. -/
theorem smallEtaleBaseChangeNatTrans_eq_mateEquiv_symm (h : g' ≫ f = f' ≫ g) :
    smallEtaleBaseChangeNatTrans B g' f' f g h =
      (mateEquiv (B.smallPullbackAdjunction g' (Type (u + 1)))
        (B.smallPullbackAdjunction g (Type (u + 1)))).symm
        (smallEtaleBaseChangeMate B g' f' f g h) := rfl

/-- The adjunction units relate the base-change comparison to the identification of the two
composite direct images: `f_*` of the unit of `g'`, followed by that identification, is the unit
of `g` followed by `g_*` of the comparison. -/
theorem unit_comp_smallEtaleBaseChangeNatTrans (h : g' ≫ f = f' ≫ g)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1))) :
    (B.smallPushforward f (Type (u + 1))).map
          ((B.smallPullbackAdjunction g' (Type (u + 1))).unit.app F) ≫
        (smallEtaleBaseChangeMate B g' f' f g h).app
          ((B.smallInverseImage g' (Type (u + 1))).obj F) =
      (B.smallPullbackAdjunction g (Type (u + 1))).unit.app
          ((B.smallPushforward f (Type (u + 1))).obj F) ≫
        (B.smallPushforward g (Type (u + 1))).map
          (((mateEquiv (B.smallPullbackAdjunction g' (Type (u + 1)))
            (B.smallPullbackAdjunction g (Type (u + 1)))).symm
            (smallEtaleBaseChangeMate B g' f' f g h)).app F) :=
  unit_mateEquiv_symm' (B.smallPullbackAdjunction g' (Type (u + 1)))
    (B.smallPullbackAdjunction g (Type (u + 1))) (smallEtaleBaseChangeMate B g' f' f g h) F

/-- For a cartesian square and a lift `p` of a geometric point `y` of `Y'` through `f'`, the
canonical map at `p` applied to the stalk map of `g⁻¹ f_* F ⟶ f'_* (g')⁻¹ F` is the canonical map
from the stalk of `f_* F` at `g ∘ y` to the stalk of `F` at the corresponding lift `p ∘ g'` of
`g ∘ y`, transported into the stalk of `(g')⁻¹ F` by the stalk comparison of the inverse
image. -/
theorem pushforwardEtaleStalkComponent_smallEtaleBaseChangeNatTrans
    (sq : IsPullback (B.inclusion.map g') (B.inclusion.map f') (B.inclusion.map f)
      (B.inclusion.map g))
    (h : g' ≫ f = f' ≫ g)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1)))
    (y : GeometricPoint Y'.1) (p : {a : y.source ⟶ X'.1 // a ≫ B.inclusion.map f' = y.hom})
    (ζ : etaleStalk B Y.1 Y.property (y.map (B.inclusion.map g))
      (((B.smallPushforward f (Type (u + 1))).obj F).obj)) :
    pushforwardEtaleStalkComponent B f' (geometricPointLift (B.inclusion.map f') y p) y
        (geometricPointLift_map (B.inclusion.map f') y p)
        ((B.smallInverseImage g' (Type (u + 1))).obj F)
        ((etaleStalkFunctor.{u, u + 1} B Y'.1 Y'.property y).map
          ((smallEtaleBaseChangeNatTrans B g' f' f g h).app F)
          ((smallEtalePullbackStalkIso B g y).inv.app
            ((B.smallPushforward f (Type (u + 1))).obj F) ζ)) =
      (smallEtalePullbackStalkIso B g'
          (geometricPointLift (B.inclusion.map f') y p)).inv.app F
        (pushforwardEtaleStalkComponent B f
          (geometricPointLift (B.inclusion.map f) (y.map (B.inclusion.map g))
            (cartesianLiftEquiv B g' f' f g sq y p))
          (y.map (B.inclusion.map g))
          (geometricPointLift_map (B.inclusion.map f) (y.map (B.inclusion.map g))
            (cartesianLiftEquiv B g' f' f g sq y p)) F ζ) := by
  have hp := geometricPointLift_map (B.inclusion.map f') y p
  have hl1 : (geometricPointLift (B.inclusion.map f) (y.map (B.inclusion.map g)) (cartesianLiftEquiv
      B g' f' f g sq y p)).map (B.inclusion.map f) = (y.map (B.inclusion.map g)) :=
    geometricPointLift_map (B.inclusion.map f) (y.map (B.inclusion.map g)) (cartesianLiftEquiv B g'
        f' f g sq y p)
  have hk1 : (geometricPointLift (B.inclusion.map f') y p).map (B.inclusion.map g') =
      (geometricPointLift (B.inclusion.map f) (y.map (B.inclusion.map g)) (cartesianLiftEquiv B g'
      f' f g sq y p)) := rfl
  have hm1 : (geometricPointLift (B.inclusion.map f') y p).map (B.inclusion.map (g' ≫ f)) = (y.map
      (B.inclusion.map g)) := by
    rw [B.inclusion.map_comp, GeometricPoint.map_comp, hk1, hl1]
  have hm2 : (geometricPointLift (B.inclusion.map f') y p).map (B.inclusion.map (f' ≫ g)) = (y.map
      (B.inclusion.map g)) := by
    rw [B.inclusion.map_comp, GeometricPoint.map_comp, hp]
  have mt := unit_comp_smallEtaleBaseChangeNatTrans B g' f' f g h F
  rw [smallEtaleBaseChangeNatTrans_eq_mateEquiv_symm, ← pushforwardEtaleStalkComponent_unit B g y]
  erw [← pushforwardEtaleStalkComponent_natural B g y _ rfl]
  erw [← etaleStalkFunctor_map_comp_apply, ← mt]
  erw [etaleStalkFunctor_map_comp_apply]
  rw [smallEtaleBaseChangeMate_app, etaleStalkFunctor_map_comp_apply,
    etaleStalkFunctor_map_comp_apply]
  erw [← pushforwardEtaleStalkComponent_comp B f' g hp rfl hm2,
    pushforwardEtaleStalkComponent_eqToHom B (g' ≫ f) (f' ≫ g) h _ _ hm1 hm2,
    pushforwardEtaleStalkComponent_comp B g' f hk1 hl1 hm1,
    ← etaleStalkFunctor_map_comp_apply, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  erw [ConcreteCategory.id_apply, pushforwardEtaleStalkComponent_natural B f _ _ hl1
    ((B.smallPullbackAdjunction g' (Type (u + 1))).unit.app F) ζ]
  exact pushforwardEtaleStalkComponent_unit B g' _ F _

/-- Consider a cartesian square
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
of schemes of a big étale site with `f` finite, and a sheaf of sets `F` on the small étale site
of `X`. Then the canonical comparison `g⁻¹ f_* F ⟶ f'_* (g')⁻¹ F` is an isomorphism. -/
@[stacks 0959]
theorem isIso_smallEtaleBaseChangeNatTrans
    (sq : IsPullback (B.inclusion.map g') (B.inclusion.map f') (B.inclusion.map f)
      (B.inclusion.map g))
    [IsFinite (B.inclusion.map f)] (h : g' ≫ f = f' ≫ g)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1))) :
    IsIso ((smallEtaleBaseChangeNatTrans B g' f' f g h).app F) := by
  have hf' : IsFinite (B.inclusion.map f') := MorphismProperty.of_isPullback sq inferInstance
  refine isIso_smallEtaleBaseChangeNatTrans_of_stalkMap_eq B g' f' f g sq h F fun y z => ?_
  refine (finitePushforwardStalkEquiv B f' y ((B.smallInverseImage g' (Type (u + 1))).obj
      F)).injective ?_
  have h1 : (finitePushforwardStalkEquiv B f' y ((B.smallInverseImage g' (Type (u + 1))).obj F))
        ((finiteBaseChangeStalkEquiv B g' f' f g sq y F).symm z) =
      (Equiv.piCongr (cartesianLiftEquiv B g' f' f g sq y) fun q =>
        ((smallEtalePullbackStalkIso B g'
          (geometricPointLift (B.inclusion.map f') y q)).app F).toEquiv).symm
        ((finitePushforwardStalkEquiv B f (y.map (B.inclusion.map g)) F)
          (((smallEtalePullbackStalkIso B g y).app ((B.smallPushforward f (Type (u + 1))).obj
              F)).toEquiv z)) :=
    Equiv.apply_symm_apply _ _
  rw [h1]
  funext p
  have hz : (smallEtalePullbackStalkIso B g y).inv.app ((B.smallPushforward f (Type (u + 1))).obj F)
      (((smallEtalePullbackStalkIso B g y).app ((B.smallPushforward f (Type (u + 1))).obj
      F)).toEquiv z) = z :=
    Equiv.symm_apply_apply (((smallEtalePullbackStalkIso B g y).app ((B.smallPushforward f (Type (u
        + 1))).obj F)).toEquiv) z
  refine Eq.trans (congrArg (fun ww => finitePushforwardStalkEquiv B f' y ((B.smallInverseImage g'
      (Type (u + 1))).obj F)
    ((etaleStalkFunctor.{u, u + 1} B Y'.1 Y'.property y).map ((smallEtaleBaseChangeNatTrans B g' f'
        f g h).app F) ww) p) hz.symm) ?_
  exact pushforwardEtaleStalkComponent_smallEtaleBaseChangeNatTrans B g' f' f g sq h F y p
    (((smallEtalePullbackStalkIso B g y).app ((B.smallPushforward f (Type (u + 1))).obj F)).toEquiv
        z)

end BaseChange

/-- The stalk at `y` of a morphism `g⁻¹ P ⟶ Q` obtained by adjunction from `ψ : P ⟶ g_* Q` is
the canonical map from the stalk of a direct image, applied after the stalk map of `ψ`. -/
theorem pushforwardEtaleStalkComponent_counit_comp
    (B : BigEtaleSite.{u}) {Y' Y : B.Scheme} (g : Y' ⟶ Y) (y : GeometricPoint Y'.obj)
    {P : Sheaf (SmallEtale.topology B Y.obj Y.property) (Type (u + 1))}
    {Q : Sheaf (SmallEtale.topology B Y'.obj Y'.property) (Type (u + 1))}
    (ψ : P ⟶ (B.smallPushforward g (Type (u + 1))).obj Q)
    (z : etaleStalk B Y.obj Y.property (y.map (B.inclusion.map g)) P.obj) :
    (etaleStalkFunctor.{u, u + 1} B Y'.obj Y'.property y).map
        ((B.smallInverseImage g (Type (u + 1))).map ψ ≫
          (B.smallPullbackAdjunction g (Type (u + 1))).counit.app Q)
        ((smallEtalePullbackStalkIso B g y).inv.app P z) =
      pushforwardEtaleStalkComponent B g y (y.map (B.inclusion.map g)) rfl Q
        ((etaleStalkFunctor.{u, u + 1} B Y.obj Y.property
          (y.map (B.inclusion.map g))).map ψ z) := by
  let Ig := B.smallInverseImage g (Type (u + 1))
  let Pg := B.smallPushforward g (Type (u + 1))
  let adj := B.smallPullbackAdjunction g (Type (u + 1))
  let Sy := etaleStalkFunctor.{u, u + 1} B Y'.obj Y'.property y
  let Sgy := etaleStalkFunctor.{u, u + 1} B Y.obj Y.property (y.map (B.inclusion.map g))
  let iso := smallEtalePullbackStalkIso B g y
  have key : iso.inv.app P ≫ Sy.map (Ig.map ψ ≫ adj.counit.app Q) =
      Sgy.map ψ ≫ iso.inv.app (Pg.obj Q) ≫ Sy.map (adj.counit.app Q) := by
    have hnat : iso.inv.app P ≫ Sy.map (Ig.map ψ) =
        Sgy.map ψ ≫ iso.inv.app (Pg.obj Q) := (iso.inv.naturality ψ).symm
    rw [Sy.map_comp, ← Category.assoc, hnat, Category.assoc]
  exact congrArg (fun k => k z) key

end AlgebraicGeometry

end
