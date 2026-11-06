module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointFiber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.BasicUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sweep.EtaleStalkFunctor
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BoundedCovering
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.MorphismComposition
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverRepresentable
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardBaseChange
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardBaseChange

public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalkUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkIsomorphismCriterion
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality

/-!
# Base change for finite direct images of étale sheaves of sets

For a cartesian square `g' ≫ f = f' ≫ g` of schemes of a big étale site with `f` finite, and a
sheaf of sets `F` with values in `Type (max (u + 1) v)` on the small étale site of the source of
`f`, the canonical comparison `g⁻¹ f_* F ⟶ f'_* (g')⁻¹ F` is an isomorphism. On the way: a
morphism of étale sheaves of sets which is bijective on all stalks at geometric points is an
isomorphism, and the canonical stalk maps of direct images are computed on germs, along
composites and along the base-change comparison.

## Main definitions

* `AlgebraicGeometry.smallEtaleBaseChangeNatTransUniv`: the base-change comparison
  `g⁻¹ f_* ⟶ f'_* (g')⁻¹` attached to a commuting square.
* `AlgebraicGeometry.finiteBaseChangeStalkEquivUniv`: for `f` finite, the bijection between the
  stalks of `f'_* (g')⁻¹ F` and `g⁻¹ f_* F` at a geometric point.

## Main results

* `AlgebraicGeometry.isIso_of_bijective_etaleStalkMap_univ`: a morphism of sheaves of sets on the
  small étale site which is bijective on every stalk at a geometric point is an isomorphism.
* `AlgebraicGeometry.isIso_smallEtaleBaseChangeNatTrans_univ`: for a cartesian square with `f`
  finite, the base-change comparison `g⁻¹ f_* F ⟶ f'_* (g')⁻¹ F` is an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ u v

namespace CategoryTheory

end CategoryTheory

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u})

section CartesianLifts

variable {X' X Y' Y : B.Scheme} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- The canonical base-change comparison `g⁻¹ f_* ⟶ f'_* (g')⁻¹` for sheaves of sets on the
small étale sites attached to a commuting square `g' ≫ f = f' ≫ g` of a big étale site. It is
the mate, along the inverse-image/direct-image adjunctions of `g` and `g'`, of the canonical
identification of the two composite direct images around the square. -/
public def smallEtaleBaseChangeNatTransUniv (h : g' ≫ f = f' ≫ g) :
    B.smallPushforward f (Type (max (u + 1) v)) ⋙ B.smallInverseImage g (Type (max (u + 1) v)) ⟶
      B.smallInverseImage g' (Type (max (u + 1) v)) ⋙
        B.smallPushforward f' (Type (max (u + 1) v)) :=
  (mateEquiv (B.smallPullbackAdjunction g' (Type (max (u + 1) v)))
      (B.smallPullbackAdjunction g (Type (max (u + 1) v)))).symm
    ((smallEtaleSheafPushforwardCompIso B X' X Y g' f (Type (max (u + 1) v))).hom ≫
      (eqToIso (congrArg
        (fun k : X' ⟶ Y => B.smallPushforward k (Type (max (u + 1) v))) h)).hom ≫
      (smallEtaleSheafPushforwardCompIso B X' Y' Y f' g (Type (max (u + 1) v))).inv)

end CartesianLifts

section Conservativity

variable (X : Scheme.{u}) (hX : B.Contains X)
variable {F G : Sheaf (SmallEtale.topology B X hX) (Type (max (u + 1) v))}

/-- Local surjectivity of a morphism of sheaves of sets from surjectivity on all stalks at
geometric points. -/
public theorem isLocallySurjective_of_surjective_etaleStalkMap_type_univ (α : F ⟶ G)
    (h : ∀ s : GeometricPoint X, Function.Surjective
      ((etaleStalkPresheafFunctor B X hX s (Type (max (u + 1) v))).map α.hom)) :
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
  have hl : Φ.toPresheafFiber Z.obj Z.val G.obj (G.obj.map l.hom.op (α.hom.app (op W) c)) =
      Φ.toPresheafFiber W y G.obj (α.hom.app (op W) c) := by
    have := ConcreteCategory.congr_hom (Φ.toPresheafFiber_w l.hom Z.val G.obj)
      (α.hom.app (op W) c)
    rwa [l.map_val] at this
  have hr : Φ.toPresheafFiber Z.obj Z.val G.obj (G.obj.map r.hom.op b) =
      Φ.toPresheafFiber V p G.obj b := by
    have := ConcreteCategory.congr_hom (Φ.toPresheafFiber_w r.hom Z.val G.obj) b
    rwa [r.map_val] at this
  obtain ⟨Y, k, y', hy', heq⟩ :=
    (Φ.toPresheafFiber_eq_iff' (P := G.obj) Z.obj Z.val (G.obj.map l.hom.op (α.hom.app (op W) c))
      (G.obj.map r.hom.op b)).1 (hl.trans (hz.trans hr.symm))
  refine ⟨Y, k ≫ r.hom, ⟨F.obj.map (k ≫ l.hom).op c, ?_⟩, ?_⟩
  · rwa [NatTrans.naturality_apply, op_comp, op_comp, G.obj.map_comp, G.obj.map_comp,
      types_comp_apply, types_comp_apply]
  · have h1 : y'.1 ≫ (SmallEtale.toScheme B X hX).map k = Z.val.1 := congrArg Subtype.val hy'
    have h2 : Z.val.1 ≫ (SmallEtale.toScheme B X hX).map r.hom = p.1 :=
      congrArg Subtype.val r.map_val
    refine ⟨y'.1 default, ?_⟩
    have hfac : y'.1 ≫ (SmallEtale.toScheme B X hX).map (k ≫ r.hom) = p.1 := by
      rw [Functor.map_comp, ← Category.assoc, h1, h2]
    rw [← geometricPointOfEtalePointLift_base B X hX V x, ← hfac]
    rfl

/-- Local injectivity of a morphism of sheaves of sets from injectivity on all stalks at
geometric points. -/
public theorem isLocallyInjective_of_injective_etaleStalkMap_type_univ (α : F ⟶ G)
    (h : ∀ s : GeometricPoint X, Function.Injective
      ((etaleStalkPresheafFunctor B X hX s (Type (max (u + 1) v))).map α.hom)) :
    Presheaf.IsLocallyInjective (SmallEtale.topology B X hX) α.hom := by
  constructor
  rintro ⟨V⟩ a₁ a₂ ha
  apply SmallEtale.mem_topology_of_jointlySurjective
  intro x
  let s := geometricPointOfEtalePoint B X hX V x
  let Φ := geometricPointSitePoint B X hX s
  let p : Φ.fiber.obj V := geometricPointOfEtalePointLift B X hX V x
  have hgerm : Φ.toPresheafFiber V p F.obj a₁ = Φ.toPresheafFiber V p F.obj a₂ := h s <| by
    show (Φ.presheafFiber.map α.hom) (Φ.toPresheafFiber V p F.obj a₁) =
      (Φ.presheafFiber.map α.hom) (Φ.toPresheafFiber V p F.obj a₂)
    rw [Φ.toPresheafFiber_naturality_apply α.hom, Φ.toPresheafFiber_naturality_apply α.hom, ha]
  obtain ⟨Y, k, y', hy', heq⟩ := (Φ.toPresheafFiber_eq_iff' (P := F.obj) V p a₁ a₂).1 hgerm
  refine ⟨Y, k, heq, ⟨y'.1 default, ?_⟩⟩
  have h1 : y'.1 ≫ (SmallEtale.toScheme B X hX).map k = p.1 := congrArg Subtype.val hy'
  rw [← geometricPointOfEtalePointLift_base B X hX V x, ← h1]
  rfl

/-- **Stacks 03PU**, the isomorphism case for sheaves of sets. A morphism of sheaves of sets on
the small étale site of `X` which is bijective on the stalk at every geometric point of `X` is
an isomorphism. -/
public theorem isIso_of_bijective_etaleStalkMap_univ (α : F ⟶ G)
    (h : ∀ s : GeometricPoint X, Function.Bijective
      ((etaleStalkFunctor.{u, max (u + 1) v} B X hX s).map α)) :
    IsIso α :=
  (Sheaf.isLocallyBijective_iff_isIso α).1
    ⟨isLocallyInjective_of_injective_etaleStalkMap_type_univ B X hX α fun s ↦ (h s).1,
      isLocallySurjective_of_surjective_etaleStalkMap_type_univ B X hX α fun s ↦ (h s).2⟩

end Conservativity

section UnitComponent

variable {S T : B.Scheme} (k : T ⟶ S)

/-- The canonical map from the stalk of a direct image to the stalk at a point of the source,
evaluated on the unit of inverse and direct image, is the comparison of Tag 03Q1: for a
geometric point `x` of `T` and a sheaf `A` on the small étale site of `S`, the germ at `x ∘ k`
of a section of `A`, pushed into `k_* k⁻¹ A` and then read at `x`, is its germ in the stalk of
`k⁻¹ A`. -/
public theorem pushforwardEtaleStalkComponent_unit_univ (x : GeometricPoint T.1)
    (A : Sheaf (SmallEtale.topology B S.1 S.property) (Type (max (u + 1) v)))
    (z : etaleStalk B S.1 S.property (x.map (B.inclusion.map k)) A.obj) :
    pushforwardEtaleStalkComponentUniv B k x (x.map (B.inclusion.map k)) rfl
        ((B.smallInverseImage k (Type (max (u + 1) v))).obj A)
        ((etaleStalkFunctor.{u, max (u + 1) v} B S.1 S.property (x.map (B.inclusion.map k))).map
          ((B.smallPullbackAdjunction k (Type (max (u + 1) v))).unit.app A) z) =
      (smallEtalePullbackStalkIsoUniv B k x).inv.app A z := by
  let adj := B.smallPullbackAdjunction k (Type (max (u + 1) v))
  let L := B.smallInverseImage k (Type (max (u + 1) v))
  let R := B.smallPushforward k (Type (max (u + 1) v))
  let SS := etaleStalkFunctor.{u, max (u + 1) v} B S.1 S.property (x.map (B.inclusion.map k))
  let ST := etaleStalkFunctor.{u, max (u + 1) v} B T.1 T.property x
  let iso := smallEtalePullbackStalkIsoUniv B k x
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

/-- **The stalk computation of Stacks 0959.** For a cartesian square with `f` finite and a
geometric point `y` of `Y'`, the stalk of `f'_* (g')⁻¹ F` at `y` and the stalk of `g⁻¹ f_* F` at
`y` are both the product of the stalks of `F` over the lifts of `y`, hence in bijection: the
lifts of `y` through `f'` correspond, by composition with `g'`, to the lifts of `g ∘ y` through
`f`. -/
public def finiteBaseChangeStalkEquivUniv
    (sq : IsPullback (B.inclusion.map g') (B.inclusion.map f') (B.inclusion.map f)
      (B.inclusion.map g))
    [IsFinite (B.inclusion.map f)] (y : GeometricPoint Y'.1)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (max (u + 1) v))) :
    etaleStalk B Y'.1 Y'.property y
        (((B.smallPushforward f' (Type (max (u + 1) v))).obj
          ((B.smallInverseImage g' (Type (max (u + 1) v))).obj F)).obj) ≃
      etaleStalk B Y'.1 Y'.property y
        (((B.smallInverseImage g (Type (max (u + 1) v))).obj
          ((B.smallPushforward f (Type (max (u + 1) v))).obj F)).obj) :=
  haveI : IsFinite (B.inclusion.map f') := MorphismProperty.of_isPullback sq inferInstance
  (finitePushforwardStalkEquivUniv B f' y ((B.smallInverseImage g' (Type (max (u + 1) v))).obj
    F)).trans (((Equiv.piCongr (cartesianLiftEquiv B g' f' f g sq y) fun p =>
      ((smallEtalePullbackStalkIsoUniv B g'
        (geometricPointLift (B.inclusion.map f') y p)).app F).toEquiv).trans
      (finitePushforwardStalkEquivUniv B f (y.map (B.inclusion.map g)) F).symm).trans
      ((smallEtalePullbackStalkIsoUniv B g y).app
        ((B.smallPushforward f (Type (max (u + 1) v))).obj F)).toEquiv.symm)

/-- **Stacks Project, Tag 0959**, granted the compatibility of the canonical comparison with the
stalk computation. For a cartesian square with `f` finite, the canonical comparison
`g⁻¹ f_* F ⟶ f'_* (g')⁻¹ F` is an isomorphism as soon as its map on the stalk at every geometric
point of `Y'` is the bijection `AlgebraicGeometry.finiteBaseChangeStalkEquivUniv`. -/
public theorem isIso_smallEtaleBaseChangeNatTrans_of_stalkMap_eq_univ
    (sq : IsPullback (B.inclusion.map g') (B.inclusion.map f') (B.inclusion.map f)
      (B.inclusion.map g))
    [IsFinite (B.inclusion.map f)]
    (h : g' ≫ f = f' ≫ g)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (max (u + 1) v)))
    (hstalk : ∀ (y : GeometricPoint Y'.1)
      (z : etaleStalk B Y'.1 Y'.property y
        (((B.smallInverseImage g (Type (max (u + 1) v))).obj
          ((B.smallPushforward f (Type (max (u + 1) v))).obj F)).obj)),
      (etaleStalkFunctor.{u, max (u + 1) v} B Y'.1 Y'.property y).map
          ((smallEtaleBaseChangeNatTransUniv B g' f' f g h).app F) z =
        (finiteBaseChangeStalkEquivUniv.{u, v} B g' f' f g sq y F).symm z) :
    IsIso ((smallEtaleBaseChangeNatTransUniv B g' f' f g h).app F) :=
  isIso_of_bijective_etaleStalkMap_univ B Y'.1 Y'.property _ fun y => by
    have hb := (finiteBaseChangeStalkEquivUniv.{u, v} B g' f' f g sq y F).symm.bijective
    refine ⟨fun a b hab => hb.1 ?_, fun c => ?_⟩
    · exact ((hstalk y a).symm.trans hab).trans (hstalk y b)
    · obtain ⟨a, ha⟩ := hb.2 c
      exact ⟨a, (hstalk y a).trans ha⟩

end StalkBaseChange

/-- Equal morphisms of sheaves induce the same map on the étale stalk at a geometric point. -/
theorem etaleStalkFunctor_map_congr_univ (B : BigEtaleSite.{u}) (S : B.Scheme)
    (s : GeometricPoint S.1)
    {P Q : Sheaf (SmallEtale.topology B S.1 S.property) (Type (max (u + 1) v))} {a b : P ⟶ Q}
    (hab : a = b) (ζ : (etaleStalkFunctor.{u, max (u + 1) v} B S.1 S.property s).obj P) :
    (etaleStalkFunctor.{u, max (u + 1) v} B S.1 S.property s).map a ζ =
      (etaleStalkFunctor.{u, max (u + 1) v} B S.1 S.property s).map b ζ :=
  congrArg (fun m => (etaleStalkFunctor.{u, max (u + 1) v} B S.1 S.property s).map m ζ) hab

/-- The map on étale stalks induced by a composite of morphisms of sheaves is the composite of
the induced maps. -/
theorem etaleStalkFunctor_map_comp_apply_univ (B : BigEtaleSite.{u}) (S : B.Scheme)
    (s : GeometricPoint S.1)
    {P Q R : Sheaf (SmallEtale.topology B S.1 S.property) (Type (max (u + 1) v))}
    (a : P ⟶ Q) (b : Q ⟶ R)
    (ζ : (etaleStalkFunctor.{u, max (u + 1) v} B S.1 S.property s).obj P) :
    (etaleStalkFunctor.{u, max (u + 1) v} B S.1 S.property s).map (a ≫ b) ζ =
      (etaleStalkFunctor.{u, max (u + 1) v} B S.1 S.property s).map b
        ((etaleStalkFunctor.{u, max (u + 1) v} B S.1 S.property s).map a ζ) :=
  ConcreteCategory.congr_hom
    ((etaleStalkFunctor.{u, max (u + 1) v} B S.1 S.property s).map_comp a b) ζ

section BaseChangeNeighborhood

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) {x : GeometricPoint X.1}
  {y : GeometricPoint Y.1} (h : x.map (B.inclusion.map f) = y)
  (V : SmallEtale B Y.1 Y.property) (v : (geometricPointFiber B Y.1 Y.property y).obj V)

/-- **The comparison on germs, at the base-changed neighborhood.** The germ at `y` of a section
of `f_* F` over an étale neighborhood `V` of `y` is sent to the germ at `x` of the same section,
read over the pointed étale neighborhood `V ×_Y X` of `x`. -/
theorem pushforwardEtaleStalkComponent_germ_baseChange_univ
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (max (u + 1) v)))
    (σ : F.obj.obj (op ((smallEtaleBaseChange B f).obj V))) :
    pushforwardEtaleStalkComponentUniv B f x y h F
        (colimit.ι ((CategoryOfElements.π (geometricPointFiber B Y.1 Y.property y)).op ⋙
          ((B.smallPushforward f (Type (max (u + 1) v))).obj F).obj) (op ⟨v⟩) σ) =
      colimit.ι ((CategoryOfElements.π (geometricPointFiber B X.1 X.property x)).op ⋙ F.obj)
        (op ⟨baseChangeEtalePoint B f h V v⟩) σ := by
  have h0 : (SmallEtale.toScheme B X.1 X.property).map
      (𝟙 ((smallEtaleBaseChange B f).obj V)) = 𝟙 _ :=
    CategoryTheory.Functor.map_id _ _
  have h1 : (SmallEtale.toScheme B X.1 X.property).map
        (𝟙 ((smallEtaleBaseChange B f).obj V)) ≫
      B.inclusion.map (pullback.fst V.obj.hom f) =
      B.inclusion.map (pullback.fst V.obj.hom f) :=
    (congrArg (fun m => m ≫ B.inclusion.map (pullback.fst V.obj.hom f)) h0).trans
      (Category.id_comp _)
  have ht : (baseChangeEtalePoint B f h V v).1 ≫
      (SmallEtale.toScheme B X.1 X.property).map (𝟙 ((smallEtaleBaseChange B f).obj V)) ≫
        B.inclusion.map (pullback.fst V.obj.hom f) =
      eqToHom (congrArg (fun q : GeometricPoint Y.1 => q.source) h) ≫ v.1 :=
    (congrArg (fun m => (baseChangeEtalePoint B f h V v).1 ≫ m) h1).trans
      (baseChangeEtalePointHom_fst B f h V v)
  refine (pushforwardEtaleStalkComponent_germ_univ B f x y h F ⟨v⟩
    ⟨baseChangeEtalePoint B f h V v⟩ (𝟙 _) ht σ).trans ?_
  exact congrArg (fun z => colimit.ι
      ((CategoryOfElements.π (geometricPointFiber B X.1 X.property x)).op ⋙ F.obj)
      (op ⟨baseChangeEtalePoint B f h V v⟩) z)
    (ConcreteCategory.congr_hom (F.obj.map_id (op ((smallEtaleBaseChange B f).obj V))) σ)

end BaseChangeNeighborhood

section Composite

variable (B : BigEtaleSite.{u}) {W T S : B.Scheme} (k : W ⟶ T) (l : T ⟶ S)

variable {w : GeometricPoint W.1} {t : GeometricPoint T.1} {s : GeometricPoint S.1}
  (hk : w.map (B.inclusion.map k) = t) (hl : t.map (B.inclusion.map l) = s)
  (hm : w.map (B.inclusion.map (k ≫ l)) = s)
  (V : SmallEtale B S.1 S.property) (v : (geometricPointFiber B S.1 S.property s).obj V)

/-- **The canonical stalk map of a direct image is multiplicative in the morphism.** Let
`k : W ⟶ T` and `l : T ⟶ S`, and let `w`, `t`, `s` be geometric points of `W`, `T`, `S` with `w`
over `t` and `t` over `s`. For a sheaf `F` on the small étale site of `W`, the canonical map
from the stalk of `(k ≫ l)_* F` at `s` to the stalk of `F` at `w` is the map for `l` at the
sheaf `k_* F`, followed by the map for `k`, after the identification `(k ≫ l)_* F = l_* k_* F`
of Tag 021J. -/
theorem pushforwardEtaleStalkComponent_comp_univ
    (F : Sheaf (SmallEtale.topology B W.1 W.property) (Type (max (u + 1) v)))
    (z : etaleStalk B S.1 S.property s
      (((B.smallPushforward (k ≫ l) (Type (max (u + 1) v))).obj F).obj)) :
    pushforwardEtaleStalkComponentUniv B (k ≫ l) w s hm F z =
      pushforwardEtaleStalkComponentUniv B k w t hk F
        (pushforwardEtaleStalkComponentUniv B l t s hl
            ((B.smallPushforward k (Type (max (u + 1) v))).obj F)
          ((etaleStalkFunctor.{u, max (u + 1) v} B S.1 S.property s).map
            ((smallEtaleSheafPushforwardCompIso B W T S k l (Type (max (u + 1) v))).inv.app F)
              z)) := by
  obtain ⟨V, v, σ, hz⟩ :=
    (geometricPointSitePoint B S.1 S.property s).toPresheafFiber_jointly_surjective
      (P := ((B.smallPushforward (k ≫ l) (Type (max (u + 1) v))).obj F).obj) z
  have hz' : colimit.ι ((CategoryOfElements.π (geometricPointFiber B S.1 S.property s)).op ⋙
      ((B.smallPushforward (k ≫ l) (Type (max (u + 1) v))).obj F).obj) (op ⟨v⟩) σ = z := hz
  subst hz'
  have hR1 : (etaleStalkFunctor.{u, max (u + 1) v} B S.1 S.property s).map
        ((smallEtaleSheafPushforwardCompIso B W T S k l (Type (max (u + 1) v))).inv.app F)
        (colimit.ι ((CategoryOfElements.π (geometricPointFiber B S.1 S.property s)).op ⋙
          ((B.smallPushforward (k ≫ l) (Type (max (u + 1) v))).obj F).obj) (op ⟨v⟩) σ) =
      colimit.ι ((CategoryOfElements.π (geometricPointFiber B S.1 S.property s)).op ⋙
        ((B.smallPushforward l (Type (max (u + 1) v))).obj
          ((B.smallPushforward k (Type (max (u + 1) v))).obj F)).obj) (op ⟨v⟩)
        (F.obj.map ((smallEtaleBaseChange_compIso B W T S k l).val.hom.app V).op σ) :=
    (geometricPointSitePoint B S.1 S.property s).toPresheafFiber_naturality_apply
      ((smallEtaleSheafPushforwardCompIso B W T S k l (Type (max (u + 1) v))).inv.app F).hom V v σ
  have c1 := congrArg (fun a => pushforwardEtaleStalkComponentUniv B k w t hk F
    (pushforwardEtaleStalkComponentUniv B l t s hl
      ((B.smallPushforward k (Type (max (u + 1) v))).obj F) a)) hR1
  have c2 := congrArg (pushforwardEtaleStalkComponentUniv B k w t hk F)
    (pushforwardEtaleStalkComponent_germ_baseChange_univ.{u, v} B l hl V v
      ((B.smallPushforward k (Type (max (u + 1) v))).obj F)
      (F.obj.map ((smallEtaleBaseChange_compIso B W T S k l).val.hom.app V).op σ))
  have c3 := pushforwardEtaleStalkComponent_germ_baseChange_univ.{u, v} B k hk
    ((smallEtaleBaseChange B l).obj V) (baseChangeEtalePoint B l hl V v) F
    (F.obj.map ((smallEtaleBaseChange_compIso B W T S k l).val.hom.app V).op σ)
  have c4 := (geometricPointSitePoint B W.1 W.property w).toPresheafFiber_w_apply
    ((smallEtaleBaseChange_compIso B W T S k l).val.hom.app V)
    (baseChangeEtalePoint B k hk ((smallEtaleBaseChange B l).obj V)
      (baseChangeEtalePoint B l hl V v)) F.obj σ
  have c5 := congrArg (fun pt => colimit.ι
      ((CategoryOfElements.π (geometricPointFiber B W.1 W.property w)).op ⋙ F.obj)
      (op ⟨pt⟩) σ)
    (baseChangeEtalePoint_comp B k l hk hl hm V v)
  exact (pushforwardEtaleStalkComponent_germ_baseChange_univ.{u, v} B (k ≫ l) hm V v F σ).trans
    (((c1.trans c2).trans (c3.trans (c4.trans c5))).symm)

end Composite

section BaseChange

variable (B : BigEtaleSite.{u}) {X' X Y' Y : B.Scheme} (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- The canonical stalk map of a direct image is compatible with transporting the sheaf along an
equality of morphisms. -/
theorem pushforwardEtaleStalkComponent_eqToHom_univ {Z W : B.Scheme} (k k' : Z ⟶ W) (hkk' : k = k')
    (x : GeometricPoint Z.obj) (y : GeometricPoint W.1)
    (hc : x.map (B.inclusion.map k) = y) (hc' : x.map (B.inclusion.map k') = y)
    (F : Sheaf (SmallEtale.topology B Z.obj Z.property) (Type (max (u + 1) v)))
    (z : etaleStalk B W.1 W.property y (((B.smallPushforward k (Type (max (u + 1) v))).obj
      F).obj)) :
    pushforwardEtaleStalkComponentUniv B k' x y hc' F
        ((etaleStalkFunctor.{u, max (u + 1) v} B W.1 W.property y).map
          ((eqToIso (congrArg
            (fun m : Z ⟶ W => B.smallPushforward m (Type (max (u + 1) v))) hkk')).hom.app F) z) =
      pushforwardEtaleStalkComponentUniv B k x y hc F z := by
  subst hkk'
  refine congrArg (pushforwardEtaleStalkComponentUniv B k x y hc' F) ?_
  simp
  rfl

/-- The identification `g'_* f_* ⟶ f'_* g_*` of the two composite direct images around a
commuting square `g' ≫ f = f' ≫ g` of a big étale site, through the direct image along the
common composite. Its mate along the inverse-image/direct-image adjunctions of `g` and `g'` is
`AlgebraicGeometry.smallEtaleBaseChangeNatTransUniv`. -/
def smallEtaleBaseChangeMateUniv (h : g' ≫ f = f' ≫ g) :
    B.smallPushforward g' (Type (max (u + 1) v)) ⋙ B.smallPushforward f (Type (max (u + 1) v)) ⟶
      B.smallPushforward f' (Type (max (u + 1) v)) ⋙ B.smallPushforward g (Type (max (u + 1) v)) :=
  (smallEtaleSheafPushforwardCompIso B X' X Y g' f (Type (max (u + 1) v))).hom ≫
    (eqToIso (congrArg
      (fun k : X' ⟶ Y => B.smallPushforward k (Type (max (u + 1) v))) h)).hom ≫
    (smallEtaleSheafPushforwardCompIso B X' Y' Y f' g (Type (max (u + 1) v))).inv

/-- The identification of the two composite direct images is the composite of the two
comparisons of Tag 021J with the transport along the equality of the two composites. -/
theorem smallEtaleBaseChangeMate_eq_univ (h : g' ≫ f = f' ≫ g) :
    smallEtaleBaseChangeMateUniv B g' f' f g h =
      (smallEtaleSheafPushforwardCompIso B X' X Y g' f (Type (max (u + 1) v))).hom ≫
        ((eqToIso (congrArg
            (fun k : X' ⟶ Y => B.smallPushforward k (Type (max (u + 1) v))) h)).hom ≫
          (smallEtaleSheafPushforwardCompIso B X' Y' Y f' g (Type (max (u + 1) v))).inv) := rfl

/-- The identification of the two composite direct images, evaluated at a sheaf. -/
theorem smallEtaleBaseChangeMate_app_univ (h : g' ≫ f = f' ≫ g)
    (A : Sheaf (SmallEtale.topology B X'.1 X'.property) (Type (max (u + 1) v))) :
    (smallEtaleBaseChangeMateUniv B g' f' f g h).app A =
      (smallEtaleSheafPushforwardCompIso B X' X Y g' f (Type (max (u + 1) v))).hom.app A ≫
        ((eqToIso (congrArg
            (fun k : X' ⟶ Y => B.smallPushforward k (Type (max (u + 1) v))) h)).hom.app A ≫
          (smallEtaleSheafPushforwardCompIso B X' Y' Y f' g (Type (max (u + 1) v))).inv.app A) :=
  (congrArg (fun α : B.smallPushforward g' (Type (max (u + 1) v)) ⋙
      B.smallPushforward f (Type (max (u + 1) v)) ⟶ B.smallPushforward f' (Type (max (u + 1) v)) ⋙
        B.smallPushforward g (Type (max (u + 1) v)) => α.app A)
    (smallEtaleBaseChangeMate_eq_univ B g' f' f g h)).trans
    ((NatTrans.comp_app
        (smallEtaleSheafPushforwardCompIso B X' X Y g' f (Type (max (u + 1) v))).hom
        ((eqToIso (congrArg
            (fun k : X' ⟶ Y => B.smallPushforward k (Type (max (u + 1) v))) h)).hom ≫
          (smallEtaleSheafPushforwardCompIso B X' Y' Y f' g (Type (max (u + 1) v))).inv) A).trans
      (congrArg (fun z =>
          (smallEtaleSheafPushforwardCompIso B X' X Y g' f (Type (max (u + 1) v))).hom.app A ≫ z)
        (NatTrans.comp_app
          (eqToIso (congrArg
            (fun k : X' ⟶ Y => B.smallPushforward k (Type (max (u + 1) v))) h)).hom
          (smallEtaleSheafPushforwardCompIso B X' Y' Y f' g (Type (max (u + 1) v))).inv A)))

/-- The canonical base-change comparison `g⁻¹ f_* ⟶ f'_* (g')⁻¹` is the mate of the
identification of the two composite direct images. -/
theorem smallEtaleBaseChangeNatTrans_eq_mateEquiv_symm_univ (h : g' ≫ f = f' ≫ g) :
    smallEtaleBaseChangeNatTransUniv B g' f' f g h =
      (mateEquiv (B.smallPullbackAdjunction g' (Type (max (u + 1) v)))
        (B.smallPullbackAdjunction g (Type (max (u + 1) v)))).symm
        (smallEtaleBaseChangeMateUniv B g' f' f g h) := rfl

/-- The adjunction units relate the base-change comparison to the identification of the two
composite direct images: `f_*` of the unit of `g'`, followed by that identification, is the unit
of `g` followed by `g_*` of the comparison. -/
theorem unit_comp_smallEtaleBaseChangeNatTrans_univ (h : g' ≫ f = f' ≫ g)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (max (u + 1) v))) :
    (B.smallPushforward f (Type (max (u + 1) v))).map
          ((B.smallPullbackAdjunction g' (Type (max (u + 1) v))).unit.app F) ≫
        (smallEtaleBaseChangeMateUniv B g' f' f g h).app
          ((B.smallInverseImage g' (Type (max (u + 1) v))).obj F) =
      (B.smallPullbackAdjunction g (Type (max (u + 1) v))).unit.app
          ((B.smallPushforward f (Type (max (u + 1) v))).obj F) ≫
        (B.smallPushforward g (Type (max (u + 1) v))).map
          (((mateEquiv (B.smallPullbackAdjunction g' (Type (max (u + 1) v)))
            (B.smallPullbackAdjunction g (Type (max (u + 1) v)))).symm
            (smallEtaleBaseChangeMateUniv B g' f' f g h)).app F) :=
  unit_mateEquiv_symm' (B.smallPullbackAdjunction g' (Type (max (u + 1) v)))
    (B.smallPullbackAdjunction g (Type (max (u + 1) v))) (smallEtaleBaseChangeMateUniv B g' f' f g
        h) F

/-- **The stalk map of the base-change comparison, read at one lift.** For a cartesian square
and a lift `p` of a geometric point `y` of `Y'` through `f'`, the canonical map at `p` applied to
the stalk map of `g⁻¹ f_* F ⟶ f'_* (g')⁻¹ F` is the canonical map from the stalk of `f_* F` at
`g ∘ y` to the stalk of `F` at the corresponding lift `p ∘ g'` of `g ∘ y`, transported into the
stalk of `(g')⁻¹ F` by the comparison of Tag 03Q1. -/
theorem pushforwardEtaleStalkComponent_smallEtaleBaseChangeNatTrans_univ
    (sq : IsPullback (B.inclusion.map g') (B.inclusion.map f') (B.inclusion.map f)
      (B.inclusion.map g))
    (h : g' ≫ f = f' ≫ g)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (max (u + 1) v)))
    (y : GeometricPoint Y'.1) (p : {a : y.source ⟶ X'.1 // a ≫ B.inclusion.map f' = y.hom})
    (ζ : etaleStalk B Y.1 Y.property (y.map (B.inclusion.map g))
      (((B.smallPushforward f (Type (max (u + 1) v))).obj F).obj)) :
    pushforwardEtaleStalkComponentUniv B f' (geometricPointLift (B.inclusion.map f') y p) y
        (geometricPointLift_map (B.inclusion.map f') y p)
        ((B.smallInverseImage g' (Type (max (u + 1) v))).obj F)
        ((etaleStalkFunctor.{u, max (u + 1) v} B Y'.1 Y'.property y).map
          ((smallEtaleBaseChangeNatTransUniv B g' f' f g h).app F)
          ((smallEtalePullbackStalkIsoUniv B g y).inv.app
            ((B.smallPushforward f (Type (max (u + 1) v))).obj F) ζ)) =
      (smallEtalePullbackStalkIsoUniv B g'
          (geometricPointLift (B.inclusion.map f') y p)).inv.app F
        (pushforwardEtaleStalkComponentUniv B f
          (geometricPointLift (B.inclusion.map f) (y.map (B.inclusion.map g))
            (cartesianLiftEquiv B g' f' f g sq y p))
          (y.map (B.inclusion.map g))
          (geometricPointLift_map (B.inclusion.map f) (y.map (B.inclusion.map g))
            (cartesianLiftEquiv B g' f' f g sq y p)) F ζ) := by
  have hp := geometricPointLift_map (B.inclusion.map f') y p
  have hl1 := geometricPointLift_map (B.inclusion.map f) (y.map (B.inclusion.map g))
    (cartesianLiftEquiv B g' f' f g sq y p)
  have hk1 : (geometricPointLift (B.inclusion.map f') y p).map (B.inclusion.map g') =
      (geometricPointLift (B.inclusion.map f) (y.map (B.inclusion.map g)) (cartesianLiftEquiv
      B g' f' f g sq y p)) := rfl
  have hm1 : (geometricPointLift (B.inclusion.map f') y p).map (B.inclusion.map (g' ≫ f)) = (y.map
      (B.inclusion.map g)) := by
    rw [B.inclusion.map_comp, GeometricPoint.map_comp]
    exact hl1
  have hm2 : (geometricPointLift (B.inclusion.map f') y p).map (B.inclusion.map (f' ≫ g)) = (y.map
      (B.inclusion.map g)) := by
    rw [B.inclusion.map_comp, GeometricPoint.map_comp, hp]
  have mt := unit_comp_smallEtaleBaseChangeNatTrans_univ.{u, v} B g' f' f g h F
  rw [smallEtaleBaseChangeNatTrans_eq_mateEquiv_symm_univ]
  set E := etaleStalkFunctor.{u, max (u + 1) v} B Y.1 Y.property (y.map (B.inclusion.map g))
  have inner := (etaleStalkFunctor_map_comp_apply_univ.{u, v} (P := (B.smallPushforward f _).obj F)
      B Y _ _ _ ζ).symm.trans <|
    (etaleStalkFunctor_map_congr_univ.{u, v} B Y _ mt.symm ζ).trans <|
    (etaleStalkFunctor_map_comp_apply_univ.{u, v} (P := (B.smallPushforward f _).obj F)
      B Y _ _ _ ζ).trans <|
    (etaleStalkFunctor_map_congr_univ.{u, v} B Y _
      (smallEtaleBaseChangeMate_app_univ B g' f' f g h _) _).trans <|
    (etaleStalkFunctor_map_comp_apply_univ.{u, v} B Y _ _ _ _).trans
      (etaleStalkFunctor_map_comp_apply_univ.{u, v} B Y _ _ _ _)
  have s10 : ∀ z, E.map
        ((smallEtaleSheafPushforwardCompIso B X' X Y g' f (Type (max (u + 1) v))).inv.app
          ((B.smallInverseImage g' (Type (max (u + 1) v))).obj F))
      (E.map
        ((smallEtaleSheafPushforwardCompIso B X' X Y g' f (Type (max (u + 1) v))).hom.app
          ((B.smallInverseImage g' (Type (max (u + 1) v))).obj F)) z) = z := fun z =>
    (etaleStalkFunctor_map_comp_apply_univ.{u, v} B Y _ _ _ z).symm.trans
      ((etaleStalkFunctor_map_congr_univ.{u, v} B Y _
        ((smallEtaleSheafPushforwardCompIso B X' X Y g' f (Type (max (u + 1) v))).hom_inv_id_app
          ((B.smallInverseImage g' (Type (max (u + 1) v))).obj F)) z).trans
        (ConcreteCategory.congr_hom (E.map_id _) z))
  have einner := (congrArg ((etaleStalkFunctor.{u, max (u + 1) v} B Y'.1 Y'.property y).map
        (((mateEquiv (B.smallPullbackAdjunction g' (Type (max (u + 1) v)))
          (B.smallPullbackAdjunction g (Type (max (u + 1) v)))).symm
            (smallEtaleBaseChangeMateUniv B g' f' f g h)).app F))
      (pushforwardEtaleStalkComponent_unit_univ.{u, v} B g y _ ζ).symm).trans
    ((pushforwardEtaleStalkComponent_natural_univ.{u, v} B g y _ rfl _ _).symm.trans
      (congrArg (pushforwardEtaleStalkComponentUniv B g y _ rfl _) inner))
  refine (congrArg (pushforwardEtaleStalkComponentUniv B f' _ y hp _) einner).trans
    ((pushforwardEtaleStalkComponent_comp_univ.{u, v} B f' g hp rfl hm2 _ _).symm.trans
    ((pushforwardEtaleStalkComponent_eqToHom_univ.{u, v} B (g' ≫ f) (f' ≫ g) h _ _ hm1 hm2 _
      _).trans
    ((pushforwardEtaleStalkComponent_comp_univ.{u, v} B g' f hk1 hl1 hm1 _ _).trans ?_)))
  rw [s10]
  exact (congrArg (pushforwardEtaleStalkComponentUniv B g' _ _ hk1 _)
    (pushforwardEtaleStalkComponent_natural_univ.{u, v} B f _ _ hl1 _ ζ)).trans
    (pushforwardEtaleStalkComponent_unit_univ.{u, v} B g' _ F _)

/-- **Stacks Project, Tag 0959.** Consider a cartesian square
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
of schemes of a big étale site with `f` finite, and a sheaf of sets `F` on the small étale site
of `X`, with values in `Type (max (u + 1) v)` for any universe `v`. Then the canonical
comparison `g⁻¹ f_* F ⟶ f'_* (g')⁻¹ F` is an isomorphism. -/
theorem isIso_smallEtaleBaseChangeNatTrans_univ
    (sq : IsPullback (B.inclusion.map g') (B.inclusion.map f') (B.inclusion.map f)
      (B.inclusion.map g))
    [IsFinite (B.inclusion.map f)] (h : g' ≫ f = f' ≫ g)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (max (u + 1) v))) :
    IsIso ((smallEtaleBaseChangeNatTransUniv B g' f' f g h).app F) := by
  have hf' : IsFinite (B.inclusion.map f') := MorphismProperty.of_isPullback sq inferInstance
  refine isIso_smallEtaleBaseChangeNatTrans_of_stalkMap_eq_univ.{u, v} B g' f' f g sq h F ?_
  intro y z
  refine (finitePushforwardStalkEquivUniv B f' y ((B.smallInverseImage g' (Type (max (u + 1)
      v))).obj F)).injective ?_
  have h1 : (finitePushforwardStalkEquivUniv B f' y ((B.smallInverseImage g' (Type (max (u + 1)
    v))).obj F))
        ((finiteBaseChangeStalkEquivUniv.{u, v} B g' f' f g sq y F).symm z) =
      (Equiv.piCongr (cartesianLiftEquiv B g' f' f g sq y) fun q =>
        ((smallEtalePullbackStalkIsoUniv B g'
          (geometricPointLift (B.inclusion.map f') y q)).app F).toEquiv).symm
        ((finitePushforwardStalkEquivUniv B f (y.map (B.inclusion.map g)) F)
          (((smallEtalePullbackStalkIsoUniv B g y).app ((B.smallPushforward f
              (Type (max (u + 1) v))).obj F)).toEquiv z)) :=
    Equiv.apply_symm_apply _ _
  rw [h1]
  funext p
  have hz : (smallEtalePullbackStalkIsoUniv B g y).inv.app ((B.smallPushforward f
    (Type (max (u + 1) v))).obj F)
      (((smallEtalePullbackStalkIsoUniv B g y).app ((B.smallPushforward f (Type (max (u + 1)
      v))).obj F)).toEquiv z) = z :=
    Equiv.symm_apply_apply (((smallEtalePullbackStalkIsoUniv B g y).app ((B.smallPushforward f
      (Type (max (u + 1) v))).obj F)).toEquiv) z
  refine Eq.trans (congrArg (fun ww => finitePushforwardStalkEquivUniv B f' y ((B.smallInverseImage
      g' (Type (max (u + 1) v))).obj F)
    ((etaleStalkFunctor.{u, max (u + 1) v} B Y'.1 Y'.property y).map
        ((smallEtaleBaseChangeNatTransUniv B g' f' f g h).app F) ww) p) hz.symm) ?_
  exact pushforwardEtaleStalkComponent_smallEtaleBaseChangeNatTrans_univ.{u, v} B g' f' f g sq h F y
      p
    (((smallEtalePullbackStalkIsoUniv B g y).app ((B.smallPushforward f (Type (max (u + 1) v))).obj
        F)).toEquiv z)

end BaseChange

end AlgebraicGeometry

end
