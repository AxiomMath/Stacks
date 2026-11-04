module

public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismObstructionKey
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismObstructionSourceIdealAmbient

/-!
# The map of source thickenings induced by a morphism of deformations of the target

Let `f : X ⟶ Y` be a morphism of schemes over `k` and `a : Y'_x ⟶ Y'_y` a morphism of
deformations of `Y` (over a morphism `k[M] ⟶ k[N]` of square-zero bases). It is a morphism of
schemes `b : Y'_y ⟶ Y'_x` restricting to the identity of `Y`, so it induces a map of sheaves of
rings `f⁻¹𝒪_{Y'_x} ⟶ f⁻¹𝒪_{Y'_y}` on `|X|`. This file builds that map and proves that it is
compatible with the reductions to `f⁻¹𝒪_Y`, with the `k`-algebra structures, and with the
sections induced by sections of `𝒪_{Y'_x}`.

## Main definitions

* `Deformation.Examples.sourceIdealTransition`: the map `f⁻¹𝒪_{Y'_x} ⟶ f⁻¹𝒪_{Y'_y}`.

## Main results

* `AlgebraicGeometry.Scheme.liftToSheafHom_ambientSection`: on the section induced by `t`, the
  map `f⁻¹𝒪_{Y₁} ⟶ f⁻¹𝒪_{Y₂}` of `b : Y₂ ⟶ Y₁` is the section induced by `b^♯(t)`.
* `AlgebraicGeometry.Scheme.liftToSheafHom_comp_liftSourceReduction`: it lies over `f⁻¹𝒪_Y`.
* `Deformation.Examples.sourceIdealTransition_ambientSection`,
  `Deformation.Examples.sourceIdealTransition_comp_reduction`: the same for a morphism of
  deformations.
* `Deformation.Examples.schemeMorphismPushBase_comp_sourceIdealTransition`: it is a map of
  `k`-algebras.

## References

* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Topology

/-- **Maps out of an inverse image are determined on induced sections**: two maps
`f⁻¹F ⟶ G` agreeing on the sections induced by sections of `F` over the opens `f⁻¹W` are equal,
both being adjoint to the same map `F ⟶ f_*G`. -/
theorem pullback_hom_ext_ambientSection {X Y : TopCat.{u}} (f : X ⟶ Y)
    {F : Y.Sheaf CommRingCat.{u}} {G : X.Sheaf CommRingCat.{u}}
    {φ₁ φ₂ : (TopCat.Sheaf.pullback CommRingCat.{u} f).obj F ⟶ G}
    (h : ∀ (W : Opens Y) (t : F.presheaf.obj (op W)),
      (φ₁.hom.app (op ((Opens.map f).obj W))).hom (ambientSection f F le_rfl t) =
        (φ₂.hom.app (op ((Opens.map f).obj W))).hom (ambientSection f F le_rfl t)) :
    φ₁ = φ₂ := by
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).homEquiv F G).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  refine Sheaf.hom_ext (NatTrans.ext (funext fun W => ConcreteCategory.hom_ext _ _ fun t => ?_))
  have hu := ConcreteCategory.congr_hom (ambientSection_eq_unit f F W.unop) t
  exact (congrArg (φ₁.hom.app (op ((Opens.map f).obj W.unop))).hom hu.symm).trans
    ((h W.unop t).trans (congrArg (φ₂.hom.app (op ((Opens.map f).obj W.unop))).hom hu))

end Stacks.Topology

namespace AlgebraicGeometry.Scheme

open RingedSpace Stacks.Topology

variable {X Y Y₁ Y₂ : Scheme.{u}} (f : X ⟶ Y) {j₁ : Y ⟶ Y₁} {j₂ : Y ⟶ Y₂} {b : Y₂ ⟶ Y₁}

/-- **The map of inverse images of a morphism `b : Y₂ ⟶ Y₁` under `Y`, on induced sections**:
for `j₂ ≫ b = j₁`, the map `f⁻¹𝒪_{Y₁} ⟶ f⁻¹𝒪_{Y₂}` of `b` takes the section induced by `t` to the
section induced by `b^♯(t)`. -/
theorem liftToSheafHom_ambientSection (h : j₂ ≫ b = j₁) (hb : (f ≫ j₂) ≫ b = f ≫ j₁)
    {W : TopologicalSpace.Opens Y₁.carrier} {V : TopologicalSpace.Opens X.carrier}
    (hV : V ≤ (TopologicalSpace.Opens.map (f ≫ j₁).toLRSHom.toShHom.hom.base).obj W)
    (hV' : V ≤ (TopologicalSpace.Opens.map (f ≫ j₂).toLRSHom.toShHom.hom.base).obj
      ((TopologicalSpace.Opens.map b.toLRSHom.toShHom.hom.base).obj W))
    (t : Y₁.presheaf.obj (op W)) :
    ((liftToSheafHom b hb).hom.app (op V)).hom
        (ambientSection (f ≫ j₁).toLRSHom.toShHom.hom.base Y₁.sheaf hV t) =
      ambientSection (f ≫ j₂).toLRSHom.toShHom.hom.base Y₂.sheaf hV'
        ((b.toLRSHom.toShHom.hom.c.app (op W)).hom t) := by
  subst h
  have key : ∀ {A B : TopCat.Sheaf CommRingCat.{u} X.carrier} (e : A = A) (s : A ⟶ B),
      eqToHom e ≫ s = s := fun e s => by rw [eqToHom_refl, Category.id_comp]
  have hρ : ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
      (f ≫ j₂ ≫ b).toLRSHom.toShHom.hom.base).homEquiv _ _) (liftToSheafHom b hb) =
      ⟨(liftTargetProjection (f ≫ j₂) ≫ b.toLRSHom.toShHom).hom.c⟩ :=
    (congrArg _ (key _ _)).trans (Equiv.apply_symm_apply _ _)
  have hu : ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
        (f ≫ j₂ ≫ b).toLRSHom.toShHom.hom.base).unit.app Y₁.sheaf).hom.app (op W) ≫
        (liftToSheafHom b hb).hom.app
          (op ((TopologicalSpace.Opens.map (f ≫ j₂ ≫ b).toLRSHom.toShHom.hom.base).obj W)) =
      b.toLRSHom.toShHom.hom.c.app (op W) ≫
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
          (f ≫ j₂).toLRSHom.toShHom.hom.base).unit.app Y₂.sheaf).hom.app
            (op ((TopologicalSpace.Opens.map b.toLRSHom.toShHom.hom.base).obj W)) :=
    congrArg (fun φ : Y₁.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} (f ≫ j₂ ≫ b).toLRSHom.toShHom.hom.base).obj
        (liftTarget (f ≫ j₂)) => φ.hom.app (op W))
      ((Adjunction.homEquiv_unit _ _ _ (liftToSheafHom b hb)).symm.trans hρ)
  have hn := (liftToSheafHom b hb).hom.naturality (homOfLE hV).op
  have E : ambientSection (f ≫ j₂ ≫ b).toLRSHom.toShHom.hom.base Y₁.sheaf hV ≫
      (liftToSheafHom b hb).hom.app (op V) =
      b.toLRSHom.toShHom.hom.c.app (op W) ≫
        ambientSection (f ≫ j₂).toLRSHom.toShHom.hom.base Y₂.sheaf hV' := by
    rw [ambientSection_eq_unit_comp (f ≫ j₂ ≫ b).toLRSHom.toShHom.hom.base Y₁.sheaf hV,
      ambientSection_eq_unit_comp (f ≫ j₂).toLRSHom.toShHom.hom.base Y₂.sheaf hV']
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (_ ≫ ·) hn).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ _) hu).trans ?_
    exact Category.assoc _ _ _
  exact ConcreteCategory.congr_hom E t

/-- **The map of inverse images of `b : Y₂ ⟶ Y₁` under `Y` lies over `f⁻¹𝒪_Y`**: for
`j₂ ≫ b = j₁`, it commutes with the reductions `f⁻¹𝒪_{Y_i} ⟶ f⁻¹𝒪_Y`. -/
theorem liftToSheafHom_comp_liftSourceReduction (h : j₂ ≫ b = j₁)
    (hb : (f ≫ j₂) ≫ b = f ≫ j₁) :
    liftToSheafHom b hb ≫ liftSourceReduction j₂ f = liftSourceReduction j₁ f := by
  have hV' : ∀ W : TopologicalSpace.Opens Y₁.carrier,
      (TopologicalSpace.Opens.map (f ≫ j₁).toLRSHom.toShHom.hom.base).obj W ≤
        (TopologicalSpace.Opens.map (f ≫ j₂).toLRSHom.toShHom.hom.base).obj
          ((TopologicalSpace.Opens.map b.toLRSHom.toShHom.hom.base).obj W) := by
    subst h; exact fun W => le_rfl
  refine pullback_hom_ext_ambientSection _ fun W t => ?_
  refine (congrArg ((liftSourceReduction j₂ f).hom.app _).hom
    (liftToSheafHom_ambientSection f h hb le_rfl (hV' W) t)).trans ?_
  refine (liftSourceReduction_ambientSection j₂ f (hV' W) _).trans ?_
  refine Eq.trans ?_ (liftSourceReduction_ambientSection j₁ f le_rfl t).symm
  subst h
  rfl

end AlgebraicGeometry.Scheme

namespace Deformation.Examples

open AlgebraicGeometry

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y) {pY : Y ⟶ baseSpec (residueFieldBase Λ k)}
  {M N : FGModuleCat.{u} k}
  {x : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)).Fiber
    ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)}
  {y : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)).Fiber
    ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj N)}
  (a : x.1 ⟶ y.1)

/-- **The map `f⁻¹𝒪_{Y'_x} ⟶ f⁻¹𝒪_{Y'_y}` induced by a morphism `a` of deformations of `Y`**:
the map of sheaves of rings of the morphism of schemes `Y'_y ⟶ Y'_x` underlying `a`, which
restricts to the identity of `Y`. -/
abbrev sourceIdealTransition :
    Scheme.liftSource x.1.specialMap f ⟶ Scheme.liftSource y.1.specialMap f :=
  Scheme.liftToSheafHom (i := f ≫ y.1.specialMap) (j := x.1.specialMap) a.map
    (by rw [Category.assoc, a.special_compat])

/-- The induced map commutes with the reductions to `f⁻¹𝒪_Y`. -/
theorem sourceIdealTransition_comp_reduction :
    sourceIdealTransition f a ≫ Scheme.liftSourceReduction y.1.specialMap f =
      Scheme.liftSourceReduction x.1.specialMap f :=
  Scheme.liftToSheafHom_comp_liftSourceReduction f a.special_compat _

/-- **The induced map on induced sections**: the section of `f⁻¹𝒪_{Y'_x}` induced by `t` goes
to the section of `f⁻¹𝒪_{Y'_y}` induced by the pullback of `t` along `Y'_y ⟶ Y'_x`. -/
theorem sourceIdealTransition_ambientSection {W : Opens x.1.scheme.carrier}
    {V : Opens X.carrier}
    (hV : V ≤ (Opens.map (f ≫ x.1.specialMap).toLRSHom.toShHom.hom.base).obj W)
    (hV' : V ≤ (Opens.map (f ≫ y.1.specialMap).toLRSHom.toShHom.hom.base).obj
      ((Opens.map a.map.toLRSHom.toShHom.hom.base).obj W))
    (t : x.1.scheme.presheaf.obj (op W)) :
    ((sourceIdealTransition f a).hom.app (op V)).hom
        (Stacks.Topology.ambientSection (f ≫ x.1.specialMap).toLRSHom.toShHom.hom.base
          x.1.scheme.sheaf hV t) =
      Stacks.Topology.ambientSection (f ≫ y.1.specialMap).toLRSHom.toShHom.hom.base
        y.1.scheme.sheaf hV' ((a.map.toLRSHom.toShHom.hom.c.app (op W)).hom t) :=
  Scheme.liftToSheafHom_ambientSection f a.special_compat _ hV hV' t

/-- A morphism of deformations of `Y` over the map `k[M] ⟶ k[N]` of `g : M ⟶ N` (read through
identifications of the bases with `k[M]`, `k[N]`) is a morphism over `Spec k`. -/
theorem SchemeDeformationCategory.map_comp_rebase_toBase_comp_squareZeroStructureSpecMap
    {P Q : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
    (eP : P.base = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
    (eQ : Q.base = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj N) (b : P ⟶ Q) {g : M ⟶ N}
    (hfac : b.base = eqToHom eP ≫ (squareZeroExtensionArtinian.{u, u, u} Λ k).map g ≫
      eqToHom eQ.symm) :
    b.map ≫ (P.rebase eP).toBase ≫ squareZeroStructureSpecMap M =
      (Q.rebase eQ).toBase ≫ squareZeroStructureSpecMap N := by
  obtain ⟨BP, SP, qP, hqP, iP, hiP⟩ := P
  obtain ⟨BQ, SQ, qQ, hqQ, iQ, hiQ⟩ := Q
  dsimp only at eP eQ
  subst eP eQ
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id] at hfac
  have hw := b.cartesian.w
  rw [hfac] at hw
  simp only [SchemeDeformationCategory.rebase_toBase, eqToHom_refl, Category.comp_id]
  rw [← baseSpecMap_comp_squareZeroStructureSpecMap g]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ squareZeroStructureSpecMap M) hw).trans (Category.assoc _ _ _))

variable {a} in
/-- A morphism of deformations of `Y` over the map `k[M] ⟶ k[N]` of `g : M ⟶ N` is a morphism over
`Spec k`. -/
theorem map_comp_schemeMorphismPushStructure {g : M ⟶ N}
    (ha : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)).IsHomLift
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).map g) a) :
    a.map ≫ schemeMorphismPushStructure pY x = schemeMorphismPushStructure pY y :=
  SchemeDeformationCategory.map_comp_rebase_toBase_comp_squareZeroStructureSpecMap x.2 y.2 a
    (IsHomLift.fac' (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).map g) a)

variable {a} in
/-- **The induced map is a map of `k`-algebras**: it carries the `k`-algebra structure of
`f⁻¹𝒪_{Y'_x}` to the one of `f⁻¹𝒪_{Y'_y}`, for a morphism `a` over the map `k[M] ⟶ k[N]` of some
`g : M ⟶ N`. -/
theorem schemeMorphismPushBase_comp_sourceIdealTransition {g : M ⟶ N}
    (ha : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)).IsHomLift
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).map g) a) :
    schemeMorphismPushBase f pY x ≫ sourceIdealTransition f a = schemeMorphismPushBase f pY y := by
  have hp := map_comp_schemeMorphismPushStructure ha
  have hf : (f ≫ y.1.specialMap) ≫ schemeMorphismPushStructure pY y =
      f ≫ x.1.specialMap ≫ schemeMorphismPushStructure pY x := by
    rw [← hp, ← a.special_compat]
    simp only [Category.assoc]
  have h2 : Scheme.liftSourceBaseMap (f ≫ y.1.specialMap) x.1.specialMap
      (schemeMorphismPushStructure pY y) (schemeMorphismPushStructure pY x) f hf ≫
        sourceIdealTransition f a =
      Scheme.liftTargetBaseMap (f ≫ y.1.specialMap) (schemeMorphismPushStructure pY y) :=
    (Scheme.liftCondTwo_iff _ _ _ _ f hf _).2 ((congrArg (· ≫ _)
      (Scheme.homOver_liftToSheafHom _ _)).trans ((Category.assoc _ _ _).trans
        (congrArg (fun t => Scheme.liftTargetProjection (f ≫ y.1.specialMap) ≫
          t.toLRSHom.toShHom) hp)))
  let e := eqToHom (congrArg
      (fun t : X ⟶ baseSpec (residueFieldBase Λ k) =>
        (TopCat.Sheaf.pullback CommRingCat.{u} t.toLRSHom.toShHom.hom.base).obj
          (baseSpec (residueFieldBase Λ k)).toRingedSpace.sheaf)
        ((Category.assoc _ _ _).trans
          (congrArg (f ≫ ·) (specialMap_comp_schemeMorphismPushStructure pY y))).symm)
  have hx : schemeMorphismPushBase f pY x = e ≫
      Scheme.liftSourceBaseMap (f ≫ y.1.specialMap) x.1.specialMap
        (schemeMorphismPushStructure pY y) (schemeMorphismPushStructure pY x) f hf := by
    rw [schemeMorphismPushBase, Scheme.liftSourceBaseMap, eqToHom_trans_assoc]
    rfl
  have hc := Stacks.SheafOfModules.inverseImageCompIso_hom_comp
    (Scheme.liftTargetProjection (f ≫ y.1.specialMap))
    (schemeMorphismPushStructure pY y).toLRSHom.toShHom
  rw [AlgebraicGeometry.RingedSpace.ringedSpaceStructureMap_inverseImageProjection] at hc
  have hc' := (congrArg (_ ≫ ·) (Category.comp_id _)).symm.trans hc
  have hy : schemeMorphismPushBase f pY y = e ≫
      Scheme.liftTargetBaseMap (f ≫ y.1.specialMap) (schemeMorphismPushStructure pY y) :=
    congrArg (e ≫ ·) hc'
  exact ((congrArg (· ≫ sourceIdealTransition f a) hx).trans
    ((Category.assoc _ _ _).trans (congrArg (e ≫ ·) h2))).trans hy.symm

end Deformation.Examples

end
