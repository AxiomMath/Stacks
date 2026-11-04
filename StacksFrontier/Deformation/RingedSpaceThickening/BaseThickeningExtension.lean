module

public import StacksFrontier.Deformation.RingedSpaceThickening.CompatibleThickeningMorphism
public import StacksFrontier.Deformation.RingedSpaceThickening.SquareZeroAlgebraExtensionClassification
public import StacksFrontier.Deformation.ToposThickening.SquareZeroDerivedObstruction
public import StacksFrontier.Topology.Sheaves.RingedSpace.ThickeningTrivialization

/-!
# The extension `𝒪_{S'}` of `𝒪_S` by `𝒥 = Ker(t^♯)` and its class `ξ` (Stacks 0GQ3)

Let `t : (S, 𝒪_S) ⟶ (S', 𝒪_{S'})` be a first order thickening of ringed spaces. **Stacks 0GQ3**
uses the element `ξ ∈ Ext¹_{𝒪_S}(𝖭𝖫_{S/S'}, 𝒥)` corresponding, via **Stacks 0GPZ** applied to
`t` and the `𝒪_S`-module `𝒥 = Ker(t^♯)`, to the extension `0 ⟶ 𝒥 ⟶ 𝒪_{S'} ⟶ 𝒪_S ⟶ 0` of
`t⁻¹𝒪_{S'}`-algebras. This file constructs `𝒥`, that extension and `ξ`.

The underlying spaces of `S` and `S'` are homeomorphic but not identified, so `𝒪_{S'}` is read on
`S` as `t⁻¹𝒪_{S'}`, and `t^♯` as the structure map `t⁻¹𝒪_{S'} ⟶ 𝒪_S`. Because `t` is a
homeomorphism, the unit `𝒪_{S'} ⟶ t_*t⁻¹𝒪_{S'}` is an isomorphism (`isIso_inverseImageUnit`), so
that on the open `t⁻¹V` the map `t⁻¹𝒪_{S'} ⟶ 𝒪_S` is `t^♯ : 𝒪_{S'}(V) ⟶ 𝒪_S(t⁻¹V)`; this is how
surjectivity and the square-zero condition of `t^♯` are transported
(`isLocallySurjective_structureRingMap`, `structureRingMap_mul_eq_zero`).

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.baseIdealModule`: `𝒥 = Ker(t^♯)` as a sheaf of
  `𝒪_S`-modules.
* `AlgebraicGeometry.RingedSpaceThickening.baseExtension`: the extension
  `0 ⟶ 𝒥 ⟶ 𝒪_{S'} ⟶ 𝒪_S ⟶ 0` of `t⁻¹𝒪_{S'}`-algebras.
* `AlgebraicGeometry.RingedSpaceThickening.baseClass`: its class `ξ`, the image of
  `baseExtension` under the bijection of **Stacks 0GPZ**.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.subsingleton_compatibleMorphism`: an `S'`-morphism
  `X' ⟶ S'` compatible with `f` and `c` is unique if it exists.

## References

* [Stacks Project, Tag 0GQ3](https://stacks.math.columbia.edu/tag/0GQ3)
* [Stacks Project, Tag 0GPZ](https://stacks.math.columbia.edu/tag/0GPZ)
* [Stacks Project, Tag 08U7](https://stacks.math.columbia.edu/tag/08U7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

/-- Pushforward of sheaves of commutative rings along a homeomorphism is an equivalence. -/
def sheafPushforwardEquivOfIso {X Y : TopCat.{u}} (h : X ≅ Y) :
    TopCat.Sheaf CommRingCat.{u} X ≌ TopCat.Sheaf CommRingCat.{u} Y :=
  CategoryTheory.Equivalence.mk (TopCat.Sheaf.pushforward CommRingCat.{u} h.hom)
    (TopCat.Sheaf.pushforward CommRingCat.{u} h.inv)
    (Functor.sheafPushforwardContinuousComp'
      ((Opens.mapComp h.hom h.inv).symm ≪≫ Opens.mapIso _ _ h.hom_inv_id ≪≫ Opens.mapId X)
      CommRingCat.{u} (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X)).symm
    (Functor.sheafPushforwardContinuousComp'
      ((Opens.mapComp h.inv h.hom).symm ≪≫ Opens.mapIso _ _ h.inv_hom_id ≪≫ Opens.mapId Y)
      CommRingCat.{u} (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y))

/-- Pushforward of sheaves of commutative rings along a homeomorphism is an equivalence. -/
instance isEquivalence_sheafPushforward {X Y : TopCat.{u}} (h : X ⟶ Y) [IsIso h] :
    (TopCat.Sheaf.pushforward CommRingCat.{u} h).IsEquivalence :=
  (sheafPushforwardEquivOfIso (asIso h)).isEquivalence_functor

variable {S S' : RingedSpace.{u, u}} (t : S ⟶ S')

/-- The unit `𝒪_{S'} ⟶ t_*t⁻¹𝒪_{S'}` of `t⁻¹ ⊣ t_*` on sheaves of commutative rings. -/
abbrev inverseImageUnit : S'.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} t.hom.base).obj
    (inverseImageBaseRing t) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} t.hom.base).unit.app S'.sheaf

/-- The unit `𝒪_{S'} ⟶ t_*t⁻¹𝒪_{S'}` is an isomorphism when `t` is a homeomorphism. -/
instance isIso_inverseImageUnit [IsIso t.hom.base] : IsIso (inverseImageUnit t) := by
  have := isEquivalence_sheafPushforward t.hom.base
  exact NatIso.isIso_app_of_isIso
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} t.hom.base).unit S'.sheaf

/-- `𝒪_{S'} ⟶ t_*t⁻¹𝒪_{S'} ⟶ t_*𝒪_S` is `t^♯`: the structure map is the transpose of `t^♯`. -/
theorem inverseImageUnit_comp_structureRingMap :
    inverseImageUnit t ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} t.hom.base).map
      (structureRingMap t) = ObjectProperty.homMk t.hom.c :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} t.hom.base).homEquiv_unit
    _ _ _).symm.trans (Equiv.apply_symm_apply _ _)

/-- On sections over `t⁻¹V`, the structure map `t⁻¹𝒪_{S'} ⟶ 𝒪_S` after the unit is `t^♯`. -/
theorem structureRingMap_app_inverseImageUnit (V : Opens S'.carrier) (x : S'.presheaf.obj (op V)) :
    (structureRingMap t).hom.app (op ((Opens.map t.hom.base).obj V))
      ((inverseImageUnit t).hom.app (op V) x) = t.hom.c.app (op V) x :=
  congrArg (fun k : S'.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} t.hom.base).obj S.sheaf =>
    k.hom.app (op V) x) (inverseImageUnit_comp_structureRingMap t)

/-- Every open of `S` is the preimage of an open of `S'` when `t` is a homeomorphism. -/
theorem exists_map_obj_eq [IsIso t.hom.base] (U : Opens S.carrier) :
    ∃ V : Opens S'.carrier, (Opens.map t.hom.base).obj V = U :=
  ⟨(Opens.map (inv t.hom.base)).obj U, by
    rw [← Opens.map_comp_obj, IsIso.hom_inv_id, Opens.map_id_obj]⟩

/-- The unit `𝒪_{S'}(V) ⟶ (t⁻¹𝒪_{S'})(t⁻¹V)` is bijective when `t` is a homeomorphism. -/
theorem bijective_inverseImageUnit_app [IsIso t.hom.base] (V : Opens S'.carrier) :
    Function.Bijective ((inverseImageUnit t).hom.app (op V)) := by
  have h1 := congrArg (fun k => k.hom.app (op V)) (IsIso.hom_inv_id (inverseImageUnit t))
  have h2 := congrArg (fun k => k.hom.app (op V)) (IsIso.inv_hom_id (inverseImageUnit t))
  refine ⟨fun a b h => ?_, fun b => ⟨(inv (inverseImageUnit t)).hom.app (op V) b, ?_⟩⟩
  · exact (ConcreteCategory.congr_hom h1 a).symm.trans
      ((congrArg ((inv (inverseImageUnit t)).hom.app (op V)) h).trans
        (ConcreteCategory.congr_hom h1 b))
  · exact ConcreteCategory.congr_hom h2 b

/-- `t⁻¹𝒪_{S'} ⟶ 𝒪_S` is locally surjective for a thickening `t`. -/
theorem isLocallySurjective_structureRingMap (ht : IsThickening t) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology S.carrier)
      (structureRingMap t).hom := by
  have : IsIso t.hom.base := ht.1
  have hc := (TopCat.Presheaf.isLocallySurjective_iff _).1
    (isLocallySurjective_comorphism_of_isThickening t ht)
  refine (TopCat.Presheaf.isLocallySurjective_iff (structureRingMap t).hom).2 fun U s x hx => ?_
  obtain ⟨V, rfl⟩ := exists_map_obj_eq t U
  obtain ⟨W, hWV, ⟨a, ha⟩, hxW⟩ := hc V s (t.hom.base x) hx
  refine ⟨(Opens.map t.hom.base).obj W, (Opens.map t.hom.base).monotone hWV,
    ⟨(inverseImageUnit t).hom.app (op W) a, ?_⟩, hxW⟩
  exact (structureRingMap_app_inverseImageUnit t W a).trans ha

/-- The kernel of `t⁻¹𝒪_{S'} ⟶ 𝒪_S` has square zero for a first order thickening `t`. -/
theorem structureRingMap_mul_eq_zero (ht : IsFirstOrderThickening t) (U : (Opens S.carrier)ᵒᵖ)
    (a b : (inverseImageBaseRing t).obj.obj U) (ha : (structureRingMap t).hom.app U a = 0)
    (hb : (structureRingMap t).hom.app U b = 0) : a * b = 0 := by
  have : IsIso t.hom.base := ht.1.1
  induction U using Opposite.rec with | op U => ?_
  obtain ⟨V, rfl⟩ := exists_map_obj_eq t U
  obtain ⟨x, rfl⟩ := (bijective_inverseImageUnit_app t V).2 a
  obtain ⟨y, rfl⟩ := (bijective_inverseImageUnit_app t V).2 b
  have hI := ht.2 V
  rw [show (2 : ℕ) = 1 + 1 from rfl, Submodule.pow_succ, Submodule.pow_one] at hI
  have hxy : x * y = 0 := Ideal.mem_bot.1 (hI.le (Ideal.mul_mem_mul
    ((structureRingMap_app_inverseImageUnit t V x).symm.trans ha)
    ((structureRingMap_app_inverseImageUnit t V y).symm.trans hb)))
  have h0 := congrArg ((inverseImageUnit t).hom.app (op V)).hom hxy
  rwa [map_mul, map_zero] at h0

/-! ### The ideal `𝒥 = Ker(t^♯)` and the extension `𝒪_{S'}` -/

variable {t} (ht : IsFirstOrderThickening t)

/-- **`𝒥 = Ker(t^♯)`**, as a sheaf of `𝒪_S`-modules: the kernel of `t⁻¹𝒪_{S'} ⟶ 𝒪_S`, which has
square zero and therefore descends along the surjection to an `𝒪_S`-module. -/
def baseIdealModule : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology S.carrier) S.sheaf) :=
  Deformation.ComplexLift.squareZeroIdeal.{u, u, u} (structureRingMap t)
    (isLocallySurjective_structureRingMap t ht.1) (structureRingMap_mul_eq_zero t ht)

/-- The identification of `𝒥` with the kernel of `t⁻¹𝒪_{S'} ⟶ 𝒪_S`, read as an isomorphism of
`t⁻¹𝒪_{S'}`-modules. -/
abbrev baseIdealIso :=
  Deformation.ComplexLift.restrictSquareZeroIdealIso.{u, u, u} (structureRingMap t)
    (isLocallySurjective_structureRingMap t ht.1) (structureRingMap_mul_eq_zero t ht)

variable (t) in
/-- A section of the kernel of `t⁻¹𝒪_{S'} ⟶ 𝒪_S` lies in the kernel module. -/
theorem mem_baseKernel (U : (Opens S.carrier)ᵒᵖ)
    (a : Stacks.Sites.Conormal.kernelIdeal (structureRingMap t).hom U) :
    (show (inverseImageBaseRing t).obj.obj U from a.1) ∈
      (SheafOfModules.kerSubmodule
        (Deformation.ComplexLift.structureModuleMap (structureRingMap t))).obj U :=
  (SheafOfModules.mem_kerSubmodule _ U _).2
    ((Deformation.ComplexLift.structureModuleMap_val_app (structureRingMap t) U _).trans a.2)

variable (t) in
/-- A section of the kernel of `t⁻¹𝒪_{S'} ⟶ 𝒪_S`, as a section of the kernel module. -/
def baseKernelSection (U : (Opens S.carrier)ᵒᵖ) :
    Stacks.Sites.Conormal.kernelIdeal (structureRingMap t).hom U →+
      (Deformation.ComplexLift.kernelModule (structureRingMap t)).val.obj U where
  toFun a := ⟨a.1, mem_baseKernel t U a⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- **The identification of `Ker(t⁻¹𝒪_{S'} ⟶ 𝒪_S)` with `𝒥`**, on sections. -/
def baseIdealRestriction :
    Stacks.Sites.Conormal.IdealRestriction.{u, u, u, u} (structureRingMap t)
      (baseIdealModule ht) where
  app U := ((baseIdealIso ht).inv.val.app U).hom.toAddMonoidHom.comp (baseKernelSection t U)
  app_smul U r a := ((baseIdealIso ht).inv.val.app U).hom.map_smul r (baseKernelSection t U a)
  app_map {U _} i a :=
    PresheafOfModules.naturality_apply (baseIdealIso ht).inv.val i (baseKernelSection t U a)

/-- The identification of `Ker(t⁻¹𝒪_{S'} ⟶ 𝒪_S)` with `𝒥` is bijective on sections. -/
theorem baseIdealRestriction_bijective (U : (Opens S.carrier)ᵒᵖ) :
    Function.Bijective ((baseIdealRestriction ht).app U) := by
  have h1 := congrArg (fun k => k.val.app U) (baseIdealIso ht).hom_inv_id
  have h2 := congrArg (fun k => k.val.app U) (baseIdealIso ht).inv_hom_id
  refine ⟨fun a b h => ?_, fun m => ?_⟩
  · have h' : baseKernelSection t U a = baseKernelSection t U b :=
      (ConcreteCategory.congr_hom h2 _).symm.trans
        ((congrArg ((baseIdealIso ht).hom.val.app U) h).trans (ConcreteCategory.congr_hom h2 _))
    have h'' := congrArg Subtype.val h'
    exact Subtype.ext h''
  · set k := (baseIdealIso ht).hom.val.app U m
    have hk : (structureRingMap t).hom.app U k.1 = 0 :=
      (Deformation.ComplexLift.structureModuleMap_val_app (structureRingMap t) U _).symm.trans
        ((SheafOfModules.mem_kerSubmodule _ U _).1 k.2)
    exact ⟨⟨k.1, hk⟩, ConcreteCategory.congr_hom h1 m⟩

/-- **The sections of `𝒥` are the kernel of `t^♯`**: over the open `t⁻¹V` of `S`, the sections
of `𝒥` are the sections of `𝒪_{S'}` over `V` killed by `t^♯ : 𝒪_{S'}(V) ⟶ 𝒪_S(t⁻¹V)`. -/
def baseIdealSectionsEquiv (V : Opens S'.carrier) :
    RingHom.ker (t.hom.c.app (op V)).hom ≃
      (baseIdealModule ht).val.obj (op ((Opens.map t.hom.base).obj V)) := by
  haveI : IsIso t.hom.base := ht.1.1
  refine Equiv.ofBijective (fun x => (baseIdealRestriction ht).app _
    ⟨(inverseImageUnit t).hom.app (op V) x.1,
      (structureRingMap_app_inverseImageUnit t V x.1).trans x.2⟩) ⟨fun x y h => ?_, fun m => ?_⟩
  · exact Subtype.ext ((bijective_inverseImageUnit_app t V).1
      (congrArg Subtype.val ((baseIdealRestriction_bijective ht _).1 h)))
  · obtain ⟨a, rfl⟩ := (baseIdealRestriction_bijective ht _).2 m
    obtain ⟨x, hx⟩ := (bijective_inverseImageUnit_app t V).2 a.1
    refine ⟨⟨x, (structureRingMap_app_inverseImageUnit t V x).symm.trans ?_⟩, ?_⟩
    · rw [hx]
      exact a.2
    · exact congrArg ((baseIdealRestriction ht).app _) (Subtype.ext hx)

/-- `baseIdealSectionsEquiv` sends a section `x` of `Ker(t^♯)` to the image under
`baseIdealRestriction` of its pullback along `inverseImageUnit`. -/
theorem baseIdealSectionsEquiv_apply (V : Opens S'.carrier)
    (x : RingHom.ker (t.hom.c.app (op V)).hom) :
    baseIdealSectionsEquiv ht V x = (baseIdealRestriction ht).app _
      ⟨(inverseImageUnit t).hom.app (op V) x.1,
        (structureRingMap_app_inverseImageUnit t V x.1).trans x.2⟩ :=
  rfl

/-- `baseIdealSectionsEquiv` is linear over `𝒪_{S'}(V)`, acting on `𝒥` through `t^♯`. -/
theorem baseIdealSectionsEquiv_mul (V : Opens S'.carrier) (r : S'.presheaf.obj (op V))
    (x : RingHom.ker (t.hom.c.app (op V)).hom) :
    baseIdealSectionsEquiv ht V (r • x) =
      (show (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology S.carrier) S.sheaf).obj.obj
          (op ((Opens.map t.hom.base).obj V)) from t.hom.c.app (op V) r) •
        baseIdealSectionsEquiv ht V x := by
  rw [baseIdealSectionsEquiv_apply, baseIdealSectionsEquiv_apply]
  have h := (baseIdealRestriction ht).app_smul _ ((inverseImageUnit t).hom.app (op V) r)
    ⟨(inverseImageUnit t).hom.app (op V) x.1,
        (structureRingMap_app_inverseImageUnit t V x.1).trans x.2⟩
  refine Eq.trans ?_ (h.trans ?_)
  · congr 1
    exact Subtype.ext (map_mul _ _ _)
  · congr 1
    exact structureRingMap_app_inverseImageUnit t V r

/-- `baseIdealSectionsEquiv` commutes with restriction. -/
theorem baseIdealSectionsEquiv_map {V W : Opens S'.carrier} (h : W ≤ V)
    (x : RingHom.ker (t.hom.c.app (op V)).hom) :
    baseIdealSectionsEquiv ht W ⟨S'.presheaf.map (homOfLE h).op x.1, by
      rw [RingHom.mem_ker, ← ConcreteCategory.comp_apply, t.hom.c.naturality,
        ConcreteCategory.comp_apply, RingHom.mem_ker.1 x.2, map_zero]⟩ =
      (baseIdealModule ht).val.map ((Opens.map t.hom.base).map (homOfLE h)).op
        (baseIdealSectionsEquiv ht V x) := by
  rw [baseIdealSectionsEquiv_apply, baseIdealSectionsEquiv_apply]
  refine Eq.trans ?_
    ((baseIdealRestriction ht).app_map ((Opens.map t.hom.base).map (homOfLE h)).op _)
  congr 1
  exact Subtype.ext (NatTrans.naturality_apply (inverseImageUnit t).hom (homOfLE h).op x.1)

/-- **The extension `0 ⟶ 𝒥 ⟶ 𝒪_{S'} ⟶ 𝒪_S ⟶ 0` of `t⁻¹𝒪_{S'}`-algebras**: the structure sheaf
of `S'`, read on `S` as `t⁻¹𝒪_{S'}` with its identity algebra structure, reducing to `𝒪_S`
along `t^♯`, with kernel `𝒥`. -/
def baseExtension : SquareZeroAlgebraExtension t (baseIdealModule ht) where
  sheaf := inverseImageBaseRing t
  base := 𝟙 _
  reduction := structureRingMap t
  base_comp_reduction := Category.id_comp _
  reduction_surjective := isLocallySurjective_structureRingMap t ht.1
  ideal := baseIdealRestriction ht
  ideal_bijective := baseIdealRestriction_bijective ht

/-- The inclusion `𝒥 ⟶ t⁻¹𝒪_{S'}` on sections over `t⁻¹V`: a section of `𝒪_{S'}` over `V` killed
by `t^♯`, read in `t⁻¹𝒪_{S'}`. -/
theorem baseExtension_incl (V : Opens S'.carrier) (x : RingHom.ker (t.hom.c.app (op V)).hom) :
    (baseExtension ht).incl (op ((Opens.map t.hom.base).obj V)) (baseIdealSectionsEquiv ht V x) =
      (inverseImageUnit t).hom.app (op V) x.1 :=
  (baseExtension ht).incl_ideal _ ⟨_, _⟩

attribute [local instance] HasDerivedCategory.standard in
/-- **The class `ξ ∈ Ext¹_{𝒪_S}(𝖭𝖫_{S/S'}, 𝒥)` of the extension `𝒪_{S'}` of `𝒪_S` by `𝒥`**: the
image of `baseExtension` under the bijection of **Stacks 0GPZ** for `t` and `𝒥`. -/
def baseClass : extOneNaiveCotangent t (baseIdealModule ht) :=
  SquareZeroAlgebraExtension.isomorphismClassesEquivExt t (baseIdealModule ht)
    (Quotient.mk _ (baseExtension ht))

/-- **An `S'`-morphism `X' ⟶ S'` compatible with `f` and `c` is unique when it exists**: it is a
morphism over `S'`, and the structure map `𝒪_{S'} ⟶ t_*t⁻¹𝒪_{S'}` is an isomorphism because
`t` is a homeomorphism. -/
instance subsingleton_compatibleMorphism {X : RingedSpace.{u, u}} {f : X ⟶ S}
    {G : SheafOfModules.{u} (structureSheafRing X)} (Q : SquareZeroAlgebraExtension (f ≫ t) G)
    (c : baseIdealModule ht ⟶ (modulePushforward f).obj G) :
    Subsingleton (CompatibleMorphism (baseExtension ht) Q c) := by
  have : IsIso t.hom.base := ht.1.1
  constructor
  rintro ⟨h₁, -, hb₁, -⟩ ⟨h₂, -, hb₂, -⟩
  have hu : (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} t.hom.base).homEquiv _ _
      (baseExtension ht).base = inverseImageUnit t := by
    refine ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} t.hom.base).homEquiv_unit
      _ _ _).trans ?_
    exact (congrArg (inverseImageUnit t ≫ ·) (CategoryTheory.Functor.map_id _ _)).trans
      (Category.comp_id _)
  rw [hu] at hb₁ hb₂
  obtain rfl : h₁ = h₂ := (TopCat.Sheaf.pushforward CommRingCat.{u} t.hom.base).map_injective
    ((cancel_epi (inverseImageUnit t)).1 (hb₁.trans hb₂.symm))
  rfl

end AlgebraicGeometry.RingedSpaceThickening

end
