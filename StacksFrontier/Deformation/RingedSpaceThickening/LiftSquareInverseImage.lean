module

public import StacksFrontier.Deformation.ToposThickening.LiftingBetweenThickenings
public import StacksFrontier.Topology.Sheaves.Functors.Pullback.LocalUnitSections
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-!
# The inverse image of one layer of a lifting diagram along a continuous map

Let `p : Y ⟶ X` be a continuous map of topological spaces and let `L` be one layer
`Deformation.ToposThickening.LiftSquare` of the diagram of Stacks 08U8 on `X`: a first order
thickening `𝒪_{B'} ⟶ 𝒪_B` of a base, a first order thickening `𝒪' ⟶ 𝒪` of the source over it,
and the module `𝒢` identified with the ideal of the source thickening. Its inverse image along
`p` is again such a layer on `Y`: the sheaves of rings are `p⁻¹𝒪_{B'}`, `p⁻¹𝒪_B`, `p⁻¹𝒪'`,
`p⁻¹𝒪`, the module is `p⁻¹𝒢`, and the inclusion of the ideal is the inverse image of the
inclusion of `𝒢`. This is the step "pull everything back to `X₂`" of the proof of Stacks 08U8.

## Main definitions

* `Deformation.ToposThickening.LiftSquare.inverseImage`: the inverse image of a layer.

## Main results

* `Deformation.ToposThickening.isLocallySurjective_inverseImage_map`: the inverse image of a
  locally surjective morphism of sheaves of commutative rings is locally surjective.
* `Deformation.ToposThickening.mul_eq_zero_of_inverseImage`: the inverse image of a morphism of
  sheaves of commutative rings with square-zero kernel has square-zero kernel.
* `Deformation.ToposThickening.LiftSquare.inverseImage_incl_moduleUnit`: the inclusion of the
  ideal of the inverse image carries the induced section of a section `m` of `𝒢` to the induced
  section of the image of `m`.

## Implementation notes

Inverse image is exact, and all the properties of a layer are statements about sections, which
the inverse image does not describe. They are proved locally: by
`Stacks.Topology.exists_restrict_eq_unit` and `Stacks.Topology.exists_restrict_eq_moduleUnit`
every section of an inverse image is near every point the restriction of a section induced from
the original sheaf, on which every map of the layer is computed by the unit of the adjunction,
and by `Stacks.Topology.exists_restrict_eq_of_unit_eq` an identity between induced sections near
a point descends to an identity near its image.

## References

* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.SheafOfModules (underlyingRingSheaf inverseImageModule
  inverseImageModuleUnit inverseImageRingHom inverseImageAdjunction)

universe u

namespace Deformation.ToposThickening

section Units

variable {X Y : TopCat.{u}} (p : Y ⟶ X)

/-- The inverse image of sheaves of commutative rings along `p`, as a functor between the
categories of sheaves on the two sites of opens. It is `TopCat.Sheaf.pullback`, with its type
spelled through `CategoryTheory.Sheaf` so that the projections of its values are type-correct
without unfolding `TopCat.Sheaf`. -/
abbrev ringPullback : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u} ⥤
    Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u} :=
  TopCat.Sheaf.pullback CommRingCat.{u} p

/-- The direct image of sheaves of commutative rings along `p`, spelled as `ringPullback`. -/
abbrev ringPushforward : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u} ⥤
    Sheaf (Opens.grothendieckTopology X) CommRingCat.{u} :=
  TopCat.Sheaf.pushforward CommRingCat.{u} p

/-- The adjunction `p⁻¹ ⊣ p_*` for sheaves of commutative rings. -/
abbrev ringAdjunction : ringPullback p ⊣ ringPushforward p :=
  TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} p

/-- The section of `p⁻¹F` over `p⁻¹V` induced by a section of `F` over `V`: the unit of the
adjunction `p⁻¹ ⊣ p_*` for sheaves of commutative rings. -/
abbrev ringUnit (F : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) (V : Opens X) :
    F.obj.obj (op V) ⟶ ((ringPullback p).obj F).obj.obj (op ((Opens.map p).obj V)) :=
  ((ringAdjunction p).unit.app F).hom.app (op V)

/-- The inverse image of opens is monotone. -/
theorem opensMap_le {V V' : Opens X} (h : V' ≤ V) : (Opens.map p).obj V' ≤ (Opens.map p).obj V :=
  fun _ hz => h hz

variable (F : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})

/-- `Stacks.Topology.exists_restrict_eq_unit` for sheaves of commutative rings. -/
theorem exists_restrict_eq_ringUnit {U : Opens Y} (s : ((ringPullback p).obj F).obj.obj (op U))
    (y : Y) (hy : y ∈ U) :
    ∃ (V : Opens X) (_ : p y ∈ V) (t : F.obj.obj (op V)) (W : Opens Y) (_ : y ∈ W)
      (hWU : W ≤ U) (hWV : W ≤ (Opens.map p).obj V),
      ((ringPullback p).obj F).obj.map (homOfLE hWU).op s =
        ((ringPullback p).obj F).obj.map (homOfLE hWV).op (ringUnit p F V t) :=
  Stacks.Topology.exists_restrict_eq_unit p F s y hy

/-- `Stacks.Topology.exists_restrict_eq_of_unit_eq` for sheaves of commutative rings. -/
theorem exists_restrict_eq_of_ringUnit_eq {V : Opens X} (t t' : F.obj.obj (op V)) {W : Opens Y}
    (y : Y) (hy : y ∈ W) (hWV : W ≤ (Opens.map p).obj V)
    (h : ((ringPullback p).obj F).obj.map (homOfLE hWV).op (ringUnit p F V t) =
      ((ringPullback p).obj F).obj.map (homOfLE hWV).op (ringUnit p F V t')) :
    ∃ (V' : Opens X) (_ : p y ∈ V') (hV' : V' ≤ V),
      F.obj.map (homOfLE hV').op t = F.obj.map (homOfLE hV').op t' :=
  Stacks.Topology.exists_restrict_eq_of_unit_eq p F t t' y hy hWV h

/-- `Stacks.Topology.sheaf_eq_of_locally_eq` for sheaves of commutative rings on a site of
opens. -/
theorem ringSheaf_eq_of_locally_eq {Z : TopCat.{u}}
    (G : Sheaf (Opens.grothendieckTopology Z) CommRingCat.{u}) {U : Opens Z}
    (s t : G.obj.obj (op U))
    (h : ∀ x ∈ U, ∃ (W : Opens Z) (_ : x ∈ W) (hWU : W ≤ U),
      G.obj.map (homOfLE hWU).op s = G.obj.map (homOfLE hWU).op t) : s = t :=
  Stacks.Topology.sheaf_eq_of_locally_eq (Z := Z) G s t h

/-- The induced sections commute with the inverse image of a morphism. -/
theorem ringUnit_naturality {G : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}} (φ : F ⟶ G)
    (V : Opens X) (x : F.obj.obj (op V)) :
    ((ringPullback p).map φ).hom.app (op ((Opens.map p).obj V)) (ringUnit p F V x) =
      ringUnit p G V (φ.hom.app (op V) x) :=
  (congrArg (fun k => k.hom.app (op V) x) ((ringAdjunction p).unit.naturality φ)).symm

/-- **The adjoint transpose of a morphism into a direct image, on induced sections**: it is the
morphism itself. -/
theorem ringAdjunction_homEquiv_symm_ringUnit
    {H : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}} (ψ : F ⟶ (ringPushforward p).obj H)
    (V : Opens X) (x : F.obj.obj (op V)) :
    (((ringAdjunction p).homEquiv _ _).symm ψ).hom.app (op ((Opens.map p).obj V))
        (ringUnit p F V x) = ψ.hom.app (op V) x := by
  have h := ((ringAdjunction p).homEquiv_unit (f := ((ringAdjunction p).homEquiv _ _).symm ψ))
  rw [Equiv.apply_symm_apply] at h
  exact (congrArg (fun k => k.hom.app (op V) x) h).symm

/-- The adjoint transpose of a morphism out of an inverse image, on sections: it is the
morphism evaluated at the induced section. -/
theorem ringAdjunction_homEquiv_apply {H : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}}
    (α : (ringPullback p).obj F ⟶ H) (V : Opens X) (x : F.obj.obj (op V)) :
    (((ringAdjunction p).homEquiv _ _) α).hom.app (op V) x =
      α.hom.app (op ((Opens.map p).obj V)) (ringUnit p F V x) := by
  rw [← ringAdjunction_homEquiv_symm_ringUnit, Equiv.symm_apply_apply]

/-- **Morphisms out of an inverse image are determined by their values on induced sections.** -/
theorem ringHom_ext_pullback {H : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}}
    {α β : (ringPullback p).obj F ⟶ H}
    (h : ∀ (V : Opens X) (x : F.obj.obj (op V)),
      α.hom.app (op ((Opens.map p).obj V)) (ringUnit p F V x) =
        β.hom.app (op ((Opens.map p).obj V)) (ringUnit p F V x)) : α = β := by
  apply ((ringAdjunction p).homEquiv _ _).injective
  refine sheafHom_ext _ fun V x => ?_
  obtain ⟨V⟩ := V
  rw [ringAdjunction_homEquiv_apply, ringAdjunction_homEquiv_apply]
  exact h V x

/-- Restricting twice is restricting once. -/
theorem sheaf_map_map {Z : TopCat.{u}} (G : Sheaf (Opens.grothendieckTopology Z) CommRingCat.{u})
    {U V W : Opens Z} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : G.obj.obj (op U)) :
    G.obj.map (homOfLE h₂).op (G.obj.map (homOfLE h₁).op x) =
      G.obj.map (homOfLE (h₂.trans h₁)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Restricting from an open to itself is the identity. -/
theorem sheaf_map_self {Z : TopCat.{u}} (G : Sheaf (Opens.grothendieckTopology Z) CommRingCat.{u})
    {U : Opens Z} (h : U ≤ U) (x : G.obj.obj (op U)) : G.obj.map (homOfLE h).op x = x := by
  rw [show (homOfLE h).op = 𝟙 (op U) from rfl, CategoryTheory.Functor.map_id]
  rfl

/-- The induced sections commute with restriction. -/
theorem ringUnit_restrict {V V' : Opens X} (h : V' ≤ V)
    {W : Opens Y} (hW : W ≤ (Opens.map p).obj V') (x : F.obj.obj (op V)) :
    ((ringPullback p).obj F).obj.map
        (homOfLE (hW.trans (opensMap_le p h))).op (ringUnit p F V x) =
      ((ringPullback p).obj F).obj.map (homOfLE hW).op
        (ringUnit p F V' (F.obj.map (homOfLE h).op x)) := by
  have hx : ringUnit p F V' (F.obj.map (homOfLE h).op x) =
      ((ringPullback p).obj F).obj.map ((Opens.map p).map (homOfLE h)).op
        (ringUnit p F V x) :=
    congrArg (fun k => k x) (((ringAdjunction p).unit.app F).hom.naturality (homOfLE h).op)
  rw [hx]
  exact (sheaf_map_map ((ringPullback p).obj F) (opensMap_le p h) hW _).symm

/-- Restricting twice is restricting once, for a sheaf of modules. -/
theorem module_map_map {Z : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology Z) RingCat.{u}}
    (M : SheafOfModules.{u} R) {U V W : Opens Z} (h₁ : V ≤ U) (h₂ : W ≤ V)
    (x : M.val.obj (op U)) :
    M.val.map (homOfLE h₂).op (M.val.map (homOfLE h₁).op x) =
      M.val.map (homOfLE (h₂.trans h₁)).op x := by
  rw [← PresheafOfModules.map_comp_apply]
  rfl

/-- Restricting from an open to itself is the identity, for a sheaf of modules. -/
theorem module_map_self {Z : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology Z) RingCat.{u}}
    (M : SheafOfModules.{u} R) {U : Opens Z} (h : U ≤ U) (x : M.val.obj (op U)) :
    M.val.map (homOfLE h).op x = x := by
  rw [show (homOfLE h).op = 𝟙 (op U) from rfl, PresheafOfModules.map_id]
  rfl

/-- If a section of an inverse image agrees near a point with an induced section, it does so over
any smaller open with the restriction of the induced section. -/
private theorem restrict_eq_restrict_ringUnit {U : Opens Y}
    {s : ((ringPullback p).obj F).obj.obj (op U)} {V V' : Opens X} {x : F.obj.obj (op V)}
    (hV : V' ≤ V) {W W' : Opens Y} {hWU : W ≤ U} {hWV : W ≤ (Opens.map p).obj V}
    (e : ((ringPullback p).obj F).obj.map (homOfLE hWU).op s =
      ((ringPullback p).obj F).obj.map (homOfLE hWV).op (ringUnit p F V x))
    (h₁ : W' ≤ W) (h₂ : W' ≤ (Opens.map p).obj V') :
    ((ringPullback p).obj F).obj.map (homOfLE (h₁.trans hWU)).op s =
      ((ringPullback p).obj F).obj.map (homOfLE h₂).op
        (ringUnit p F V' (F.obj.map (homOfLE hV).op x)) := by
  rw [← ringUnit_restrict p F hV h₂, ← sheaf_map_map _ hWU h₁, e, sheaf_map_map]

/-- Two sections of an inverse image are near every point the restrictions of two induced
sections over one open. -/
theorem exists_restrict_eq_ringUnit₂ {U : Opens Y}
    (s s' : ((ringPullback p).obj F).obj.obj (op U)) (y : Y) (hy : y ∈ U) :
    ∃ (V : Opens X) (_ : p y ∈ V) (t t' : F.obj.obj (op V)) (W : Opens Y) (_ : y ∈ W)
      (hWU : W ≤ U) (hWV : W ≤ (Opens.map p).obj V),
      ((ringPullback p).obj F).obj.map (homOfLE hWU).op s =
          ((ringPullback p).obj F).obj.map (homOfLE hWV).op (ringUnit p F V t) ∧
        ((ringPullback p).obj F).obj.map (homOfLE hWU).op s' =
          ((ringPullback p).obj F).obj.map (homOfLE hWV).op (ringUnit p F V t') := by
  obtain ⟨V₁, hV₁, t₁, W₁, hW₁, hW₁U, hW₁V, e₁⟩ := exists_restrict_eq_ringUnit p F s y hy
  obtain ⟨V₂, hV₂, t₂, W₂, hW₂, hW₂U, hW₂V, e₂⟩ := exists_restrict_eq_ringUnit p F s' y hy
  have hWV : W₁ ⊓ W₂ ≤ (Opens.map p).obj (V₁ ⊓ V₂) := fun z hz => ⟨hW₁V hz.1, hW₂V hz.2⟩
  refine ⟨V₁ ⊓ V₂, ⟨hV₁, hV₂⟩, F.obj.map (homOfLE inf_le_left).op t₁,
    F.obj.map (homOfLE inf_le_right).op t₂, W₁ ⊓ W₂, ⟨hW₁, hW₂⟩,
    inf_le_left.trans hW₁U, hWV, restrict_eq_restrict_ringUnit p F inf_le_left e₁ inf_le_left hWV,
    restrict_eq_restrict_ringUnit p F inf_le_right e₂ inf_le_right hWV⟩

/-- **The inverse image of a locally surjective morphism of sheaves of commutative rings is
locally surjective.** -/
theorem isLocallySurjective_inverseImage_map
    {G : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}} (φ : F ⟶ G)
    (hφ : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ.hom) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y) ((ringPullback p).map φ).hom := by
  constructor
  intro U s y hy
  obtain ⟨V, hV, t, W, hyW, hWU, hWV, e⟩ := exists_restrict_eq_ringUnit p G s y hy
  obtain ⟨V', iV', ⟨a, ha⟩, hV'⟩ := hφ.imageSieve_mem t (p y) hV
  have hV'V : V' ≤ V := iV'.le
  let PF := (ringPullback p).obj F
  let PG := (ringPullback p).obj G
  refine ⟨W ⊓ (Opens.map p).obj V', homOfLE (inf_le_left.trans hWU),
    ⟨PF.obj.map (homOfLE inf_le_right).op (ringUnit p F V' a), ?_⟩, ⟨hyW, hV'⟩⟩
  show ((ringPullback p).map φ).hom.app _
      (PF.obj.map (homOfLE inf_le_right).op (ringUnit p F V' a)) = _
  rw [sheafHom_naturality_apply, ringUnit_naturality]
  show PG.obj.map _ (ringUnit p G V' (φ.hom.app (op V') a)) = _
  rw [ha]
  exact (restrict_eq_restrict_ringUnit p G hV'V e inf_le_left inf_le_right).symm

/-- If a section killed by the inverse image of `φ` agrees near a point with an induced section,
then the induced section is killed by `φ` on a neighbourhood of the image of the point. -/
private theorem exists_restrict_map_eq_zero
    {G : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
    (φ : F ⟶ G) {U : Opens Y} {c : ((ringPullback p).obj F).obj.obj (op U)}
    (hc : ((ringPullback p).map φ).hom.app (op U) c = 0) {V : Opens X} {x : F.obj.obj (op V)}
    {W : Opens Y} {y : Y} (hyW : y ∈ W) {hWU : W ≤ U} {hWV : W ≤ (Opens.map p).obj V}
    (hcx : ((ringPullback p).obj F).obj.map (homOfLE hWU).op c =
      ((ringPullback p).obj F).obj.map (homOfLE hWV).op (ringUnit p F V x)) :
    ∃ (V' : Opens X) (_ : p y ∈ V') (hV' : V' ≤ V),
      φ.hom.app (op V') (F.obj.map (homOfLE hV').op x) = 0 := by
  have h0 : ((ringPullback p).obj G).obj.map (homOfLE hWV).op
        (ringUnit p G V (φ.hom.app (op V) x)) =
      ((ringPullback p).obj G).obj.map (homOfLE hWV).op (ringUnit p G V 0) := by
    rw [← ringUnit_naturality, ← sheafHom_naturality_apply, ← hcx, sheafHom_naturality_apply,
      hc, map_zero, map_zero, map_zero]
  obtain ⟨V', hV', hV'V, e₀⟩ := exists_restrict_eq_of_ringUnit_eq p G _ _ y hyW hWV h0
  exact ⟨V', hV', hV'V, by rw [sheafHom_naturality_apply]; exact e₀.trans (map_zero _)⟩

/-- **The inverse image of a morphism with square-zero kernel has square-zero kernel**, read on
two sections. -/
theorem mul_eq_zero_of_inverseImage {G : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
    (φ : F ⟶ G) (hφ : ∀ U : (Opens X)ᵒᵖ, (RingHom.ker (φ.hom.app U).hom) ^ 2 = ⊥)
    {U : Opens Y} (a b : ((ringPullback p).obj F).obj.obj (op U))
    (ha : ((ringPullback p).map φ).hom.app (op U) a = 0)
    (hb : ((ringPullback p).map φ).hom.app (op U) b = 0) :
    a * b = 0 := by
  let PF := (ringPullback p).obj F
  let PG := (ringPullback p).obj G
  let Pφ := (ringPullback p).map φ
  refine ringSheaf_eq_of_locally_eq PF (a * b) 0 fun y hy => ?_
  obtain ⟨V, hV, t, t', W, hyW, hWU, hWV, e, e'⟩ := exists_restrict_eq_ringUnit₂ p F a b y hy
  obtain ⟨V₁, hV₁, hV₁V, h₁⟩ := exists_restrict_map_eq_zero p F φ ha hyW e
  obtain ⟨V₂, hV₂, hV₂V, h₂⟩ := exists_restrict_map_eq_zero p F φ hb hyW e'
  have hV₁₂V : V₁ ⊓ V₂ ≤ V := inf_le_left.trans hV₁V
  have hz : F.obj.map (homOfLE hV₁₂V).op t * F.obj.map (homOfLE hV₁₂V).op t' = 0 := by
    have hmem : F.obj.map (homOfLE hV₁₂V).op t * F.obj.map (homOfLE hV₁₂V).op t' ∈
        (RingHom.ker (φ.hom.app (op (V₁ ⊓ V₂))).hom) ^ 2 := by
      rw [pow_two]
      refine Ideal.mul_mem_mul ?_ ?_
      · rw [RingHom.mem_ker, ← sheaf_map_map F hV₁V inf_le_left]
        show φ.hom.app _ _ = 0
        rw [sheafHom_naturality_apply, h₁, map_zero]
      · rw [RingHom.mem_ker,
          show (homOfLE hV₁₂V : V₁ ⊓ V₂ ⟶ V) =
            homOfLE (inf_le_right.trans hV₂V) from Subsingleton.elim _ _,
          ← sheaf_map_map F hV₂V inf_le_right]
        show φ.hom.app _ _ = 0
        rw [sheafHom_naturality_apply, h₂, map_zero]
    rwa [hφ, Ideal.mem_bot] at hmem
  refine ⟨W ⊓ (Opens.map p).obj (V₁ ⊓ V₂), ⟨hyW, hV₁, hV₂⟩, inf_le_left.trans hWU, ?_⟩
  rw [map_mul, restrict_eq_restrict_ringUnit p F hV₁₂V e inf_le_left inf_le_right,
    restrict_eq_restrict_ringUnit p F hV₁₂V e' inf_le_left inf_le_right,
    ← map_mul, ← map_mul, hz, map_zero, map_zero, map_zero]

/-- The square-zero property of the kernel, in the form of the field of a layer. -/
theorem ker_pow_two_inverseImage {G : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
    (φ : F ⟶ G) (hφ : ∀ U : (Opens X)ᵒᵖ, (RingHom.ker (φ.hom.app U).hom) ^ 2 = ⊥)
    (U : (Opens Y)ᵒᵖ) :
    (RingHom.ker (((ringPullback p).map φ).hom.app U).hom) ^ 2 = ⊥ := by
  rw [pow_two, eq_bot_iff, Ideal.mul_le]
  intro a ha b hb
  exact Ideal.mem_bot.2 (mul_eq_zero_of_inverseImage p F φ hφ (U := U.unop) a b ha hb)

end Units

section ModuleUnits

variable {X Y : TopCat.{u}} (p : Y ⟶ X) (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))

/-- The direct image of sheaves of modules along the unit `O ⟶ p_* p⁻¹O` is a right adjoint,
for `O` spelled as a sheaf on the site of opens. -/
instance isRightAdjoint_pushforward_inverseImageRingHom :
    (SheafOfModules.pushforward.{u} (inverseImageRingHom p O)).IsRightAdjoint :=
  AlgebraicGeometry.SheafOfModules.isRightAdjoint_pushforward_inverseImageRingHom p O

/-- The section of `p⁻¹M` over `p⁻¹V` induced by a section of a sheaf of modules `M` over `V`:
the unit of the adjunction `p⁻¹ ⊣ p_*` for sheaves of modules. -/
abbrev moduleUnit (V : Opens X) (m : M.val.obj (op V)) :
    (inverseImageModule p O M).val.obj (op ((Opens.map p).obj V)) :=
  (inverseImageModuleUnit p O M).val.app (op V) m

/-- The induced section of zero is zero. -/
theorem moduleUnit_zero (V : Opens X) : moduleUnit p O M V 0 = 0 :=
  map_zero _

/-- `Stacks.Topology.exists_restrict_eq_moduleUnit`, with the induced section spelled through
`moduleUnit`. -/
theorem exists_restrict_eq_moduleUnit' {U : Opens Y}
    (s : (inverseImageModule p O M).val.obj (op U)) (y : Y) (hy : y ∈ U) :
    ∃ (V : Opens X) (_ : p y ∈ V) (m : M.val.obj (op V)) (W : Opens Y) (_ : y ∈ W)
      (hWU : W ≤ U) (hWV : W ≤ (Opens.map p).obj V),
      (inverseImageModule p O M).val.map (homOfLE hWU).op s =
        (inverseImageModule p O M).val.map (homOfLE hWV).op (moduleUnit p O M V m) :=
  Stacks.Topology.exists_restrict_eq_moduleUnit p O M s y hy

/-- The induced sections of a sheaf of modules commute with restriction. -/
theorem moduleUnit_restrict {V V' : Opens X} (h : V' ≤ V) {W : Opens Y}
    (hW : W ≤ (Opens.map p).obj V') (m : M.val.obj (op V)) :
    (inverseImageModule p O M).val.map (homOfLE (hW.trans (opensMap_le p h))).op
        (moduleUnit p O M V m) =
      (inverseImageModule p O M).val.map (homOfLE hW).op
        (moduleUnit p O M V' (M.val.map (homOfLE h).op m)) := by
  have hn : moduleUnit p O M V' (M.val.map (homOfLE h).op m) =
      (inverseImageModule p O M).val.map ((Opens.map p).map (homOfLE h)).op
        (moduleUnit p O M V m) :=
    PresheafOfModules.naturality_apply (inverseImageModuleUnit p O M).val (homOfLE h).op m
  rw [hn]
  exact (module_map_map (inverseImageModule p O M) (opensMap_le p h) hW _).symm

end ModuleUnits

namespace LiftSquare

variable {X Y : TopCat.{u}} (p : Y ⟶ X) (L : LiftSquare.{u, u, u} (Opens.grothendieckTopology X))

/-- **The inclusion of the ideal of the inverse image of a layer**: the inverse image of the
inclusion `𝒢 ⟶ 𝒪'`, read through the comparison of the inverse image of a restriction of
scalars with the restriction of scalars of the inverse image, and through the identification of
the inverse image of the unit module with the unit module. -/
def inverseImageKernelInclusion :
    (SheafOfModules.restrictScalars
      ((sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat.{u} RingCat.{u})).map
        ((ringPullback p).map L.reduction))).obj (inverseImageModule p L.O L.G) ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf ((ringPullback p).obj L.O')) :=
  (AlgebraicGeometry.SheafOfModules.inverseImageRestrictScalarsIso p L.reduction L.G).inv ≫
    (SheafOfModules.pullback (inverseImageRingHom p L.O')).map L.kernelInclusion ≫
    SheafOfModules.pullbackObjUnitToUnit (inverseImageRingHom p L.O')

/-- **The inclusion of the ideal of the inverse image carries the induced section of a section
`m` of `𝒢` to the induced section of the image of `m`.** -/
theorem inverseImageKernelInclusion_moduleUnit (V : Opens X) (m : L.G.val.obj (op V)) :
    (inverseImageKernelInclusion p L).val.app (op ((Opens.map p).obj V))
        (moduleUnit p L.O L.G V m) = ringUnit p L.O' V (L.incl m) := by
  let e := AlgebraicGeometry.SheafOfModules.inverseImageRestrictScalarsIso p L.reduction L.G
  let RS := (SheafOfModules.restrictScalars ((sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat.{u} RingCat.{u})).map L.reduction)).obj L.G
  have hu := AlgebraicGeometry.SheafOfModules.inverseImageRestrictScalarsIso_unit_apply p
    L.reduction L.G (op V) m
  have h1 : e.inv.val.app (op ((Opens.map p).obj V)) (moduleUnit p L.O L.G V m) =
      (inverseImageModuleUnit p L.O' RS).val.app (op V) m :=
    (congrArg (fun x => e.inv.val.app (op ((Opens.map p).obj V)) x) hu.symm).trans
      (congrArg (fun k => k.val.app (op ((Opens.map p).obj V))
        ((inverseImageModuleUnit p L.O' RS).val.app (op V) m)) e.hom_inv_id)
  have h2 := congrArg (fun k => k.val.app (op V) m)
    ((SheafOfModules.pullbackPushforwardAdjunction (inverseImageRingHom p L.O')).unit.naturality
      L.kernelInclusion)
  have h3' : (SheafOfModules.pullbackPushforwardAdjunction (inverseImageRingHom p L.O')).unit.app
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf L.O')) ≫
      (SheafOfModules.pushforward (inverseImageRingHom p L.O')).map
        (SheafOfModules.pullbackObjUnitToUnit (inverseImageRingHom p L.O')) =
      SheafOfModules.unitToPushforwardObjUnit (inverseImageRingHom p L.O') :=
    ((SheafOfModules.pullbackPushforwardAdjunction (inverseImageRingHom p L.O')).homEquiv_unit
      (f := SheafOfModules.pullbackObjUnitToUnit (inverseImageRingHom p L.O'))).symm.trans
      (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _)
  have h3 := congrArg (fun k => k.val.app (op V) (L.incl m)) h3'
  show (SheafOfModules.pullbackObjUnitToUnit (inverseImageRingHom p L.O')).val.app _
      (((SheafOfModules.pullback (inverseImageRingHom p L.O')).map L.kernelInclusion).val.app _
        (e.inv.val.app _ (moduleUnit p L.O L.G V m))) = _
  rw [h1]
  exact (congrArg _ h2.symm).trans h3

/-- The inclusion of the ideal of the inverse image commutes with restriction. -/
theorem inverseImageKernelInclusion_naturality {U V : Opens Y} (h : V ≤ U)
    (m : (inverseImageModule p L.O L.G).val.obj (op U)) :
    (inverseImageKernelInclusion p L).val.app (op V)
        ((inverseImageModule p L.O L.G).val.map (homOfLE h).op m) =
      ((ringPullback p).obj L.O').obj.map (homOfLE h).op
        ((inverseImageKernelInclusion p L).val.app (op U) m) :=
  PresheafOfModules.naturality_apply (inverseImageKernelInclusion p L).val (homOfLE h).op m

/-- Near every point, a section of the inverse image of the ideal module is an induced
section, and so is its image. -/
theorem exists_restrict_inverseImageKernelInclusion {U : Opens Y}
    (m : (inverseImageModule p L.O L.G).val.obj (op U)) (y : Y) (hy : y ∈ U) :
    ∃ (V : Opens X) (_ : p y ∈ V) (μ : L.G.val.obj (op V)) (W : Opens Y) (_ : y ∈ W)
      (hWU : W ≤ U) (hWV : W ≤ (Opens.map p).obj V),
      (inverseImageModule p L.O L.G).val.map (homOfLE hWU).op m =
          (inverseImageModule p L.O L.G).val.map (homOfLE hWV).op (moduleUnit p L.O L.G V μ) ∧
        ((ringPullback p).obj L.O').obj.map (homOfLE hWU).op
            ((inverseImageKernelInclusion p L).val.app (op U) m) =
          ((ringPullback p).obj L.O').obj.map (homOfLE hWV).op (ringUnit p L.O' V (L.incl μ)) := by
  obtain ⟨V, hV, μ, W, hyW, hWU, hWV, e⟩ := exists_restrict_eq_moduleUnit' p L.O L.G m y hy
  refine ⟨V, hV, μ, W, hyW, hWU, hWV, e, ?_⟩
  rw [← inverseImageKernelInclusion_naturality, e, inverseImageKernelInclusion_naturality,
    inverseImageKernelInclusion_moduleUnit]

/-- The reduction kills the image of the inclusion of the ideal of the inverse image. -/
theorem inverseImage_kernelZero (U : (Opens Y)ᵒᵖ) (m : (inverseImageModule p L.O L.G).val.obj U) :
    ((ringPullback p).map L.reduction).hom.app U
      (show ((ringPullback p).obj L.O').obj.obj U from
        (inverseImageKernelInclusion p L).val.app U m) = 0 := by
  obtain ⟨U⟩ := U
  refine ringSheaf_eq_of_locally_eq _ _ 0 fun y hy => ?_
  obtain ⟨V, hV, μ, W, hyW, hWU, hWV, -, e⟩ :=
    exists_restrict_inverseImageKernelInclusion p L m y hy
  refine ⟨W, hyW, hWU, ?_⟩
  rw [← sheafHom_naturality_apply, e, sheafHom_naturality_apply, ringUnit_naturality,
    L.reduction_incl, map_zero, map_zero, map_zero]

/-- The inclusion of the ideal of the inverse image kills only zero. -/
theorem inverseImage_eq_zero_of_incl {U : Opens Y}
    (m : (inverseImageModule p L.O L.G).val.obj (op U))
    (hm : (inverseImageKernelInclusion p L).val.app (op U) m = 0) : m = 0 := by
  refine Stacks.Topology.sheafOfModules_eq_of_locally_eq _ m 0 fun y hy => ?_
  obtain ⟨V, hV, μ, W, hyW, hWU, hWV, e, e'⟩ :=
    exists_restrict_inverseImageKernelInclusion p L m y hy
  have h0 := (congrArg (fun x => ((ringPullback p).obj L.O').obj.map (homOfLE hWU).op x) hm).trans
    (map_zero _)
  have e'' : ((ringPullback p).obj L.O').obj.map (homOfLE hWV).op (ringUnit p L.O' V (L.incl μ)) =
      ((ringPullback p).obj L.O').obj.map (homOfLE hWV).op (ringUnit p L.O' V 0) := by
    rw [map_zero, map_zero]
    exact e'.symm.trans h0
  obtain ⟨V', hV', hV'V, e₀⟩ := exists_restrict_eq_of_ringUnit_eq p L.O' _ _ y hyW hWV e''
  rw [map_zero] at e₀
  have hμ : (L.G.val.map (homOfLE hV'V).op μ : L.G.val.obj (op V')) = 0 :=
    L.incl_injective ((L.incl_naturality (homOfLE hV'V).op μ).trans (e₀.trans L.incl_zero.symm))
  have hW' : W ⊓ (Opens.map p).obj V' ≤ (Opens.map p).obj V' := inf_le_right
  refine ⟨W ⊓ (Opens.map p).obj V', ⟨hyW, hV'⟩, inf_le_left.trans hWU, ?_⟩
  rw [map_zero, ← module_map_map _ hWU inf_le_left, e, module_map_map,
    show (homOfLE (inf_le_left.trans hWV) : W ⊓ (Opens.map p).obj V' ⟶ _) =
      homOfLE (hW'.trans (opensMap_le p hV'V)) from Subsingleton.elim _ _,
    moduleUnit_restrict p L.O L.G hV'V hW', hμ]
  exact (congrArg _ (moduleUnit_zero p L.O L.G V')).trans (map_zero _)

/-- The inclusion of the ideal of the inverse image is injective on sections. -/
theorem inverseImage_incl_injective (U : Opens Y) :
    Function.Injective ((inverseImageKernelInclusion p L).val.app (op U)) :=
  fun m m' h => sub_eq_zero.1 <|
    inverseImage_eq_zero_of_incl p L (m - m') (by rw [map_sub, h, sub_self])

/-- A section of the inverse image of `𝒪'` killed by the reduction is in the image of the
inclusion of the ideal of the inverse image. -/
theorem inverseImage_exists_incl {U : Opens Y} (a : ((ringPullback p).obj L.O').obj.obj (op U))
    (ha : ((ringPullback p).map L.reduction).hom.app (op U) a = 0) :
    ∃ m, (inverseImageKernelInclusion p L).val.app (op U) m = a := by
  refine Stacks.Topology.exists_app_eq_of_locally (inverseImageKernelInclusion p L)
    (inverseImage_incl_injective p L) a fun y hy => ?_
  obtain ⟨V, hV, σ, W, hyW, hWU, hWV, e⟩ := exists_restrict_eq_ringUnit p L.O' a y hy
  obtain ⟨V', hV', hV'V, e₀⟩ := exists_restrict_map_eq_zero p L.O' L.reduction ha hyW e
  obtain ⟨μ, hμ⟩ := L.exists_incl _ e₀
  refine ⟨W ⊓ (Opens.map p).obj V', ⟨hyW, hV'⟩, inf_le_left.trans hWU,
    (inverseImageModule p L.O L.G).val.map (homOfLE inf_le_right).op (moduleUnit p L.O L.G V' μ),
    ?_⟩
  show (inverseImageKernelInclusion p L).val.app _ _ = ((ringPullback p).obj L.O').obj.map _ a
  rw [inverseImageKernelInclusion_naturality, inverseImageKernelInclusion_moduleUnit, hμ]
  exact (restrict_eq_restrict_ringUnit p L.O' hV'V e inf_le_left inf_le_right).symm

/-- **The inverse image of a layer of the diagram of Stacks 08U8 along a continuous map.** All
four sheaves of rings and both thickenings are pulled back, the module is the inverse image
`p⁻¹𝒢`, and the inclusion of the ideal is `inverseImageKernelInclusion`. -/
def inverseImage : LiftSquare.{u, u, u} (Opens.grothendieckTopology Y) where
  OB := (ringPullback p).obj L.OB
  OB' := (ringPullback p).obj L.OB'
  O := (ringPullback p).obj L.O
  O' := (ringPullback p).obj L.O'
  baseReduction := (ringPullback p).map L.baseReduction
  reduction := (ringPullback p).map L.reduction
  f := (ringPullback p).map L.f
  f' := (ringPullback p).map L.f'
  comm := by rw [← Functor.map_comp, L.comm, Functor.map_comp]
  baseLocallySurjective :=
    isLocallySurjective_inverseImage_map p _ L.baseReduction L.baseLocallySurjective
  baseSquareZero := ker_pow_two_inverseImage p _ L.baseReduction L.baseSquareZero
  locallySurjective := isLocallySurjective_inverseImage_map p _ L.reduction L.locallySurjective
  squareZero := ker_pow_two_inverseImage p _ L.reduction L.squareZero
  G := inverseImageModule p L.O L.G
  kernelInclusion := inverseImageKernelInclusion p L
  kernelZero := inverseImage_kernelZero p L
  kernelUniversal U a ha := by
    obtain ⟨U⟩ := U
    obtain ⟨m, hm⟩ := inverseImage_exists_incl p L a ha
    exact ⟨m, hm, fun m' hm' => inverseImage_incl_injective p L U (hm'.trans hm.symm)⟩

/-- The inclusion of the ideal of the inverse image, on induced sections. -/
theorem inverseImage_incl_moduleUnit (V : Opens X) (m : L.G.val.obj (op V)) :
    (L.inverseImage p).incl (moduleUnit p L.O L.G V m) = ringUnit p L.O' V (L.incl m) :=
  inverseImageKernelInclusion_moduleUnit p L V m

end LiftSquare

end Deformation.ToposThickening

end
