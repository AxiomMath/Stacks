module

public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.GenericStalkChartRatio
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.GenericStalkChartUnit

/-!
# The generic generator of Tag 0BD7, at the generic point of `X`

`AlgebraicGeometry.eq_smul_grpGerm_genericFiberTrivGenerator` states the first paragraph of
[Stacks, Tag 0BD7] at the image of a point `x₀` of the generic fibre; the penultimate paragraph
needs it at the generic point of `X` itself, which is that image for the `x₀` of
`AlgebraicGeometry.exists_fiberι_base_eq_genericPoint`. The two points are *equal*, but the
statement carries a dependent membership proof `genericPoint X ∈ U`, so rewriting by that
equality is a motive problem and not a transport. This file supplies the transport.

What has to move is a module stalk, and the comparison that moves it is
`TopCat.Presheaf.stalkSpecializes` of the underlying presheaf of abelian groups. Three facts are
needed and none of them is in the library at this spelling: that it commutes with
`Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm`, that it is semilinear over the
comparison of the structure sheaf, and that it carries a generator of one stalk to a generator
of the other — the last because the two points are inseparable, so the comparison is an
isomorphism.

## Main definitions

* `AlgebraicGeometry.genericStalkGenerator`: the generator of the stalk of `ℒ` at the generic
  point of `X` that the first paragraph of the source builds — the germ of the trivializing
  section of `ℒ_ξ`, carried down by
  `AlgebraicGeometry.stalkPullbackFiberιAddEquiv` and then along the specialization.

## Main results

* `Stacks.SheafOfModules.TensorStalkRingedSpace.stalkSpecializes_smul`: the specialization map of
  a module over a ringed space is semilinear over that of the structure sheaf.
* `Stacks.SheafOfModules.TensorStalkRingedSpace.exists_stalkSpecializes_eq_grpGerm_smul`: the
  transport of a relation `v = c · germ s`, with the multiplier turned back into a section.
* `Stacks.SheafOfModules.TensorStalkRingedSpace.span_eq_top_stalkSpecializes`: between
  inseparable points the specialization map carries a generator to a generator.
* `AlgebraicGeometry.span_eq_top_genericStalkGenerator`: that generator generates.
* `AlgebraicGeometry.eq_smul_germ_genericStalkGenerator`: it is the chart ratio, read in `K(X)`,
  times the germ at the generic point of a chart generator. This is the hypothesis `hm` of
  `Stacks.InvertiblePullback.exists_mem_generatingLocus_restrictₛₗ_pullbackMeromorphicMul_eq`.

## Implementation notes

The multiplier is pushed back onto a *section* before the transport is used. At the generic point
of an integral scheme the scalar ring carries a `Field` instance, so `c • m` on the stalk
resolves its `Module` instance through the field rather than through the commutative ring, and
the resulting action is Mathlib's `Scheme.Modules.moduleStalkPresheaf` while the action in
`AlgebraicGeometry.eq_smul_grpGerm_genericFiberTrivGenerator` is Tag 01CB's
`Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule`. The two are equal
(`Stacks.SheafOfModules.stalkModule_eq`) but not definitionally, and the definitional comparison
is not available here: it needs `CategoryTheory.Limits.getColimitCocone` unfolded, which
the module system does not expose. So no statement below multiplies on a stalk at the generic
point: `exists_stalkSpecializes_eq_grpGerm_smul` returns the product as a section, and
`PresheafOfModules.germ_smul` splits its germ in whichever action the consumer is using.

For the same reason the section product is written `HSMul.hSMul` with the scalar type named: with
`ℒ` bound as `X.Modules` the instance for `a • t` is not found from `a : Γ(X, W)` alone.

`Stacks.ModuleStalkSpecialization.stalkSpecializes_smul` is the same statement for an
`X.Modules` over a scheme, proved the same way; the two should be merged when the files meet, in
the ringed-space generality, since this one is what the Tag 01CB spelling needs.

No tag attribute: every statement here carries an affine chart of `X` and a point of the generic
fibre, neither of which [Stacks, Tag 0BD7] has.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open Stacks.RingedSpace Stacks.SheafOfModules RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.TensorStalkRingedSpace

namespace Stacks.SheafOfModules.TensorStalkRingedSpace

variable (X : AlgebraicGeometry.RingedSpace.{u, u})

/-- The germ of a section of a module, specialized, is its germ at the smaller point. -/
theorem grpGerm_stalkSpecializes (F : PresheafOfModules.{u} (O X)) {x y : X.carrier}
    {W : TopologicalSpace.Opens X.carrier} (hx : x ∈ W) (h : y ⤳ x) (s : F.obj (op W)) :
    TopCat.Presheaf.stalkSpecializes F.presheaf h (grpGerm X F x W hx s)
      = grpGerm X F y W (h.mem_open W.isOpen hx) s :=
  congrArg (fun φ => (ConcreteCategory.hom φ) s)
    (TopCat.Presheaf.germ_stalkSpecializes F.presheaf hx h)

/-- The germ of a section of the structure sheaf, specialized, is its germ at the smaller
point. -/
theorem ringGerm_stalkSpecializes {x y : X.carrier}
    {W : TopologicalSpace.Opens X.carrier} (hx : x ∈ W) (h : y ⤳ x)
    (r : X.presheaf.obj (op W)) :
    X.presheaf.stalkSpecializes h (ringGerm X x W hx r)
      = ringGerm X y W (h.mem_open W.isOpen hx) r :=
  congrArg (fun φ => (ConcreteCategory.hom φ) r)
    (TopCat.Presheaf.germ_stalkSpecializes X.presheaf hx h)

/-- Every element of a ring stalk is the germ of a section over any smaller neighbourhood. -/
private theorem exists_ringGerm_eq_of_le {x : X.carrier} (r : ringStalk X x)
    {W : TopologicalSpace.Opens X.carrier} (hxW : x ∈ W) :
    ∃ V : TopologicalSpace.Opens X.carrier, V ≤ W ∧ ∃ (hxV : x ∈ V)
      (a : X.presheaf.obj (op V)), ringGerm X x V hxV a = r := by
  obtain ⟨V, hxV, a, ha⟩ := X.presheaf.exists_germ_eq r
  exact ⟨V ⊓ W, inf_le_right, ⟨hxV, hxW⟩,
    (X.presheaf.map (homOfLE (inf_le_left : V ⊓ W ≤ V)).op).hom a,
    (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE inf_le_left) x ⟨hxV, hxW⟩ a).trans ha⟩

/-- **The specialization map of a module is semilinear** over the specialization map of the
structure sheaf. Both arguments are germs on a common neighbourhood, and the identity is
`Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule_germ_smul` at the two points. -/
theorem stalkSpecializes_smul (F : PresheafOfModules.{u} (O X)) {x y : X.carrier}
    (h : y ⤳ x) (r : ringStalk X x) (m : grpStalk X F x) :
    TopCat.Presheaf.stalkSpecializes F.presheaf h (r • m)
      = X.presheaf.stalkSpecializes h r • TopCat.Presheaf.stalkSpecializes F.presheaf h m := by
  obtain ⟨W, hxW, t, ht⟩ := TopCat.Presheaf.exists_germ_eq F.presheaf m
  obtain ⟨V, hVW, hxV, u, hu⟩ := exists_ringGerm_eq_of_le X r hxW
  obtain ⟨t0, ht0⟩ : ∃ t0 : F.obj (op V), grpGerm X F x V hxV t0 = m :=
    ⟨F.presheaf.map (homOfLE hVW).op t,
      (TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE hVW) x hxV t).trans ht⟩
  rw [← hu, ← ht0, ← stalkModule_germ_smul X F x V hxV, grpGerm_stalkSpecializes,
    grpGerm_stalkSpecializes, ringGerm_stalkSpecializes,
    stalkModule_germ_smul X F y V (h.mem_open V.isOpen hxV)]

/-- **The transport of `v = c · germ s`, with the multiplier turned back into a section.** At the
smaller point `z` the relation is the germ of a single section `a · s`, and no scalar
multiplication on the stalk at `z` occurs — which is what lets a consumer at the generic point
split the germ in whichever of the two equal module structures it is using. -/
theorem exists_stalkSpecializes_eq_grpGerm_smul (F : PresheafOfModules.{u} (O X))
    {b z : X.carrier} (h : z ⤳ b) {W : TopologicalSpace.Opens X.carrier} (hbW : b ∈ W)
    (v : grpStalk X F b) (c : ringStalk X b) (s : F.obj (op W))
    (hv : v = c • grpGerm X F b W hbW s) :
    ∃ (W' : TopologicalSpace.Opens X.carrier) (hW'W : W' ≤ W) (hzW' : z ∈ W')
      (a : X.presheaf.obj (op W')),
      ringGerm X z W' hzW' a = X.presheaf.stalkSpecializes h c ∧
        TopCat.Presheaf.stalkSpecializes F.presheaf h v
          = grpGerm X F z W' hzW' (a • F.restrictₛₗ (homOfLE hW'W).op s) := by
  obtain ⟨V, hVW, hbV, a, ha⟩ := exists_ringGerm_eq_of_le X c hbW
  have hs : grpGerm X F b V hbV (F.restrictₛₗ (homOfLE hVW).op s) = grpGerm X F b W hbW s :=
    TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE hVW) b hbV s
  refine ⟨V, hVW, h.mem_open V.isOpen hbV, a, ?_, ?_⟩
  · rw [← ha, ringGerm_stalkSpecializes]
  · rw [hv, ← ha, ← hs, ← stalkModule_germ_smul, grpGerm_stalkSpecializes]

/-- **Between inseparable points the specialization map carries a generator to a generator.**
The comparison is then an isomorphism of stalks, semilinear over an isomorphism of local rings,
so a single generator is carried to a single generator. -/
theorem span_eq_top_stalkSpecializes (F : PresheafOfModules.{u} (O X)) {b z : X.carrier}
    (hbz : Inseparable b z) (v : grpStalk X F b)
    (hv : Submodule.span (ringStalk X b) {v} = ⊤) :
    Submodule.span (ringStalk X z)
      {TopCat.Presheaf.stalkSpecializes F.presheaf hbz.ge v} = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun w => ?_
  have hw : TopCat.Presheaf.stalkSpecializes F.presheaf hbz.ge
      ((TopCat.Presheaf.stalkCongr F.presheaf hbz).inv w) = w :=
    congrArg (fun φ : grpStalk X F z ⟶ grpStalk X F z => (ConcreteCategory.hom φ) w)
      (TopCat.Presheaf.stalkCongr F.presheaf hbz).inv_hom_id
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1
    (hv ▸ Submodule.mem_top : (TopCat.Presheaf.stalkCongr F.presheaf hbz).inv w ∈
      Submodule.span (ringStalk X b) {v})
  refine Submodule.mem_span_singleton.2 ⟨X.presheaf.stalkSpecializes hbz.ge r, ?_⟩
  exact ((stalkSpecializes_smul X F hbz.ge r v).symm.trans
    (congrArg (fun y : grpStalk X F b =>
      TopCat.Presheaf.stalkSpecializes F.presheaf hbz.ge y) hr)).trans hw

end Stacks.SheafOfModules.TensorStalkRingedSpace

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [IsIntegral X] [IsIntegral Y] {x : X}
  {V : Y.Opens} {U : X.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U)
  (e : U ≤ f ⁻¹ᵁ V) (hx : x ∈ U)
  (L : X.Modules)
  (hgen : AlgebraicGeometry.SheafOfModules.IsTrivial
    (f.fiber (genericPoint Y)).presheaf
    (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
      (f.fiber (genericPoint Y)).IsSheaf)
    ((Scheme.Modules.pullback (f.fiberι (genericPoint Y))).obj L))
  (hL : IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L)
  (genU : GeneratorSections X.toRingedSpace L U)

/-- **The generator of the stalk of `ℒ` at the generic point of `X`.** The germ on `⊤` of the
trivializing section of `ℒ_ξ`, carried to the stalk of `ℒ` at the image of `x₀` by
`AlgebraicGeometry.stalkPullbackFiberιAddEquiv` and from there to the generic point of `X`. -/
noncomputable def genericStalkGenerator {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X]
    [IsIntegral Y] (L : X.Modules)
    (hgen : AlgebraicGeometry.SheafOfModules.IsTrivial
      (f.fiber (genericPoint Y)).presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
        (f.fiber (genericPoint Y)).IsSheaf)
      ((Scheme.Modules.pullback (f.fiberι (genericPoint Y))).obj L))
    (x₀ : f.fiber (genericPoint Y))
    (hx₀ : (f.fiberι (genericPoint Y)).base x₀ = genericPoint X) :
    grpStalk X.toRingedSpace L.val (genericPoint X) :=
  TopCat.Presheaf.stalkSpecializes L.val.presheaf (Inseparable.of_eq hx₀).ge
    (stalkPullbackFiberιAddEquiv f (maximalIdeal_stalk_genericPoint_eq_bot Y) L x₀
      (grpGerm (f.fiber (genericPoint Y)).toRingedSpace
        ((pullbackFunctor (f.fiberι (genericPoint Y)).toLRSHom.toShHom).obj L).val x₀
        ⊤ (Opens.mem_top x₀) (genericFiberTrivGenerator f L hgen ⊤).val))

omit [Flat f] in
/-- **`AlgebraicGeometry.genericStalkGenerator` generates the stalk at the generic point.**
The germ of the trivializing section generates on the generic fibre
(`AlgebraicGeometry.span_eq_top_grpGerm_genericFiberTrivGenerator`), and both comparisons carry
a generator to a generator. -/
theorem span_eq_top_genericStalkGenerator (x₀ : f.fiber (genericPoint Y))
    (hx₀ : (f.fiberι (genericPoint Y)).base x₀ = genericPoint X) :
    letI : Module (ringStalk X.toRingedSpace (genericPoint X))
        (grpStalk X.toRingedSpace L.val (genericPoint X)) :=
      stalkModule X.toRingedSpace L.val (genericPoint X)
    Submodule.span (ringStalk X.toRingedSpace (genericPoint X))
      {genericStalkGenerator f L hgen x₀ hx₀} = ⊤ :=
  span_eq_top_stalkSpecializes X.toRingedSpace L.val (Inseparable.of_eq hx₀) _
    (span_eq_top_grpStalk_stalkPullbackFiberιAddEquiv f
      (maximalIdeal_stalk_genericPoint_eq_bot Y) L x₀ _
      (span_eq_top_grpGerm_genericFiberTrivGenerator f L hgen x₀))

omit [Flat f] in
include hV hU e hx hL in
/-- **The generic generator is the chart ratio times the germ of the chart generator.**
`AlgebraicGeometry.eq_smul_grpGerm_genericFiberTrivGenerator`, transported to the generic point
of `X`; the multiplier is the chart ratio read in `K(X)` through
`AlgebraicGeometry.genericFiberStalkIsoFunctionField`. -/
theorem eq_smul_germ_genericStalkGenerator (x₀ : f.fiber (genericPoint Y))
    (hx₀ : (f.fiberι (genericPoint Y)).base x₀ = genericPoint X)
    (hξU : genericPoint X ∈ U) :
    genericStalkGenerator f L hgen x₀ hx₀
      = (genericFiberStalkIsoFunctionField f x₀ hx₀).inv
            ((f.fiber (genericPoint Y)).presheaf.germ (genericFiberChartOpens f hV hU e hx) x₀
              (mem_genericFiberChartOpens_of_base_eq_genericPoint f hV hU e hx x₀ hx₀)
              (generatorRatio _ (genericFiberChartOpens f hV hU e hx)
                (genericFiberChartGenerator f hV hU e hx L hL genU)
                (genericFiberTrivGenerator f L hgen (genericFiberChartOpens f hV hU e hx))))
        • L.presheaf.germ U (genericPoint X) hξU genU.val := by
  classical
  have : IsIso (((f.fiberι (genericPoint Y)).toLRSHom.toShHom).hom.stalkMap x₀) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (bijective_stalkMap_fiberι_of_mem f (maximalIdeal_stalk_genericPoint_eq_bot Y) x₀)
  have hbase : ((f.fiberι (genericPoint Y)).toLRSHom.toShHom).hom.base x₀ ∈ U := by
    rw [show ((f.fiberι (genericPoint Y)).toLRSHom.toShHom).hom.base x₀ = genericPoint X from hx₀]
    exact hξU
  have key := eq_smul_grpGerm_genericFiberTrivGenerator f hV hU e hx L hgen hL genU x₀ hbase
  obtain ⟨W', hW'U, hξW', a, hca, hv⟩ := exists_stalkSpecializes_eq_grpGerm_smul
    X.toRingedSpace L.val (Inseparable.of_eq hx₀).ge hbase _ _ genU.val key
  have hac := hca.trans (genericFiberStalkIsoFunctionField_inv_apply f x₀ hx₀ _).symm
  have e1 : L.presheaf.germ W' (genericPoint X) hξW'
        (HSMul.hSMul (α := ↑((Stacks.Sheaves.Differentials.ringSheaf
          (J := Opens.grothendieckTopology X) X.sheaf).obj.obj (op W'))) a
            (L.val.restrictₛₗ (homOfLE hW'U).op genU.val))
      = X.presheaf.germ W' (genericPoint X) hξW' a
        • L.presheaf.germ W' (genericPoint X) hξW'
            (L.val.restrictₛₗ (homOfLE hW'U).op genU.val) :=
    PresheafOfModules.germ_smul L.val (genericPoint X) W' hξW' _ _
  have e2 : L.presheaf.germ W' (genericPoint X) hξW'
        (L.val.restrictₛₗ (homOfLE hW'U).op genU.val)
      = L.presheaf.germ U (genericPoint X) hξU genU.val :=
    TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) L.val.presheaf
      (homOfLE hW'U) (genericPoint X) hξW' genU.val
  exact hv.trans (e1.trans (congrArg₂ (fun (r : X.functionField)
    (w : L.presheaf.stalk (genericPoint X)) => r • w) hac e2))

end AlgebraicGeometry

end
