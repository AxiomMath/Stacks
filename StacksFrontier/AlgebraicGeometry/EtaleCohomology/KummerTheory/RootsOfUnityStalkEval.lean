module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.TwistNegOneModuleStalk

/-!
# The stalk of `μ_N` at a geometric point, by evaluation

Let `s : Spec Ω ⟶ X` be a geometric point, `Ω` separably closed. A section `ζ` of `μ_N` over an
étale neighbourhood `u : Spec Ω ⟶ U` of `s` has a value `u^*ζ ∈ Ω`, an `N`-th root of unity
(`Stacks.Kummer.rootEval`). The value depends only on the germ of `ζ`
(`Stacks.Kummer.rootEval_eq_of_germ_eq`), turns sums of sections into products, and is compatible
with the maps of stalks induced by endomorphisms of the geometric point: an endomorphism acting on
`Ω` by a ring map `φ` acts on values by `φ` (`Stacks.Kummer.rootEval_hom_app`).

## Main definitions

* `Stacks.Kummer.rootEval`: the value of a section of `μ_N` at a lift of the geometric point.

## Main results

* `Stacks.Kummer.exists_presheafFiber_hom_root_eq_nsmul`: an endomorphism of the geometric point
  inverting `y ↦ y ^ q` on `Ω` multiplies the germ of a primitive root of unity by some `i` with
  `i q ≡ 1 mod N`.
* `Stacks.Kummer.twistNegOneFiberPairing_presheafFiber_hom`: on the stalk of `G(-1)`, such an
  endomorphism acts as `q` times its action on the stalk of `G`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry GrothendieckTopology

universe u

namespace Stacks.Kummer

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
variable (N : ℕ) [NeZero N]

/-- The root of unity underlying a section of `μ_N`, as a function. -/
abbrev rootSectionValue {U : X.Etale}
    (z : ToType ((rootsOfUnityModule.{u, 0} X N).obj.obj (op U))) :
    Γ(U.left, ⊤) :=
  ((rootsOfUnitySection.{u, 0} X N (op U) z).1 : Γ(U.left, ⊤))

/-- The morphism `Spec Ω ⟶ U` underlying a lift of the geometric point to `U`. -/
abbrev fiberLift {U : X.Etale} (u : (Scheme.pointSmallEtale s).fiber.obj U) :
    Spec (.of Ω) ⟶ U.left :=
  (show Over.mk s ⟶ (Scheme.Etale.forget X).obj U from u).left

/-- **The value of a section of `μ_N` at a lift `u : Spec Ω ⟶ U` of the geometric point.** -/
def rootEval {U : X.Etale} (u : (Scheme.pointSmallEtale s).fiber.obj U)
    (z : ToType ((rootsOfUnityModule.{u, 0} X N).obj.obj (op U))) : Ω :=
  (Scheme.ΓSpecIso (.of Ω)).hom.hom ((fiberLift s u).appTop.hom
    (rootSectionValue N z))

/-- The root of unity underlying a section is compatible with restriction. -/
theorem rootSectionValue_map {U V : X.Etale} (g : V ⟶ U)
    (z : ToType ((rootsOfUnityModule.{u, 0} X N).obj.obj (op U))) :
    rootSectionValue N ((rootsOfUnityModule.{u, 0} X N).obj.map g.op z) =
      g.left.appTop.hom (rootSectionValue N z) :=
  congrArg Units.val (rootsOfUnitySection_naturality.{u, 0} X N g z)

/-- The value is compatible with restriction. -/
theorem rootEval_map {U V : X.Etale} (g : V ⟶ U) (v : (Scheme.pointSmallEtale s).fiber.obj V)
    (z : ToType ((rootsOfUnityModule.{u, 0} X N).obj.obj (op U))) :
    rootEval s N ((Scheme.pointSmallEtale s).fiber.map g v) z =
      rootEval s N v ((rootsOfUnityModule.{u, 0} X N).obj.map g.op z) := by
  rw [rootEval, rootEval, rootSectionValue_map]
  change (Scheme.ΓSpecIso (.of Ω)).hom.hom ((fiberLift s v ≫ g.left).appTop.hom
    (rootSectionValue N z)) = _
  rw [Scheme.Hom.comp_appTop]
  rfl

/-- A section of `μ_N` whose image in `𝐆_m` is `ofUnit b` has underlying root of unity `b`. -/
private theorem rootSectionValue_eq_of_ι_eq {U : X.Etale}
    (z : ToType ((rootsOfUnityModule.{u, 0} X N).obj.obj (op U))) (b : Γ(U.left, ⊤)ˣ)
    (h : (rootsOfUnityι.{u, 0} X N).hom.app (op U) z = ofUnit.{u, 0} b) :
    rootSectionValue N z = b :=
  congrArg Units.val (ofUnit_injective.{u, 0} h)

/-- The root of unity underlying a sum of sections is the product of the roots of unity. -/
theorem rootSectionValue_add {U : X.Etale}
    (z z' : ToType ((rootsOfUnityModule.{u, 0} X N).obj.obj (op U))) :
    rootSectionValue N (z + z') = rootSectionValue N z * rootSectionValue N z' :=
  (rootSectionValue_eq_of_ι_eq N _ _
    (map_add ((rootsOfUnityι.{u, 0} X N).hom.app (op U)).hom z z')).trans (Units.val_mul _ _)

/-- The value turns sums of sections into products. -/
theorem rootEval_add {U : X.Etale} (u : (Scheme.pointSmallEtale s).fiber.obj U)
    (z z' : ToType ((rootsOfUnityModule.{u, 0} X N).obj.obj (op U))) :
    rootEval s N u (z + z') = rootEval s N u z * rootEval s N u z' := by
  rw [rootEval, rootEval, rootEval, rootSectionValue_add, map_mul, map_mul]

/-- The value turns multiples of a section into powers. -/
theorem rootEval_nsmul {U : X.Etale} (u : (Scheme.pointSmallEtale s).fiber.obj U)
    (z : ToType ((rootsOfUnityModule.{u, 0} X N).obj.obj (op U))) (i : ℕ) :
    rootEval s N u (i • z) = rootEval s N u z ^ i := by
  induction i with
  | zero =>
    have h : rootSectionValue N (0 : ToType ((rootsOfUnityModule.{u, 0} X N).obj.obj (op U))) = 1 :=
      rootSectionValue_eq_of_ι_eq N _ 1 (map_zero ((rootsOfUnityι.{u, 0} X N).hom.app (op U)).hom)
    rw [zero_nsmul, pow_zero, rootEval, h, map_one, map_one]
  | succ i ih => rw [succ_nsmul, rootEval_add, ih, pow_succ]

/-- The section `ζ^m` of `μ_N` over a neighbourhood `V` carrying a primitive root `ζ`. -/
abbrev rootSection {V : X.Etale} {k : Type u} [Field k] (κ : k →+* Γ(V.left, ⊤)) {ζ : k}
    (hζ : IsPrimitiveRoot ζ N) (m : ZMod N) :
    ToType ((rootsOfUnityModule.{u, 0} X N).obj.obj (op V)) :=
  sliceRootSection.{u, 0} V κ hζ (Over.mk (𝟙 V)) m

section Germs

/-- **The value depends only on the germ.** -/
theorem rootEval_eq_of_germ_eq {U U' : X.Etale} (u : (Scheme.pointSmallEtale s).fiber.obj U)
    (u' : (Scheme.pointSmallEtale s).fiber.obj U')
    (z : ToType ((rootsOfUnityModule.{u, 0} X N).obj.obj (op U)))
    (z' : ToType ((rootsOfUnityModule.{u, 0} X N).obj.obj (op U')))
    (h : (Scheme.pointSmallEtale s).toPresheafFiber U u (rootsOfUnityModule.{u, 0} X N).obj z =
      (Scheme.pointSmallEtale s).toPresheafFiber U' u' (rootsOfUnityModule.{u, 0} X N).obj z') :
    rootEval s N u z = rootEval s N u' z' := by
  have := preservesFilteredColimitsOfSize_forget_moduleCat.{u, u} (ZMod N)
  obtain ⟨W, w, g, g', rfl, rfl⟩ := exists_fiber_cone (Scheme.pointSmallEtale s) u u'
  rw [toPresheafFiber_fiber_map, toPresheafFiber_fiber_map] at h
  obtain ⟨Y, f, y, rfl, hf⟩ := ((Scheme.pointSmallEtale s).toPresheafFiber_eq_iff' W _ _ _).1 h
  rw [rootEval_map, rootEval_map, rootEval_map, rootEval_map]
  exact congrArg (rootEval s N y) hf

/-- **The stalk of `μ_N` is generated by a primitive root of unity**: on a neighbourhood `V`
carrying a primitive `N`-th root `ζ`, every germ of `μ_N` is a multiple of the germ of `ζ`, as
every section is locally a power of `ζ`. -/
theorem exists_nsmul_eq_germ_sliceRootSection {V : X.Etale}
    (v : (Scheme.pointSmallEtale s).fiber.obj V) {k : Type u} [Field k] (κ : k →+* Γ(V.left, ⊤))
    {ζ : k} (hζ : IsPrimitiveRoot ζ N)
    (m : ToType
      ((Scheme.pointSmallEtale s).presheafFiber.obj (rootsOfUnityModule.{u, 0} X N).obj)) :
    ∃ i : ℕ, m = i • (Scheme.pointSmallEtale s).toPresheafFiber V v
      (rootsOfUnityModule.{u, 0} X N).obj (rootSection N κ hζ 1) := by
  have := preservesFilteredColimitsOfSize_forget_moduleCat.{u, u} (ZMod N)
  let Φ := Scheme.pointSmallEtale s
  let M := rootsOfUnityModule.{u, 0} X N
  obtain ⟨U, u, z, rfl⟩ := Φ.toPresheafFiber_jointly_surjective m
  obtain ⟨W, w, g, h, rfl, rfl⟩ := exists_fiber_cone Φ u v
  let κW := h.left.appTop.hom.comp κ
  have hS := imageSieve_sliceRootPresheafHom_mem.{u, 0} W κW hζ (Over.mk (𝟙 W)) (M.obj.map g.op z)
  rw [GrothendieckTopology.mem_over_iff] at hS
  obtain ⟨Y, f, hf, y, rfl⟩ := Φ.jointly_surjective _ hS w
  rw [Sieve.overEquiv_iff] at hf
  obtain ⟨t, ht⟩ := hf
  let f' : Y ⟶ W := f
  let rV : ToType (M.obj.obj (op V)) := rootSection N κ hζ 1
  let rW : ToType (M.obj.obj (op W)) := sliceRootSection.{u, 0} W κW hζ (Over.mk (𝟙 W)) 1
  have ht' : (sliceRootSection.{u, 0} W κW hζ (Over.mk (f ≫ 𝟙 W)) t.down :
      ToType (M.obj.obj (op Y))) = M.obj.map f'.op (M.obj.map g.op z) := ht
  have hnat : M.obj.map f'.op rW =
      (sliceRootSection.{u, 0} W κW hζ (Over.mk (f ≫ 𝟙 W)) 1 : ToType (M.obj.obj (op Y))) :=
    sliceRootSection_naturality.{u, 0} W κW hζ
      (Over.homMk f : Over.mk (f ≫ 𝟙 W) ⟶ Over.mk (𝟙 W)) 1
  have hres : M.obj.map h.op rV = rW := rootsOfUnitySheaf_map_sliceRootSection N h κ hζ 1
  have h1 : t.down = t.down.val • (1 : ZMod N) := by
    rw [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
  have hsec : M.obj.map f'.op (M.obj.map g.op z) = t.down.val • M.obj.map f'.op rW := by
    rw [← ht', hnat]
    conv_lhs => rw [h1]
    exact sliceRootSection_nsmul.{u, 0} W κW hζ _ t.down.val 1
  refine ⟨t.down.val, ?_⟩
  change Φ.toPresheafFiber U (Φ.fiber.map g (Φ.fiber.map f' y)) M.obj z =
    t.down.val • Φ.toPresheafFiber V (Φ.fiber.map h (Φ.fiber.map f' y)) M.obj rV
  rw [toPresheafFiber_fiber_map Φ M.obj g, toPresheafFiber_fiber_map Φ M.obj f',
    toPresheafFiber_fiber_map Φ M.obj h, toPresheafFiber_fiber_map Φ M.obj f', hres, hsec,
    map_nsmul]

/-- The ring map `k → Ω` through which a neighbourhood with structure map `κ` is evaluated. -/
def rootFieldMap {V : X.Etale} (v : (Scheme.pointSmallEtale s).fiber.obj V) {k : Type u} [Field k]
    (κ : k →+* Γ(V.left, ⊤)) : k →+* Ω :=
  (Scheme.ΓSpecIso (.of Ω)).hom.hom.comp ((fiberLift s v).appTop.hom.comp κ)

/-- **The value of the section `ζ^m` is `ζ^m` read in `Ω`.** -/
theorem rootEval_sliceRootSection {V : X.Etale} (v : (Scheme.pointSmallEtale s).fiber.obj V)
    {k : Type u} [Field k] (κ : k →+* Γ(V.left, ⊤)) {ζ : k} (hζ : IsPrimitiveRoot ζ N)
    (m : ZMod N) :
    rootEval s N v (rootSection N κ hζ m) =
      rootFieldMap s v κ ζ ^ m.val := by
  rw [rootEval, rootSectionValue_eq_of_ι_eq N (rootSection N κ hζ m) _
    (rootsOfUnityι_sliceRootSection.{u, 0} V κ hζ (Over.mk (𝟙 V)) m),
    Units.val_pow_eq_pow_val, map_pow, map_pow]
  congr 1

omit [NeZero N] in
/-- The image of a primitive root of unity in `Ω` is primitive. -/
theorem isPrimitiveRoot_rootFieldMap {V : X.Etale} (v : (Scheme.pointSmallEtale s).fiber.obj V)
    {k : Type u} [Field k] (κ : k →+* Γ(V.left, ⊤)) {ζ : k} (hζ : IsPrimitiveRoot ζ N) :
    IsPrimitiveRoot (rootFieldMap s v κ ζ) N :=
  hζ.map_of_injective (rootFieldMap s v κ).injective

/-- **The value at the image of a lift under an endomorphism of the point** acting on lifts by a
ring map `φ` of `Ω` is the image of the value under `φ`. -/
theorem rootEval_hom_app (f : Scheme.pointSmallEtale s ⟶ Scheme.pointSmallEtale s)
    (φ : Ω →+* Ω)
    (hf : ∀ (U : X.Etale) (u : (Scheme.pointSmallEtale s).fiber.obj U),
      fiberLift s (f.hom.app U u) = Spec.map (CommRingCat.ofHom φ) ≫ fiberLift s u)
    {U : X.Etale} (u : (Scheme.pointSmallEtale s).fiber.obj U)
    (z : ToType ((rootsOfUnityModule.{u, 0} X N).obj.obj (op U))) :
    rootEval s N (f.hom.app U u) z = φ (rootEval s N u z) := by
  rw [rootEval, rootEval, hf, Scheme.Hom.comp_appTop]
  change ((fiberLift s u).appTop ≫ (Spec.map (CommRingCat.ofHom φ)).appTop ≫
    (Scheme.ΓSpecIso (.of Ω)).hom).hom (rootSectionValue N z) = _
  rw [Scheme.ΓSpecIso_naturality]
  rfl

/-- **The action on the stalk of `μ_N` of an endomorphism of the point inverting `y ↦ y ^ q`**:
it multiplies the germ of a primitive root by some `i` with `i q ≡ 1 mod N`. -/
theorem exists_presheafFiber_hom_root_eq_nsmul
    (f : Scheme.pointSmallEtale s ⟶ Scheme.pointSmallEtale s) (φ : Ω →+* Ω)
    (hf : ∀ (U : X.Etale) (u : (Scheme.pointSmallEtale s).fiber.obj U),
      fiberLift s (f.hom.app U u) = Spec.map (CommRingCat.ofHom φ) ≫ fiberLift s u)
    (q : ℕ) (hq : ∀ y, φ y ^ q = y) {V : X.Etale} (v : (Scheme.pointSmallEtale s).fiber.obj V)
    {k : Type u} [Field k] (κ : k →+* Γ(V.left, ⊤)) {ζ : k} (hζ : IsPrimitiveRoot ζ N) :
    ∃ i : ℕ, i * q ≡ 1 [MOD N] ∧
      (Point.Hom.presheafFiber f).app (rootsOfUnityModule.{u, 0} X N).obj
        ((Scheme.pointSmallEtale s).toPresheafFiber V v (rootsOfUnityModule.{u, 0} X N).obj
          (rootSection N κ hζ 1)) =
        i • (Scheme.pointSmallEtale s).toPresheafFiber V v (rootsOfUnityModule.{u, 0} X N).obj
          (rootSection N κ hζ 1) := by
  have := preservesFilteredColimitsOfSize_forget_moduleCat.{u, u} (ZMod N)
  let r : ToType ((rootsOfUnityModule.{u, 0} X N).obj.obj (op V)) :=
    rootSection N κ hζ 1
  obtain ⟨i, hi⟩ := exists_nsmul_eq_germ_sliceRootSection s N v κ hζ
    ((Point.Hom.presheafFiber f).app (rootsOfUnityModule.{u, 0} X N).obj
      ((Scheme.pointSmallEtale s).toPresheafFiber V v (rootsOfUnityModule.{u, 0} X N).obj r))
  refine ⟨i, ?_, hi⟩
  rw [presheafFiber_hom_app_germ, ← map_nsmul] at hi
  have hev := rootEval_eq_of_germ_eq s N _ _ _ _ hi
  rw [rootEval_hom_app s N f φ hf, rootEval_nsmul] at hev
  rcases Nat.lt_or_ge 1 N with hN | hN
  · have : Fact (1 < N) := ⟨hN⟩
    have hε := isPrimitiveRoot_rootFieldMap s N v κ hζ
    have h1 : rootEval s N v r = rootFieldMap s v κ ζ := by
      rw [rootEval_sliceRootSection, ZMod.val_one, pow_one]
    rw [h1] at hev
    have hpow : rootFieldMap s v κ ζ ^ (i * q) = rootFieldMap s v κ ζ := by
      rw [pow_mul, ← hev, hq]
    have hpos : 1 ≤ i * q := Nat.one_le_iff_ne_zero.2 fun h0 =>
      hε.ne_one hN (by rw [← hpow, h0, pow_zero])
    have hd : N ∣ i * q - 1 := (hε.pow_eq_one_iff_dvd _).1 <|
      mul_right_cancel₀ (hε.ne_zero (NeZero.ne N)) <| by
        rw [← pow_succ, Nat.sub_add_cancel hpos, hpow, one_mul]
    exact ((Nat.modEq_iff_dvd' hpos).2 hd).symm
  · obtain rfl : N = 1 := le_antisymm hN (Nat.pos_of_ne_zero (NeZero.ne N))
    exact Nat.modEq_one

/-- **The geometric Frobenius on the stalk of the Tate twist**: an endomorphism `f` of the
geometric point acting on `Ω` by a ring map `φ` with `φ(y)^q = y` satisfies
`⟨f a, ζ⟩ = q · f ⟨a, ζ⟩` on the stalk of `𝓗om(μ_N, G)`, for the germ `ζ` of a primitive `N`-th
root of unity. So under `a ↦ ⟨a, ζ⟩`, the action of `f` on the stalk of `G(-1)` is `q` times its
action on the stalk of `G`. -/
theorem twistNegOneFiberPairing_presheafFiber_hom
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod N)))
    (f : Scheme.pointSmallEtale s ⟶ Scheme.pointSmallEtale s) (φ : Ω →+* Ω)
    (hf : ∀ (U : X.Etale) (u : (Scheme.pointSmallEtale s).fiber.obj U),
      fiberLift s (f.hom.app U u) = Spec.map (CommRingCat.ofHom φ) ≫ fiberLift s u)
    (q : ℕ) (hq : ∀ y, φ y ^ q = y) {V : X.Etale} (v : (Scheme.pointSmallEtale s).fiber.obj V)
    {k : Type u} [Field k] (κ : k →+* Γ(V.left, ⊤)) {ζ : k} (hζ : IsPrimitiveRoot ζ N)
    (a : ToType ((Scheme.pointSmallEtale s).presheafFiber.obj
      (twistNegOneModule.{u, 0} X N G).obj)) :
    fiberPairing (Scheme.pointSmallEtale s)
        (fun U α s => twistNegOneModulePairing.{u, 0} X N G U α s)
        ((Point.Hom.presheafFiber f).app (twistNegOneModule.{u, 0} X N G).obj a)
        ((Scheme.pointSmallEtale s).toPresheafFiber V v (rootsOfUnityModule.{u, 0} X N).obj
          (rootSection N κ hζ 1)) =
      q • (Point.Hom.presheafFiber f).app G.obj (fiberPairing (Scheme.pointSmallEtale s)
        (fun U α s => twistNegOneModulePairing.{u, 0} X N G U α s) a
        ((Scheme.pointSmallEtale s).toPresheafFiber V v (rootsOfUnityModule.{u, 0} X N).obj
          (rootSection N κ hζ 1))) := by
  have := preservesFilteredColimitsOfSize_forget_moduleCat.{u, u} (ZMod N)
  obtain ⟨i, hiq, he⟩ := exists_presheafFiber_hom_root_eq_nsmul s N f φ hf q hq v κ hζ
  have hp := fiberPairing_presheafFiber_hom.{u, u}
    (fun U α s => twistNegOneModulePairing.{u, 0} X N G U α s)
    (twistNegOneModulePairing_naturality.{u, 0} X N G) f a
    ((Scheme.pointSmallEtale s).toPresheafFiber V v (rootsOfUnityModule.{u, 0} X N).obj
      (rootSection N κ hζ 1))
  rw [he, fiberPairing_nsmul_right (Scheme.pointSmallEtale s)
    (fun U α s => twistNegOneModulePairing.{u, 0} X N G U α s)
    (twistNegOneModulePairing_naturality.{u, 0} X N G)
    (fun U z s i => map_nsmul (twistNegOneModulePairing.{u, 0} X N G U z) i s)] at hp
  rw [← hp, smul_smul]
  set x := fiberPairing (Scheme.pointSmallEtale s)
    (fun U α s => twistNegOneModulePairing.{u, 0} X N G U α s)
    ((Point.Hom.presheafFiber f).app (twistNegOneModule.{u, 0} X N G).obj a)
    ((Scheme.pointSmallEtale s).toPresheafFiber V v (rootsOfUnityModule.{u, 0} X N).obj
      (rootSection N κ hζ 1))
  have hN : N • x = 0 := ZModModule.char_nsmul_eq_zero N x
  rw [nsmul_eq_mod_nsmul_of_nsmul_eq_zero N hN (q * i), mul_comm q i, hiq,
    ← nsmul_eq_mod_nsmul_of_nsmul_eq_zero N hN 1, one_nsmul]

end Germs

end Stacks.Kummer

end
