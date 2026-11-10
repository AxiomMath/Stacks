module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.PointPullbackDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingOnObjectsGluing
public import StacksFrontier.AlgebraicGeometry.Stacks.FpqcDescent.Stack
public import StacksFrontier.AlgebraicGeometry.Stacks.AffineDiagonalAbsolute
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.ModuleExtensionSheaf

/-!
# Descending a point from a trivialization of a tensor functor after faithfully flat base change

Let `𝒳` be an algebraic stack with affine diagonal, `F : QCoh(𝒪_𝒳) ⥤ Mod_R` a tensor functor,
`π : R ⟶ T` faithfully flat, and `θ : T ⊗_R F(-) ≅ x_T^*` an isomorphism of tensor functors for a
point `x_T` of `𝒳` over `Spec T`. This file shows that `x_T` descends to a point `x` over
`Spec R` with `F ≅ x^*` as tensor functors: the two pullbacks of `x_T` to `Spec (T ⊗_R T)` are
glued by Stacks 0GRP, the gluing satisfies the cocycle condition by the rigidity of the gluing
2-arrows, and the descent datum is effective because `𝒳` is an fpqc stack (Stacks 0GRH). This is
the second half of the proof of Stacks 0GRQ.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.RestrictEq`: two arrows `z ⟶ x_T` restrict the
  elements `θ(1 ⊗ f)` in the same way.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.eq_of_restrictEq`: rigidity of the gluing 2-arrows over
  an affine base.
* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_iso_pointPullback_of_trivialization`: the
  descent.

## References

* [Stacks Project, Tag 0GRQ](https://stacks.math.columbia.edu/tag/0GRQ)
* [Stacks Project, Tag 0GRH](https://stacks.math.columbia.edu/tag/0GRH)
* [Stacks Project, Tag 0GRP](https://stacks.math.columbia.edu/tag/0GRP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

attribute [local instance] hasSheafCompose_forget_ringCat
  hasSheafCompose_forget_commRingCat Stacks.hasSheafCompose_forget₂_commRingCat
  FlatFppf.hasSheafify_addCommGrpCat FlatFppf.wEqualsLocallyBijective_addCommGrpCat
  FlatFppf.hasSheafify_fppf_addCommGrpCat FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat
  FlatFppf.hasSheafify_associatedTopology_ab
  FlatFppf.wEqualsLocallyBijective_fppfTopology_addCommGrpCat
attribute [local instance] fppfModulesMonoidal fppfModulesBraided fppfModulesSymmetric


section Generic

/-- A morphism over an identity, through an `eqToHom` of its source and target. -/
theorem map_eq_eqToHom_of_isHomLift_id {𝒳 𝒮 : Type*} [Category 𝒳] [Category 𝒮]
    (p : 𝒳 ⥤ 𝒮) {Z : 𝒮} {a b : 𝒳} (φ : a ⟶ b) [p.IsHomLift (𝟙 Z) φ] (ha : p.obj a = Z)
    (hb : p.obj b = Z) : p.map φ = eqToHom (ha.trans hb.symm) := by
  rw [IsHomLift.fac' p (𝟙 Z) φ, Category.id_comp, eqToHom_trans]

/-- The image of an `eqToHom` is compatible with identifications through `eqToIso`. -/
theorem map_comp_eqToIso_trans {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {X Y Z : C} (hX : X = Z) (hY : Y = Z) {W : D} (E : G.obj Z ≅ W) (φ : X ⟶ Y)
    (hφ : φ = eqToHom (hX.trans hY.symm)) :
    G.map φ ≫ (eqToIso (congrArg G.obj hY) ≪≫ E).hom = (eqToIso (congrArg G.obj hX) ≪≫ E).hom := by
  subst hφ hX hY
  simp

/-- The image of a morphism lying over `k`, through `eqToHom`s of its source and target. -/
theorem map_map_comp_eqToHom_of_isHomLift {𝒳 𝒮 D : Type*} [Category 𝒳] [Category 𝒮]
    [Category D] (p : 𝒳 ⥤ 𝒮) (G : 𝒮 ⥤ D) {X Y : 𝒮} {a b : 𝒳} (k : X ⟶ Y) (φ : a ⟶ b)
    [p.IsHomLift k φ] (ha : p.obj a = X) (hb : p.obj b = Y) :
    G.map (p.map φ) ≫ eqToHom (congrArg G.obj hb) = eqToHom (congrArg G.obj ha) ≫ G.map k := by
  rw [IsHomLift.fac' p k φ]
  simp [eqToHom_map]

/-- A morphism whose image, read through identifications `eqToIso ≪≫ E` of its source and target,
is the identity lies over the identity. -/
theorem isHomLift_id_of_map_comp_eqToIso {𝒳 𝒮 D : Type*} [Category 𝒳] [Category 𝒮]
    [Category D] (p : 𝒳 ⥤ 𝒮) (G : 𝒮 ⥤ D) [G.Faithful] {Z : 𝒮} {a b : 𝒳} (φ : a ⟶ b)
    (ha : p.obj a = Z) (hb : p.obj b = Z) {W : D} (E : G.obj Z ≅ W)
    (h : G.map (p.map φ) ≫ (eqToIso (congrArg G.obj hb) ≪≫ E).hom =
      (eqToIso (congrArg G.obj ha) ≪≫ E).hom) : p.IsHomLift (𝟙 Z) φ := by
  subst hb
  have h' : G.map (p.map φ) = G.map (eqToHom ha) := by
    rw [eqToHom_map]
    simpa using h
  refine IsHomLift.of_fac' p _ φ ha rfl ?_
  rw [G.map_injective h']
  simp

end Generic

section RestrictEq

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : AlgebraicStacks.{u, w} B S hS} {R T : Type u} [CommRing R] [CommRing T] {π : R →+* T}
  {F : quasicoherentModules B S hS 𝒳 ⥤ ModuleCat.{u} R} {xT : 𝒳.val.val.obj}
  {eT : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj xT) ≅ Spec (CommRingCat.of T)}
  (θ : F ⋙ ModuleCat.extendScalars π ≅ pointPullback B S hS 𝒳 xT eT)

/-- Two arrows `ζ₁ ζ₂ : z ⟶ x_T` **restrict the trivialization `θ` in the same way**: the
restrictions of `θ(1 ⊗ f)` along them agree, for every `f ∈ F(M)`. -/
def RestrictEq {z : 𝒳.val.val.obj} (ζ₁ ζ₂ : z ⟶ xT) : Prop :=
  ∀ (M : quasicoherentModules B S hS 𝒳) (f : F.obj M),
    (M.obj.val.map ζ₁.op).hom ((θ.hom.app M).hom ((1 : T) ⊗ₜ[R, π] f)) =
      (M.obj.val.map ζ₂.op).hom ((θ.hom.app M).hom ((1 : T) ⊗ₜ[R, π] f))

variable {θ}

/-- Every arrow `ζ : z ⟶ x_T` restricts `θ` in the same way as itself. -/
theorem RestrictEq.refl {z : 𝒳.val.val.obj} (ζ : z ⟶ xT) : RestrictEq θ ζ ζ :=
  fun _ _ => rfl

/-- `RestrictEq θ` is symmetric. -/
theorem RestrictEq.symm {z : 𝒳.val.val.obj} {ζ₁ ζ₂ : z ⟶ xT} (h : RestrictEq θ ζ₁ ζ₂) :
    RestrictEq θ ζ₂ ζ₁ :=
  fun M f => (h M f).symm

/-- `RestrictEq θ` is transitive. -/
theorem RestrictEq.trans {z : 𝒳.val.val.obj} {ζ₁ ζ₂ ζ₃ : z ⟶ xT} (h : RestrictEq θ ζ₁ ζ₂)
    (h' : RestrictEq θ ζ₂ ζ₃) : RestrictEq θ ζ₁ ζ₃ :=
  fun M f => (h M f).trans (h' M f)

/-- The condition only depends on the two arrows. -/
theorem RestrictEq.of_eq {z : 𝒳.val.val.obj} {ζ₁ ζ₂ ζ₁' ζ₂' : z ⟶ xT} (h₁ : ζ₁ = ζ₁')
    (h₂ : ζ₂ = ζ₂') (h : RestrictEq θ ζ₁ ζ₂) : RestrictEq θ ζ₁' ζ₂' := by
  subst h₁ h₂
  exact h

/-- The condition is stable under precomposition. -/
theorem RestrictEq.comp {z z' : 𝒳.val.val.obj} (l : z' ⟶ z) {ζ₁ ζ₂ : z ⟶ xT}
    (h : RestrictEq θ ζ₁ ζ₂) : RestrictEq θ (l ≫ ζ₁) (l ≫ ζ₂) := by
  intro M f
  have h₁ := M.obj.val.map_comp_apply ζ₁.op l.op ((θ.hom.app M).hom ((1 : T) ⊗ₜ[R, π] f))
  have h₂ := M.obj.val.map_comp_apply ζ₂.op l.op ((θ.hom.app M).hom ((1 : T) ⊗ₜ[R, π] f))
  rw [← op_comp] at h₁ h₂
  exact h₁.trans ((congrArg (M.obj.val.map l.op).hom (h M f)).trans h₂.symm)

/-- Transporting `RestrictEq θ` across an isomorphism of the source. -/
private theorem RestrictEq.inv_comp_iff {z z' : 𝒳.val.val.obj} (e : z ≅ z') {ζ₁ : z ⟶ xT}
    {ζ₂ : z' ⟶ xT} : RestrictEq θ (e.inv ≫ ζ₁) ζ₂ ↔ RestrictEq θ ζ₁ (e.hom ≫ ζ₂) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa using h.comp e.hom
  · simpa using h.comp e.inv

end RestrictEq

section Rigidity

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : AlgebraicStacks.{u, w} B S hS}

/-- A morphism of a fibre of an algebraic stack is an isomorphism. -/
theorem isIso_fiberInclusion_map {Z : BigFppfOver B S hS} {z z' : 𝒳.val.val.p.Fiber Z}
    (a : z ⟶ z') : IsIso (a.1) := by
  have : 𝒳.val.val.p.IsHomLift (𝟙 Z) a.1 := a.2
  have := 𝒳.val.isFiberedInGroupoids.isStronglyCartesian_homLift (𝟙 Z) a.1
  exact Functor.IsStronglyCartesian.isIso_of_base_isIso 𝒳.val.val.p (𝟙 Z) a.1

/-- The scheme of a point lying over an affine object, identified with the spectrum of its global
sections. -/
def fiberSpecIso {Z : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj Z)]
    (z : 𝒳.val.val.p.Fiber Z) :
    (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj z.1) ≅
      Spec (CommRingCat.of Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)) :=
  eqToIso (congrArg (BigFppfOver.toScheme B S hS).obj z.2) ≪≫
    ((BigFppfOver.toScheme B S hS).obj Z).isoSpec

/-- A morphism of the fibre over `Z` is compatible with the identifications `fiberSpecIso`. -/
theorem toScheme_map_comp_fiberSpecIso {Z : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Z)] {z z' : 𝒳.val.val.p.Fiber Z} (a : z ⟶ z') :
    (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map (a.1)) ≫
      (fiberSpecIso z').hom = (fiberSpecIso z).hom := by
  have : 𝒳.val.val.p.IsHomLift (𝟙 Z) a.1 := a.2
  exact map_comp_eqToIso_trans (BigFppfOver.toScheme B S hS) z.2 z'.2 _ _
    (map_eq_eqToHom_of_isHomLift_id 𝒳.val.val.p (Z := Z) a.1 z.2 z'.2)

variable {R T : Type u} [CommRing R] [CommRing T] {π : R →+* T}
  {F : quasicoherentModules B S hS 𝒳 ⥤ ModuleCat.{u} R} {xT : 𝒳.val.val.obj}
  {eT : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj xT) ≅ Spec (CommRingCat.of T)}
  {θ : F ⋙ ModuleCat.extendScalars π ≅ pointPullback B S hS 𝒳 xT eT}

/-- **Rigidity of the gluing 2-arrows over an affine base.** Let `c : U ⟶ 𝒳` be an affine,
smooth and surjective chart. Two morphisms `a b : z ⟶ z'` of the fibre of `𝒳` over an affine
object, with `χ : z ⟶ x_T` and `χ' : z' ⟶ x_T` such that `χ` and `a ≫ χ'` (resp. `b ≫ χ'`)
restrict `θ` in the same way, are equal. -/
theorem eq_of_restrictEq (U : BigFppfOver B S hS)
    (c : schemeStack.{u, w} B S hS U ⟶ 𝒳) (hc : IsAffineHom B S hS c) (hsm : IsSmooth B S hS c)
    (hsurj : IsSurjective B S hS c) {Z : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Z)] {z z' : 𝒳.val.val.p.Fiber Z}
    (a b : z ⟶ z') {χ : z.1 ⟶ xT} {χ' : z'.1 ⟶ xT}
    (ha : RestrictEq θ χ (a.1 ≫ χ'))
    (hb : RestrictEq θ χ (b.1 ≫ χ')) : a = b := by
  let f := (fiberSpecIso z).inv ≫ (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map χ) ≫ eT.hom
  have hχ : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map χ) ≫ eT.hom =
      (fiberSpecIso z).hom ≫ Spec.map (CommRingCat.ofHom (Spec.preimage f).hom) := by
    rw [CommRingCat.ofHom_hom, Spec.map_preimage, Iso.hom_inv_id_assoc]
  have := isIso_fiberInclusion_map a
  have := isIso_fiberInclusion_map b
  have key : asIso a.1 = asIso b.1 := by
    refine eq_of_restrict_hom_app_one_tmul_eq θ U c hc hsm hsurj hχ (χ' := χ')
      (asIso (a.1)) (asIso (b.1))
      (toScheme_map_comp_fiberSpecIso a) (toScheme_map_comp_fiberSpecIso b) ?_ ?_
    · exact (RestrictEq.inv_comp_iff (asIso a.1)).2 ha
    · exact (RestrictEq.inv_comp_iff (asIso b.1)).2 hb
  exact Subtype.ext (congrArg Iso.hom key)

end Rigidity

section Descent

open Functor

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : AlgebraicStacks.{u, w} B S hS} {R T : Type u} [CommRing R] [CommRing T] {π : R →+* T}
  {F : quasicoherentModules B S hS 𝒳 ⥤ ModuleCat.{u} R}
  {hT : B.Contains (Spec (CommRingCat.of T))} {qT : B.obj hT ⟶ B.obj hS} {xT : 𝒳.val.val.obj}
  {hxT : 𝒳.val.val.p.obj xT = Over.mk qT}
  (θ : F ⋙ ModuleCat.extendScalars π ≅ pointPullback B S hS 𝒳 xT (overSpecIso B S hS 𝒳 hxT))

/-- An arrow into `x_T` lying over `Over.homMk f`, read on the schemes `Spec W ⟶ Spec T`. -/
theorem toScheme_map_comp_overSpecIso_of_isHomLift {W : Type u} [CommRing W]
    {hW : B.Contains (Spec (CommRingCat.of W))} (f : B.obj hW ⟶ B.obj hT) (g : T →+* W)
    (hf : B.inclusion.map f = Spec.map (CommRingCat.ofHom g)) {z : 𝒳.val.val.obj}
    (hz : 𝒳.val.val.p.obj z = Over.mk (f ≫ qT)) (χ : z ⟶ xT)
    [𝒳.val.val.p.IsHomLift (Over.homMk f rfl : Over.mk (f ≫ qT) ⟶ Over.mk qT) χ] :
    (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map χ) ≫ (overSpecIso B S hS 𝒳 hxT).hom =
      (overSpecIso B S hS 𝒳 hz).hom ≫ Spec.map (CommRingCat.ofHom g) :=
  (map_map_comp_eqToHom_of_isHomLift 𝒳.val.val.p (BigFppfOver.toScheme B S hS)
    (Over.homMk f rfl : Over.mk (f ≫ qT) ⟶ Over.mk qT) χ hz hxT).trans
      (congrArg ((overSpecIso B S hS 𝒳 hz).hom ≫ ·) hf)

include θ in
/-- **The structure morphism of `x_T` descends to `Spec R`** (Stacks 0GRQ, proof): the two
composites `Spec (T ⊗_R T) ⇉ Spec T ⟶ S` agree by Stacks 0GRP, so `Spec T ⟶ S` factors through
the faithfully flat `Spec T ⟶ Spec R`. -/
theorem exists_comp_eq_of_trivialization
    (hΔ : Stack.IsAffineHom B (⊤_ Scheme.{u}) (contains_terminalScheme B)
      (Stack.diagonal.{u, u, u + 1} B (⊤_ Scheme.{u}) (contains_terminalScheme B)
        (AlgebraicStacks.viewOverIntegers B S hS (contains_terminalScheme B) 𝒳).val))
    [F.LaxMonoidal] [NatTrans.IsMonoidal θ.hom] (hπ : π.FaithfullyFlat) :
    ∃ q' : Spec (CommRingCat.of R) ⟶ S,
      Spec.map (CommRingCat.ofHom π) ≫ q' = B.inclusion.map qT := by
  let := π.toAlgebra
  have hW : B.Contains (Spec (CommRingCat.of (T ⊗[R] T))) :=
    Stacks.Adequate.size_Spec_tensorProduct_lt B.aleph0_lt_cutoff R T T hT hT
  let g₁ : T →+* T ⊗[R] T := Algebra.TensorProduct.includeLeftRingHom
  let g₂ : T →+* T ⊗[R] T :=
    RingHomClass.toRingHom (Algebra.TensorProduct.includeRight : T →ₐ[R] T ⊗[R] T)
  let pr₁ : B.obj hW ⟶ B.obj hT := B.inclusion.preimage (Spec.map (CommRingCat.ofHom g₁))
  let pr₂ : B.obj hW ⟶ B.obj hT := B.inclusion.preimage (Spec.map (CommRingCat.ofHom g₂))
  let k₁ : Over.mk (pr₁ ≫ qT) ⟶ Over.mk qT := Over.homMk pr₁ rfl
  let k₂ : Over.mk (pr₂ ≫ qT) ⟶ Over.mk qT := Over.homMk pr₂ rfl
  have : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  let X₀ : 𝒳.val.val.p.Fiber (Over.mk qT) := ⟨xT, hxT⟩
  let z₁ := pullbackFiber 𝒳.val.val.p X₀ k₁
  let z₂ := pullbackFiber 𝒳.val.val.p X₀ k₂
  let χ₁ : z₁.1 ⟶ xT := IsPreFibered.pullbackMap X₀.2 k₁
  let χ₂ : z₂.1 ⟶ xT := IsPreFibered.pullbackMap X₀.2 k₂
  have : 𝒳.val.val.p.IsHomLift k₁ χ₁ := (IsPreFibered.pullbackMap.IsCartesian X₀.2 k₁).toIsHomLift
  have : 𝒳.val.val.p.IsHomLift k₂ χ₂ := (IsPreFibered.pullbackMap.IsCartesian X₀.2 k₂).toIsHomLift
  have hχ₁ := toScheme_map_comp_overSpecIso_of_isHomLift (hxT := hxT) pr₁ g₁
    (B.inclusion.map_preimage _) z₁.2 χ₁
  have hχ₂ := toScheme_map_comp_overSpecIso_of_isHomLift (hxT := hxT) pr₂ g₂
    (B.inclusion.map_preimage _) z₂.2 χ₂
  have hq := eq_of_restrict_hom_app_one_tmul θ hΔ z₁.2 z₂.2 hχ₁ hχ₂
    Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
  refine exists_spec_map_comp_eq_of_faithfullyFlat R T hπ (B.inclusion.map qT) ?_
  have h := congrArg B.inclusion.map hq
  rwa [Functor.map_comp, Functor.map_comp, B.inclusion.map_preimage,
    B.inclusion.map_preimage] at h

/-- An arrow into `x_T` lying over `k : Z ⟶ Spec T` with `k = E ≫ Spec g`, read on schemes. -/
theorem toScheme_map_comp_overSpecIso_of_isHomLift_of_iso {W : Type u} [CommRing W]
    {Z : BigFppfOver B S hS} (E : (BigFppfOver.toScheme B S hS).obj Z ≅ Spec (CommRingCat.of W))
    (k : Z ⟶ Over.mk qT) (g : T →+* W)
    (hk : (BigFppfOver.toScheme B S hS).map k = E.hom ≫ Spec.map (CommRingCat.ofHom g))
    {z : 𝒳.val.val.obj} (hz : 𝒳.val.val.p.obj z = Z) (χ : z ⟶ xT) [𝒳.val.val.p.IsHomLift k χ] :
    (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map χ) ≫ (overSpecIso B S hS 𝒳 hxT).hom =
      (eqToIso (congrArg (BigFppfOver.toScheme B S hS).obj hz) ≪≫ E).hom ≫
        Spec.map (CommRingCat.ofHom g) :=
  (map_map_comp_eqToHom_of_isHomLift 𝒳.val.val.p (BigFppfOver.toScheme B S hS) k χ hz hxT).trans
    ((congrArg (eqToHom (congrArg (BigFppfOver.toScheme B S hS).obj hz) ≫ ·) hk).trans
      (Category.assoc _ _ _).symm)

include θ in
/-- **Descent of a point along a faithfully flat base change trivializing a tensor functor**
(Stacks 0GRQ, proof). Let `𝒳` be an algebraic stack with affine (absolute) diagonal and an affine,
smooth and surjective chart `c : U ⟶ 𝒳`, `F : QCoh(𝒪_𝒳) ⥤ Mod_R` a tensor functor, `π : R ⟶ T`
faithfully flat with `Spec R`, `Spec T` in the site, and `θ : T ⊗_R F(-) ≅ x_T^*` an isomorphism
of tensor functors for a point `x_T` of `𝒳` over `Spec T`. Then there is a point `x` of `𝒳` over
`Spec R` with `F ≅ x^*` as tensor functors. -/
theorem exists_iso_pointPullback_of_trivialization
    (hΔ : Stack.IsAffineHom B (⊤_ Scheme.{u}) (contains_terminalScheme B)
      (Stack.diagonal.{u, u, u + 1} B (⊤_ Scheme.{u}) (contains_terminalScheme B)
        (AlgebraicStacks.viewOverIntegers B S hS (contains_terminalScheme B) 𝒳).val))
    (U : BigFppfOver B S hS) (c : schemeStack.{u, w} B S hS U ⟶ 𝒳) (hc : IsAffineHom B S hS c)
    (hsm : IsSmooth B S hS c) (hsurj : IsSurjective B S hS c)
    [F.Monoidal] [NatTrans.IsMonoidal θ.hom] (hR : B.Contains (Spec (CommRingCat.of R)))
    (hπ : π.FaithfullyFlat) :
    ∃ (q : B.obj hR ⟶ B.obj hS) (x : 𝒳.val.val.obj) (hx : 𝒳.val.val.p.obj x = Over.mk q)
      (e : F ≅ pointPullback B S hS 𝒳 x (overSpecIso B S hS 𝒳 hx)), NatTrans.IsMonoidal e.hom := by
  let := π.toAlgebra
  obtain ⟨q', hq'⟩ := exists_comp_eq_of_trivialization θ hΔ hπ
  let q : B.obj hR ⟶ B.obj hS := B.inclusion.preimage q'
  let πs : B.obj hT ⟶ B.obj hR := B.inclusion.preimage (Spec.map (CommRingCat.ofHom π))
  have hw : πs ≫ q = qT := B.inclusion.map_injective (by
    rw [Functor.map_comp, B.inclusion.map_preimage, B.inclusion.map_preimage]
    exact hq')
  let V : BigFppfOver B S hS := Over.mk qT
  let v : V ⟶ Over.mk q := Over.homMk πs hw
  have : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  have hp := 𝒳.val.isFiberedInGroupoids
  let X₀ : 𝒳.val.val.p.Fiber V := ⟨xT, hxT⟩
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj V) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of T)))
  have := Space.preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have hv : (BigFppfOver.toScheme B S hS).map v =
      Spec.map (CommRingCat.ofHom (algebraMap R T)) :=
    B.inclusion.map_preimage _
  let eP : (BigFppfOver.toScheme B S hS).obj (pullback v v) ≅
      Spec (CommRingCat.of (T ⊗[R] T)) :=
    PreservesPullback.iso (BigFppfOver.toScheme B S hS) v v ≪≫ pullback.congrHom hv hv ≪≫
      pullbackSpecIso R T T
  have hfst : (BigFppfOver.toScheme B S hS).map (pullback.fst v v ≫ 𝟙 V) =
      eP.hom ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) := by
    simp only [eP, Iso.trans_hom, Category.assoc, pullbackSpecIso_hom_fst,
      pullback.congrHom_hom, pullback.lift_fst, Category.comp_id]
    exact (PreservesPullback.iso_hom_fst _ _ _).symm
  have hsnd : (BigFppfOver.toScheme B S hS).map (pullback.snd v v ≫ 𝟙 V) =
      eP.hom ≫ Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
        (Algebra.TensorProduct.includeRight : T →ₐ[R] T ⊗[R] T))) := by
    simp only [eP, Iso.trans_hom, Category.assoc, pullbackSpecIso_hom_snd,
      pullback.congrHom_hom, pullback.lift_snd, Category.comp_id]
    exact (PreservesPullback.iso_hom_snd _ _ _).symm
  let y₁ := pullbackFiber 𝒳.val.val.p X₀ (pullback.fst v v ≫ 𝟙 V)
  let y₂ := pullbackFiber 𝒳.val.val.p X₀ (pullback.snd v v ≫ 𝟙 V)
  let χ₁ : y₁.1 ⟶ xT := IsPreFibered.pullbackMap X₀.2 (pullback.fst v v ≫ 𝟙 V)
  let χ₂ : y₂.1 ⟶ xT := IsPreFibered.pullbackMap X₀.2 (pullback.snd v v ≫ 𝟙 V)
  have i₁ : 𝒳.val.val.p.IsHomLift (pullback.fst v v ≫ 𝟙 V) χ₁ :=
    (IsPreFibered.pullbackMap.IsCartesian X₀.2 _).toIsHomLift
  have i₂ : 𝒳.val.val.p.IsHomLift (pullback.snd v v ≫ 𝟙 V) χ₂ :=
    (IsPreFibered.pullbackMap.IsCartesian X₀.2 _).toIsHomLift
  let e₁ := eqToIso (congrArg (BigFppfOver.toScheme B S hS).obj y₁.2) ≪≫ eP
  let e₂ := eqToIso (congrArg (BigFppfOver.toScheme B S hS).obj y₂.2) ≪≫ eP
  have hχ₁ := toScheme_map_comp_overSpecIso_of_isHomLift_of_iso (hxT := hxT) eP _ _ hfst y₁.2 χ₁
  have hχ₂ := toScheme_map_comp_overSpecIso_of_isHomLift_of_iso (hxT := hxT) eP _ _ hsnd y₂.2 χ₂
  obtain ⟨a, ha, hPa⟩ := exists_iso_restrict_hom_app_one_tmul_eq θ hΔ hχ₁ hχ₂
    Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
  have ia : 𝒳.val.val.p.IsHomLift (𝟙 (pullback v v)) a.hom :=
    isHomLift_id_of_map_comp_eqToIso 𝒳.val.val.p (BigFppfOver.toScheme B S hS) a.hom y₁.2 y₂.2
      eP ha
  have hκĥ : RestrictEq θ χ₁ (a.hom ≫ χ₂) := (RestrictEq.inv_comp_iff a).1 hPa
  let K : GlueKernel.Kernel 𝒳.val.val.p :=
    { V₀ := V, V := V, U := Over.mk q, τ := 𝟙 V, v := v, X₀ := X₀, E := y₁.1, κ := χ₁,
      ĥ := a.hom ≫ χ₂, isHomLift_κ := i₁,
      isHomLift_ĥ := by
        have : 𝒳.val.val.p.IsHomLift (𝟙 (pullback v v) ≫ pullback.snd v v ≫ 𝟙 V) (a.hom ≫ χ₂) :=
          inferInstance
        rwa [Category.id_comp] at this }
  have htr : ∀ ⦃Z : BigFppfOver B S hS⦄ (e₁ e₂ : Z ⟶ V) (h : e₁ ≫ v = e₂ ≫ v),
      RestrictEq θ (IsPreFibered.pullbackMap X₀.2 (e₁ ≫ 𝟙 V))
        (Functor.Fiber.fiberInclusion.map (GlueKernel.transition hp K e₁ e₂ h) ≫
          IsPreFibered.pullbackMap X₀.2 (e₂ ≫ 𝟙 V)) := fun Z e₁ e₂ h =>
    RestrictEq.of_eq (GlueKernel.transitionLift_fac hp K e₁ e₂ h)
      (GlueKernel.transition_fac hp K e₁ e₂ h).symm
      (RestrictEq.comp (GlueKernel.transitionLift hp K e₁ e₂ h) hκĥ)
  have h0 : GlueKernel.transition hp K (𝟙 V) (𝟙 V) rfl = 𝟙 _ :=
    eq_of_restrictEq U c hc hsm hsurj (Z := V) _ _ (htr (𝟙 V) (𝟙 V) rfl)
      (RestrictEq.of_eq rfl (Category.id_comp _).symm (RestrictEq.refl _))
  have hself : ∀ ⦃Z : BigFppfOver B S hS⦄ (e : Z ⟶ V),
      GlueKernel.transition hp K (e ≫ 𝟙 V) (e ≫ 𝟙 V) rfl = 𝟙 _ := fun Z e =>
    GlueKernel.transition_self_of_pullbackFiberHom hp K (𝟙 V) (e ≫ 𝟙 V) (e ≫ 𝟙 V)
      (Category.comp_id _)
      ((congrArg (fun m => pullbackFiberHom m (e ≫ 𝟙 V)) h0).trans (pullbackFiberHom_id _))
  let Z₀ := pullback (pullback.snd v v) (pullback.fst v v)
  let r₁ : Z₀ ⟶ V := pullback.fst _ _ ≫ pullback.fst v v
  let r₂ : Z₀ ⟶ V := pullback.fst _ _ ≫ pullback.snd v v
  let r₃ : Z₀ ⟶ V := pullback.snd _ _ ≫ pullback.snd v v
  have c₁₂ : r₁ ≫ v = r₂ ≫ v :=
    (Category.assoc _ _ _).trans ((congrArg (pullback.fst _ _ ≫ ·) pullback.condition).trans
      (Category.assoc _ _ _).symm)
  have c₂₃ : r₂ ≫ v = r₃ ≫ v :=
    (congrArg (· ≫ v) pullback.condition).trans ((Category.assoc _ _ _).trans
      ((congrArg (pullback.snd _ _ ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm))
  have c₁₃ : r₁ ≫ v = r₃ ≫ v := c₁₂.trans c₂₃
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (pullback v v)) := IsAffine.of_isIso eP.hom
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj Z₀) :=
    IsAffine.of_isIso (PreservesPullback.iso (BigFppfOver.toScheme B S hS) _ _).hom
  have hT3 : GlueKernel.transition hp K r₁ r₂ c₁₂ ≫ GlueKernel.transition hp K r₂ r₃ c₂₃ =
      GlueKernel.transition hp K r₁ r₃ c₁₃ :=
    eq_of_restrictEq U c hc hsm hsurj (Z := Z₀) _ _
      (RestrictEq.of_eq rfl (Category.assoc _ _ _).symm
        ((htr r₁ r₂ c₁₂).trans ((htr r₂ r₃ c₂₃).comp _))) (htr r₁ r₃ c₁₃)
  have hcomp : ∀ ⦃Z : BigFppfOver B S hS⦄ (e₁ e₂ e₃ : Z ⟶ V) (h₁₂ : e₁ ≫ v = e₂ ≫ v)
      (h₂₃ : e₂ ≫ v = e₃ ≫ v) (h₁₃ : e₁ ≫ v = e₃ ≫ v),
      GlueKernel.transition hp K (e₁ ≫ 𝟙 V) (e₂ ≫ 𝟙 V) (by simpa using h₁₂) ≫
        GlueKernel.transition hp K (e₂ ≫ 𝟙 V) (e₃ ≫ 𝟙 V) (by simpa using h₂₃) =
      GlueKernel.transition hp K (e₁ ≫ 𝟙 V) (e₃ ≫ 𝟙 V) (by simpa using h₁₃) := by
    intro Z e₁ e₂ e₃ h₁₂ h₂₃ h₁₃
    have h₁₂' : (e₁ ≫ 𝟙 V) ≫ v = (e₂ ≫ 𝟙 V) ≫ v := by simpa using h₁₂
    have h₂₃' : (e₂ ≫ 𝟙 V) ≫ v = (e₃ ≫ 𝟙 V) ≫ v := by simpa using h₂₃
    let g : Z ⟶ Z₀ := pullback.lift (pullback.lift (e₁ ≫ 𝟙 V) (e₂ ≫ 𝟙 V) h₁₂')
      (pullback.lift (e₂ ≫ 𝟙 V) (e₃ ≫ 𝟙 V) h₂₃')
      ((pullback.lift_snd _ _ _).trans (pullback.lift_fst _ _ _).symm)
    have he₁ : g ≫ r₁ = e₁ ≫ 𝟙 V := (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ pullback.fst v v) (pullback.lift_fst _ _ _)).trans (pullback.lift_fst _ _ _))
    have he₂ : g ≫ r₂ = e₂ ≫ 𝟙 V := (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ pullback.snd v v) (pullback.lift_fst _ _ _)).trans (pullback.lift_snd _ _ _))
    have he₃ : g ≫ r₃ = e₃ ≫ 𝟙 V := (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ pullback.snd v v) (pullback.lift_snd _ _ _)).trans (pullback.lift_snd _ _ _))
    exact GlueKernel.transition_comp_of_pullbackFiberHom hp K r₁ r₂ r₃ c₁₂ c₂₃ c₁₃ g
      (e₁ ≫ 𝟙 V) (e₂ ≫ 𝟙 V) (e₃ ≫ 𝟙 V) he₁ he₂ he₃
      _ _ _ (congrArg (fun m => pullbackFiberHom m g) hT3)
  have hpS : 𝒳.val.val.p.IsStack
      (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck :=
    isStack_fpqc_of_isQuasiAffineHom_diagonal 𝒳.val 𝒳.2
      (isQuasiAffineHom_diagonal_of_viewOverIntegers B S hS (contains_terminalScheme B) 𝒳
        ⟨isRepresentableByAlgebraicSpaces_diagonal_algebraicStack B (⊤_ Scheme.{u})
          (contains_terminalScheme B) _, hΔ⟩)
  have hv' : Sieve.ofArrows (fun _ : Unit => V) (fun _ => v) ∈
      (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck (Over.mk q) := by
    have hfs := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap R T))).2 hπ
    rw [Sieve.ofArrows, Presieve.ofArrows_pUnit]
    refine Space.sieve_generate_singleton_mem_fpqcTopology_over B S hS v ?_ ?_ ?_
    · rw [hv]; exact hfs.2
    · rw [hv]; exact hfs.1
    · rw [hv]
      have : AlgebraicGeometry.IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap R T))) :=
        AlgebraicGeometry.isAffineHom_of_isAffine _
      infer_instance
  have hσ : 𝟙 V ≫ K.v = v ≫ 𝟙 (Over.mk q) := (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨x', ζ, iζ, hζ⟩ := GlueKernel.exists_stageGlue hp K (𝟙 V) v (𝟙 _) hσ hpS hv' hself hcomp
  let O := GlueKernel.stageObj K (𝟙 V)
  let ι : O.1 ⟶ xT := IsPreFibered.pullbackMap X₀.2 (𝟙 V ≫ 𝟙 V)
  have iι : 𝒳.val.val.p.IsHomLift (𝟙 V) ι := by
    have : 𝒳.val.val.p.IsHomLift (𝟙 V ≫ 𝟙 V) ι :=
      (IsPreFibered.pullbackMap.IsCartesian X₀.2 _).toIsHomLift
    rwa [Category.comp_id] at this
  have : IsIso ι := isIso_fiberInclusion_map (z := O) (z' := X₀) ⟨ι, iι⟩
  let ψ : xT ⟶ x'.1 := inv ι ≫ ζ
  have iψ : 𝒳.val.val.p.IsHomLift v ψ := by
    have h1 : 𝒳.val.val.p.IsHomLift (𝟙 V) (inv ι) :=
      @IsHomLift.lift_id_inv_isIso _ _ _ _ 𝒳.val.val.p V _ _ ι _ iι
    have : 𝒳.val.val.p.IsHomLift (𝟙 V ≫ v) (inv ι ≫ ζ) :=
      @IsHomLift.comp _ _ _ _ 𝒳.val.val.p _ _ _ _ _ _ (𝟙 V) v (inv ι) ζ h1 iζ
    rwa [Category.id_comp] at this
  have hψ : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map ψ) ≫
      (overSpecIso B S hS 𝒳 x'.2).hom =
        (overSpecIso B S hS 𝒳 hxT).hom ≫ Spec.map (CommRingCat.ofHom π) :=
    (map_map_comp_eqToHom_of_isHomLift 𝒳.val.val.p (BigFppfOver.toScheme B S hS) v ψ hxT
      x'.2).trans (congrArg ((overSpecIso B S hS 𝒳 hxT).hom ≫ ·) hv)
  let y'₁ := pullbackFiber 𝒳.val.val.p O (pullback.fst v v)
  let y'₂ := pullbackFiber 𝒳.val.val.p O (pullback.snd v v)
  let φ₁ : y'₁.1 ⟶ xT := GlueKernel.stageMap K (𝟙 V) (pullback.fst v v)
  let φ₂ : y'₂.1 ⟶ xT := GlueKernel.stageMap K (𝟙 V) (pullback.snd v v)
  have hlift : ∀ f : pullback v v ⟶ V,
      𝒳.val.val.p.IsHomLift (f ≫ 𝟙 V) (GlueKernel.stageMap K (𝟙 V) f) := fun f => by
    have := (GlueKernel.stageMap_isCartesian K (𝟙 V) f).toIsHomLift
    rwa [Category.comp_id] at this
  have := hlift (pullback.fst v v)
  have := hlift (pullback.snd v v)
  have hφ₁ := toScheme_map_comp_overSpecIso_of_isHomLift_of_iso (hxT := hxT) eP _ _ hfst y'₁.2 φ₁
  have hφ₂ := toScheme_map_comp_overSpecIso_of_isHomLift_of_iso (hxT := hxT) eP _ _ hsnd y'₂.2 φ₂
  let m := GlueKernel.stageHom hp K (𝟙 V) v (𝟙 _) hσ (pullback.fst v v) (pullback.snd v v)
    pullback.condition
  have : IsIso m.1 := isIso_fiberInclusion_map m
  have : 𝒳.val.val.p.IsHomLift (𝟙 (pullback v v)) m.1 := m.2
  have ha' : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map (asIso m.1).hom) ≫
      (eqToIso (congrArg (BigFppfOver.toScheme B S hS).obj y'₂.2) ≪≫ eP).hom =
        (eqToIso (congrArg (BigFppfOver.toScheme B S hS).obj y'₁.2) ≪≫ eP).hom :=
    map_comp_eqToIso_trans (BigFppfOver.toScheme B S hS) y'₁.2 y'₂.2 _ _
      (map_eq_eqToHom_of_isHomLift_id 𝒳.val.val.p (Z := pullback v v) m.1 y'₁.2 y'₂.2)
  have hR1 : RestrictEq θ φ₁ (m.1 ≫ φ₂) :=
    RestrictEq.of_eq (GlueKernel.stageLift_fac hp K (𝟙 V) v (𝟙 _) hσ _ _ pullback.condition)
      (GlueKernel.stageHom_fac hp K (𝟙 V) v (𝟙 _) hσ _ _ pullback.condition).symm
      (RestrictEq.comp (GlueKernel.stageLift hp K (𝟙 V) v (𝟙 _) hσ _ _ pullback.condition) hκĥ)
  have hPa' : RestrictEq θ ((asIso m.1).inv ≫ φ₁) φ₂ :=
    (RestrictEq.inv_comp_iff (asIso m.1)).2 hR1
  have hcomp' : (asIso m.1).inv ≫ φ₁ ≫ ψ = φ₂ ≫ ψ := by
    have h := hζ (pullback.fst v v) (pullback.snd v v) pullback.condition
    change (asIso m.1).inv ≫ (IsPreFibered.pullbackMap O.2 (pullback.fst v v) ≫ ι) ≫ inv ι ≫ ζ =
      (IsPreFibered.pullbackMap O.2 (pullback.snd v v) ≫ ι) ≫ inv ι ≫ ζ
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    rw [h]
    exact Iso.inv_hom_id_assoc (asIso m.1) _
  obtain ⟨e', he'⟩ := exists_iso_pointPullback_of_gluing θ hπ hψ hφ₁ hφ₂ (asIso m.1) ha' hPa'
    hcomp'
  exact ⟨q, x'.1, x'.2, e', he'⟩

end Descent

end AlgebraicGeometry.Stack.AlgebraicStacks
