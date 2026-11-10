module

public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.StackGroupoid
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.Nerve
public import StacksFrontier.CategoryTheory.Sites.Stack.IsomPresheaf

/-!
# The arrows of the groupoid of a chart as sections of a morphism presheaf

With the notation of `AlgebraicGeometry.Stack.GroupoidLift.stackGroupoid`, let `N = P ⊗[A'] P`
and let `x₀`, `x₁` be the objects `ξ v₀`, `ξ vₗ` of `𝒳` over `Spec N`, the images of the two
vertices `P → N`. An arrow of the groupoid of the chart over `C` with source `h ∘ v₀` and target
`h ∘ vₗ`, for `h : N → C`, is a morphism `ξ (h ∘ v₀) ⟶ ξ (h ∘ vₗ)` over `Spec C`; a section of
the presheaf `Mor(x₀, x₁)` on `𝒮/Spec N` over `Spec h` is a morphism between the chosen pullbacks
of `x₀` and `x₁` along `Spec h`. The two are identified by conjugation with the comparison
isomorphisms of the cartesian arrows `ξ (h ∘ vᵢ) ⟶ xᵢ` and the chosen pullbacks
(`AlgebraicGeometry.Stack.GroupoidLift.StackChart.morToArr`), naturally in `C`
(`AlgebraicGeometry.Stack.GroupoidLift.StackChart.map_morToArr`).

## Main definitions

* `AlgebraicGeometry.Stack.GroupoidLift.StackChart.pairAlg`: the algebra `P ⊗[A'] P`.
* `AlgebraicGeometry.Stack.GroupoidLift.StackChart.morToArr`: the identification.

## Main results

* `AlgebraicGeometry.Stack.GroupoidLift.StackChart.morToArr_injective`,
  `AlgebraicGeometry.Stack.GroupoidLift.StackChart.exists_morToArr_eq`: it is bijective.
* `AlgebraicGeometry.Stack.GroupoidLift.StackChart.map_morToArr`: it is natural, the restriction
  of sections being `CategoryTheory.Functor.morRestrict` along
  `AlgebraicGeometry.Stack.GroupoidLift.StackChart.pairOverMap`.
-/

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry.Space.ChartDescent

namespace AlgebraicGeometry.Stack.GroupoidLift

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T' : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
  {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  {U₀ : BigFppfOver B S hS} (a : schemeFibredCategory B S hS U₀ ⟶ 𝒳)
  {P : SmallAlg (ringOf B S hS T') B.cutoff} (ι : specOver P ⟶ U₀)

namespace StackChart

/-- The projection of the category fibred in groupoids `𝒳` is a fibred functor. -/
local instance : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered

variable (P) in
/-- The algebra `P ⊗[A'] P`, the first term of the Čech nerve of `P`. -/
noncomputable abbrev pairAlg : SmallAlg (ringOf B S hS T') B.cutoff :=
  nerve (A' := ringOf B S hS T') B.aleph0_lt_cutoff P.obj P.property 1

variable (P) in
/-- The vertex `0` of `P ⊗[A'] P`. -/
noncomputable abbrev vtx₀ : P.obj →ₐ[ringOf B S hS T'] (pairAlg P).obj := v₀ _ P.obj 1

variable (P) in
/-- The vertex `1` of `P ⊗[A'] P`. -/
noncomputable abbrev vtx₁ : P.obj →ₐ[ringOf B S hS T'] (pairAlg P).obj := vₗ _ P.obj 1

/-- The object `ξ u` as an object of the fibre over `Spec C`. -/
noncomputable abbrev ξF {C : SmallAlg (ringOf B S hS T') B.cutoff}
    (u : P.obj →ₐ[ringOf B S hS T'] C.obj) : 𝒳.val.p.Fiber (specOver C) :=
  ⟨ξ a ι u, ξ_obj a ι u⟩

/-- The object `ξ v₀` of the fibre over `Spec (P ⊗ P)`. -/
noncomputable abbrev pairObj₀ : 𝒳.val.p.Fiber (specOver (pairAlg P)) := ξF a ι (vtx₀ P)

/-- The object `ξ vₗ` of the fibre over `Spec (P ⊗ P)`. -/
noncomputable abbrev pairObj₁ : 𝒳.val.p.Fiber (specOver (pairAlg P)) := ξF a ι (vtx₁ P)

variable (P) in
/-- The point `Spec h` of `Spec (P ⊗ P)`, as an object of the slice. -/
noncomputable abbrev pairOver {C : SmallAlg (ringOf B S hS T') B.cutoff}
    (h : (pairAlg P).obj →ₐ[ringOf B S hS T'] C.obj) : Over (specOver (pairAlg P)) :=
  Over.mk (specOverMap (SmallAlg.homMk h))

/-- The comparison of `ξ (h ∘ u)` with the chosen pullback of `ξ u` along `Spec h`, for a point
`u` of `P` with values in `P ⊗ P`. -/
noncomputable def pairCmp {C : SmallAlg (ringOf B S hS T') B.cutoff}
    (h : (pairAlg P).obj →ₐ[ringOf B S hS T'] C.obj)
    (u : P.obj →ₐ[ringOf B S hS T'] (pairAlg P).obj) :
    ξF a ι (h.comp u) ≅ Functor.pullbackFiber 𝒳.val.p (ξF a ι u) (pairOver P h).hom :=
  Functor.fiberIsoOfCartesian (p := 𝒳.val.p) (z := ξF a ι (h.comp u))
    (z' := Functor.pullbackFiber 𝒳.val.p (ξF a ι u) (pairOver P h).hom)
    (specOverMap (SmallAlg.homMk h))
    (trans a ι (SmallAlg.homMk h) u)
    (Functor.IsPreFibered.pullbackMap (ξ_obj a ι u) (specOverMap (SmallAlg.homMk h)))
    inferInstance (Functor.IsPreFibered.pullbackMap.IsCartesian (ξ_obj a ι u) _)

/-- The comparison `pairCmp` followed by the chosen pullback arrow is the cartesian arrow
`ξ (h ∘ u) ⟶ ξ u`. -/
theorem pairCmp_hom_fac {C : SmallAlg (ringOf B S hS T') B.cutoff}
    (h : (pairAlg P).obj →ₐ[ringOf B S hS T'] C.obj)
    (u : P.obj →ₐ[ringOf B S hS T'] (pairAlg P).obj) :
    (pairCmp a ι h u).hom.1 ≫
      Functor.IsPreFibered.pullbackMap (ξ_obj a ι u) (specOverMap (SmallAlg.homMk h)) =
      trans a ι (SmallAlg.homMk h) u :=
  Functor.fiberIsoOfCartesian_hom_fac (p := 𝒳.val.p) (z := ξF a ι (h.comp u))
    (z' := Functor.pullbackFiber 𝒳.val.p (ξF a ι u) (pairOver P h).hom)
    (specOverMap (SmallAlg.homMk h)) _ _ inferInstance
    (Functor.IsPreFibered.pullbackMap.IsCartesian (ξ_obj a ι u) _)

/-- The inverse of the comparison `pairCmp` followed by the cartesian arrow `ξ (h ∘ u) ⟶ ξ u` is
the chosen pullback arrow. -/
theorem pairCmp_inv_fac {C : SmallAlg (ringOf B S hS T') B.cutoff}
    (h : (pairAlg P).obj →ₐ[ringOf B S hS T'] C.obj)
    (u : P.obj →ₐ[ringOf B S hS T'] (pairAlg P).obj) :
    (pairCmp a ι h u).inv.1 ≫ trans a ι (SmallAlg.homMk h) u =
      Functor.IsPreFibered.pullbackMap (ξ_obj a ι u) (specOverMap (SmallAlg.homMk h)) :=
  Functor.fiberIsoOfCartesian_inv_fac (p := 𝒳.val.p) (z := ξF a ι (h.comp u))
    (z' := Functor.pullbackFiber 𝒳.val.p (ξF a ι u) (pairOver P h).hom)
    (specOverMap (SmallAlg.homMk h)) _ _ inferInstance
    (Functor.IsPreFibered.pullbackMap.IsCartesian (ξ_obj a ι u) _)

/-- **A section of `Mor(x₀, x₁)` over `Spec h` as an arrow of the groupoid of the chart.** -/
noncomputable def morToArr {C : SmallAlg (ringOf B S hS T') B.cutoff}
    (h : (pairAlg P).obj →ₐ[ringOf B S hS T'] C.obj)
    (m : Functor.pullbackFiber 𝒳.val.p (pairObj₀ a ι) (pairOver P h).hom ⟶
        Functor.pullbackFiber 𝒳.val.p (pairObj₁ a ι) (pairOver P h).hom) : Arr a ι C where
  src := h.comp (vtx₀ P)
  tgt := h.comp (vtx₁ P)
  hom := ((pairCmp a ι h (vtx₀ P)).hom ≫ m ≫ (pairCmp a ι h (vtx₁ P)).inv).1
  lift := ((pairCmp a ι h (vtx₀ P)).hom ≫ m ≫ (pairCmp a ι h (vtx₁ P)).inv).2

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
variable (P) in
/-- A map out of `P ⊗ P` is determined by its two vertices. -/
theorem pair_ext {C : SmallAlg (ringOf B S hS T') B.cutoff}
    {h h' : (pairAlg P).obj →ₐ[ringOf B S hS T'] C.obj} (h₀ : h.comp (vtx₀ P) = h'.comp (vtx₀ P))
    (h₁ : h.comp (vtx₁ P) = h'.comp (vtx₁ P)) : h = h' :=
  Algebra.TensorProduct.ext h₁ h₀

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
variable (P) in
/-- Every pair of points of `P` is the pair of vertices of a map out of `P ⊗ P`. -/
theorem exists_pair {C : SmallAlg (ringOf B S hS T') B.cutoff}
    (s t : P.obj →ₐ[ringOf B S hS T'] C.obj) :
    ∃ h : (pairAlg P).obj →ₐ[ringOf B S hS T'] C.obj, h.comp (vtx₀ P) = s ∧ h.comp (vtx₁ P) = t :=
  ⟨Algebra.TensorProduct.productMap t s, Algebra.TensorProduct.productMap_right t s,
    Algebra.TensorProduct.productMap_left t s⟩

/-- The source of `morToArr h m` is the point `h ∘ v₀` of `P`. -/
theorem morToArr_src {C : SmallAlg (ringOf B S hS T') B.cutoff}
    (h : (pairAlg P).obj →ₐ[ringOf B S hS T'] C.obj)
    (m : Functor.pullbackFiber 𝒳.val.p (pairObj₀ a ι) (pairOver P h).hom ⟶
        Functor.pullbackFiber 𝒳.val.p (pairObj₁ a ι) (pairOver P h).hom) :
    (morToArr a ι h m).src = h.comp (vtx₀ P) := rfl

/-- The target of `morToArr h m` is the point `h ∘ vₗ` of `P`. -/
theorem morToArr_tgt {C : SmallAlg (ringOf B S hS T') B.cutoff}
    (h : (pairAlg P).obj →ₐ[ringOf B S hS T'] C.obj)
    (m : Functor.pullbackFiber 𝒳.val.p (pairObj₀ a ι) (pairOver P h).hom ⟶
        Functor.pullbackFiber 𝒳.val.p (pairObj₁ a ι) (pairOver P h).hom) :
    (morToArr a ι h m).tgt = h.comp (vtx₁ P) := rfl

/-- **The identification is injective** on the sections over a fixed point of `P ⊗ P`. -/
theorem morToArr_injective {C : SmallAlg (ringOf B S hS T') B.cutoff}
    (h : (pairAlg P).obj →ₐ[ringOf B S hS T'] C.obj)
    {m m' : Functor.pullbackFiber 𝒳.val.p (pairObj₀ a ι) (pairOver P h).hom ⟶
        Functor.pullbackFiber 𝒳.val.p (pairObj₁ a ι) (pairOver P h).hom}
    (e : morToArr a ι h m = morToArr a ι h m') : m = m' := by
  unfold morToArr at e
  obtain ⟨-, -, hhom⟩ := Arr.mk.inj e
  have e' : (pairCmp a ι h (vtx₀ P)).hom ≫ m ≫ (pairCmp a ι h (vtx₁ P)).inv =
      (pairCmp a ι h (vtx₀ P)).hom ≫ m' ≫ (pairCmp a ι h (vtx₁ P)).inv :=
    Functor.Fiber.hom_ext (eq_of_heq hhom)
  simpa using e'

/-- **The identification is surjective.** -/
theorem exists_morToArr_eq {C : SmallAlg (ringOf B S hS T') B.cutoff} (g : Arr a ι C) :
    ∃ (h : (pairAlg P).obj →ₐ[ringOf B S hS T'] C.obj)
      (m : Functor.pullbackFiber 𝒳.val.p (pairObj₀ a ι) (pairOver P h).hom ⟶
        Functor.pullbackFiber 𝒳.val.p (pairObj₁ a ι) (pairOver P h).hom),
      morToArr a ι h m = g := by
  obtain ⟨s, t, φ, hl⟩ := g
  obtain ⟨h, rfl, rfl⟩ := exists_pair P s t
  let F : ξF a ι (h.comp (vtx₀ P)) ⟶ ξF a ι (h.comp (vtx₁ P)) := ⟨φ, hl⟩
  refine ⟨h, (pairCmp a ι h (vtx₀ P)).inv ≫ F ≫ (pairCmp a ι h (vtx₁ P)).hom, ?_⟩
  refine Arr.ext_heq rfl rfl (heq_of_eq ?_)
  change ((pairCmp a ι h (vtx₀ P)).hom ≫ ((pairCmp a ι h (vtx₀ P)).inv ≫ F ≫
    (pairCmp a ι h (vtx₁ P)).hom) ≫ (pairCmp a ι h (vtx₁ P)).inv).1 = F.1
  simp only [Iso.hom_inv_id_assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The morphism of the slice over `Spec (P ⊗ P)` induced by `f : C ⟶ D`. -/
noncomputable def pairOverMap {C D : SmallAlg (ringOf B S hS T') B.cutoff} (f : C ⟶ D)
    (h : (pairAlg P).obj →ₐ[ringOf B S hS T'] C.obj) :
    pairOver P (f.hom.hom.comp h) ⟶ pairOver P h :=
  Over.homMk (specOverMap f) (specOverMap_comp (SmallAlg.homMk h) f).symm

/-- The comparison of the cartesian arrows of a point with the chosen pullbacks is natural. -/
theorem pairCmp_naturality {C D : SmallAlg (ringOf B S hS T') B.cutoff} (f : C ⟶ D)
    (h : (pairAlg P).obj →ₐ[ringOf B S hS T'] C.obj)
    (u : P.obj →ₐ[ringOf B S hS T'] (pairAlg P).obj) :
    (pairCmp a ι (f.hom.hom.comp h) u).hom.1 ≫
        Functor.pullbackFiberMap 𝒳.val.p (ξF a ι u) (pairOverMap f h) =
      trans a ι f (h.comp u) ≫ (pairCmp a ι h u).hom.1 := by
  have := 𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift (specOverMap (SmallAlg.homMk h))
    (Functor.IsPreFibered.pullbackMap (ξ_obj a ι u) (specOverMap (SmallAlg.homMk h)))
  have i₂ : 𝒳.val.p.IsHomLift (𝟙 (specOver D)) (pairCmp a ι (f.hom.hom.comp h) u).hom.1 :=
    (pairCmp a ι (f.hom.hom.comp h) u).hom.2
  have i₃ : 𝒳.val.p.IsHomLift (𝟙 (specOver C)) (pairCmp a ι h u).hom.1 :=
    (pairCmp a ι h u).hom.2
  have j₁ : 𝒳.val.p.IsHomLift (specOverMap f) ((pairCmp a ι (f.hom.hom.comp h) u).hom.1 ≫
      Functor.pullbackFiberMap 𝒳.val.p (ξF a ι u) (pairOverMap f h)) :=
    @IsHomLift.comp_lift_id_left _ _ _ _ 𝒳.val.p _ _ _ _ _ (specOverMap f) _
      (Functor.pullbackFiberMap_isHomLift 𝒳.val.p (ξF a ι u) (pairOverMap f h)) _ i₂
  have j₂ : 𝒳.val.p.IsHomLift (specOverMap f) (trans a ι f (h.comp u) ≫ (pairCmp a ι h u).hom.1) :=
    @IsHomLift.comp_lift_id_right _ _ _ _ 𝒳.val.p _ _ _ _ _ (specOverMap f) _ inferInstance _ i₃
  refine @Functor.IsStronglyCartesian.ext _ _ _ _ 𝒳.val.p _ _ _ _
    (specOverMap (SmallAlg.homMk h))
    (Functor.IsPreFibered.pullbackMap (ξ_obj a ι u) (specOverMap (SmallAlg.homMk h)))
    inferInstance _ _ (specOverMap f) _ _ j₁ j₂ ?_
  refine ((Category.assoc _ _ _).trans ((congrArg ((pairCmp a ι (f.hom.hom.comp h) u).hom.1 ≫ ·)
    (Functor.pullbackFiberMap_fac 𝒳.val.p (ξF a ι u) (pairOverMap f h))).trans
    (pairCmp_hom_fac a ι (f.hom.hom.comp h) u))).trans ?_
  refine Eq.trans ?_ ((Category.assoc _ _ _).trans
    (congrArg (trans a ι f (h.comp u) ≫ ·) (pairCmp_hom_fac a ι h u))).symm
  exact trans_comp a ι (SmallAlg.homMk h) f u

/-- **The identification is natural**: restricting the section along `Spec f` corresponds to
restricting the arrow along `f`. -/
theorem map_morToArr {C D : SmallAlg (ringOf B S hS T') B.cutoff} (f : C ⟶ D)
    (h : (pairAlg P).obj →ₐ[ringOf B S hS T'] C.obj)
    (m : Functor.pullbackFiber 𝒳.val.p (pairObj₀ a ι) (pairOver P h).hom ⟶
        Functor.pullbackFiber 𝒳.val.p (pairObj₁ a ι) (pairOver P h).hom) :
    Arr.map a ι f (morToArr a ι h m) = morToArr a ι (f.hom.hom.comp h)
      (Functor.morRestrict 𝒳.val.p (pairObj₀ a ι) (pairObj₁ a ι) (pairOverMap f h) m) := by
  refine Arr.map_eq_mk f (morToArr a ι h m) (morToArr a ι (f.hom.hom.comp h)
    (Functor.morRestrict 𝒳.val.p (pairObj₀ a ι) (pairObj₁ a ι) (pairOverMap f h) m)).hom
    (morToArr a ι (f.hom.hom.comp h) _).lift ?_
  have k₁ : 𝒳.val.p.IsHomLift (specOverMap f) ((morToArr a ι (f.hom.hom.comp h)
      (Functor.morRestrict 𝒳.val.p (pairObj₀ a ι) (pairObj₁ a ι) (pairOverMap f h) m)).hom ≫
      trans a ι f (h.comp (vtx₁ P))) :=
    @IsHomLift.comp_lift_id_left _ _ _ _ 𝒳.val.p _ _ _ _ _ (specOverMap f) _
      (trans_isHomLift a ι f (h.comp (vtx₁ P))) _ (morToArr a ι (f.hom.hom.comp h) _).lift
  have k₂ : 𝒳.val.p.IsHomLift (specOverMap f) (trans a ι f (h.comp (vtx₀ P)) ≫
      (morToArr a ι h m).hom) :=
    @IsHomLift.comp_lift_id_right _ _ _ _ 𝒳.val.p _ _ _ _ _ (specOverMap f) _
      (trans_isHomLift a ι f (h.comp (vtx₀ P))) _ (morToArr a ι h m).lift
  refine @Functor.IsStronglyCartesian.ext _ _ _ _ 𝒳.val.p _ _ _ _
    (specOverMap (SmallAlg.homMk h)) (trans a ι (SmallAlg.homMk h) (vtx₁ P))
    inferInstance _ _ (specOverMap f) _ _ k₁ k₂ ?_
  change (((pairCmp a ι (f.hom.hom.comp h) (vtx₀ P)).hom.1 ≫
      (Functor.morRestrict 𝒳.val.p (pairObj₀ a ι) (pairObj₁ a ι) (pairOverMap f h) m).1 ≫
      (pairCmp a ι (f.hom.hom.comp h) (vtx₁ P)).inv.1) ≫ trans a ι f (h.comp (vtx₁ P))) ≫
      trans a ι (SmallAlg.homMk h) (vtx₁ P) =
    (trans a ι f (h.comp (vtx₀ P)) ≫ (pairCmp a ι h (vtx₀ P)).hom.1 ≫ m.1 ≫
      (pairCmp a ι h (vtx₁ P)).inv.1) ≫ trans a ι (SmallAlg.homMk h) (vtx₁ P)
  simp only [Category.assoc]
  refine ((Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans
    (congrArg ((pairCmp a ι (f.hom.hom.comp h) (vtx₀ P)).hom.1 ≫ ·)
      (Category.assoc _ _ _)))).trans ?_
  refine (congrArg (fun t => (pairCmp a ι (f.hom.hom.comp h) (vtx₀ P)).hom.1 ≫
    (Functor.morRestrict 𝒳.val.p (pairObj₀ a ι) (pairObj₁ a ι) (pairOverMap f h) m).1 ≫
    (pairCmp a ι (f.hom.hom.comp h) (vtx₁ P)).inv.1 ≫ t)
    (trans_comp a ι (SmallAlg.homMk h) f (vtx₁ P)).symm).trans ?_
  refine (congrArg (fun t => (pairCmp a ι (f.hom.hom.comp h) (vtx₀ P)).hom.1 ≫
    (Functor.morRestrict 𝒳.val.p (pairObj₀ a ι) (pairObj₁ a ι) (pairOverMap f h) m).1 ≫ t)
    (pairCmp_inv_fac a ι (f.hom.hom.comp h) (vtx₁ P))).trans ?_
  refine (congrArg (fun t => (pairCmp a ι (f.hom.hom.comp h) (vtx₀ P)).hom.1 ≫ t)
    (Functor.morRestrict_fac 𝒳.val.p (pairObj₀ a ι) (pairObj₁ a ι) (pairOverMap f h) m)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ m.1 ≫ Functor.IsPreFibered.pullbackMap (pairObj₁ a ι).2
    (pairOver P h).hom) (pairCmp_naturality a ι f h (vtx₀ P))).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg (fun t => trans a ι f (h.comp (vtx₀ P)) ≫ (pairCmp a ι h (vtx₀ P)).hom.1 ≫
    m.1 ≫ t) (pairCmp_inv_fac a ι h (vtx₁ P)).symm

end StackChart

end AlgebraicGeometry.Stack.GroupoidLift

end
