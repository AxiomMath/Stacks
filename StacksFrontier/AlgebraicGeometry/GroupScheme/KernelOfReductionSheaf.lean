module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.CategoryTheory.Sites.OverPullbackPushforward
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianSchemeFirstCohomologyGenericPoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExamplesSheaves.AdditiveGroupSheafCohomology
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.AlgebraicGeometry.Thickenings.BaseChange
public import StacksFrontier.AlgebraicGeometry.Thickenings.KernelGlobalSections
public import StacksFrontier.AlgebraicGeometry.GroupScheme.KernelOfReduction
public import StacksFrontier.RingTheory.Kaehler.DerivationsAtSection
public import StacksFrontier.AlgebraicGeometry.GroupScheme.SmoothPointsSheafBaseChangeEpi

/-!
# The kernel of reduction of a smooth commutative group scheme is a vector group

Let `S` be an affine scheme with local ring of global functions, `G` a smooth commutative group
scheme over `S`, and `Z ⟶ S` a morphism such that, for an object `U` of the big fppf site of `S`,
the base change `U ×_S Z ⟶ U` is a first-order thickening. For every `T` over `U`, the points
`a : T ⟶ G` restricting to the unit on `T ×_S Z` form, under the group law of `G`, a group
isomorphic to `I_T ^ g`, where `I_T` is the kernel of `Γ(T, 𝒪_T) ⟶ Γ(T ×_S Z, 𝒪)` and `g` is the
rank of the cotangent space of `G` at the unit of the closed point, naturally in `T`.

## Main results

* `AlgebraicGeometry.exists_addEquiv_ker_toBaseChangePushforward_pointsSheaf`: the
  isomorphisms, in terms of the sheaf of points `AlgebraicGeometry.pointsSheaf` and of the
  additive group sheaf `AlgebraicGeometry.BigFppfOver.additiveGroupSheaf`.

## Implementation notes

The isomorphism sends a point `a` to the values at fixed elements `v₁, …, v_g` of the local ring
`𝒪_{G, e(s₀)}` of the difference `a^# - (e ∘ q)^#` of the maps on that local ring
(`AlgebraicGeometry.Scheme.Hom.stalkDiff`). The `vₖ` are chosen once, by
`KaehlerDifferential.exists_derivation_coordinates`, so the isomorphisms are natural in `T`
because the difference is (`AlgebraicGeometry.Scheme.Hom.stalkDiff_comp`). Additivity is
`AlgebraicGeometry.GrpObj.stalkDiff_mul`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite MonoidalCategory
  CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)
  {Z : Scheme.{u}} (hZ : B.Contains Z) (z : B.obj hZ ⟶ B.obj hS)

variable (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : B.Contains G.left)

/-- A section of the sheaf of points over `T` is a morphism `T ⟶ G` over `S`. -/
private abbrev pointsSheafHom {T : BigFppfOver B S hS}
    (a : (pointsSheaf B S hS G hG).obj.obj (op T)) : (Over.post B.inclusion).obj T ⟶ G :=
  show (Over.post B.inclusion).obj T ⟶ G from a

/-- A morphism `T ⟶ G` over `S` as a section of the sheaf of points over `T`. -/
private abbrev pointsSheafSection {T : BigFppfOver B S hS}
    (c : (Over.post B.inclusion).obj T ⟶ G) : (pointsSheaf B S hS G hG).obj.obj (op T) :=
  Additive.ofMul c

private theorem pointsSheafHom_pointsSheafSection {T : BigFppfOver B S hS}
    (c : (Over.post B.inclusion).obj T ⟶ G) :
    pointsSheafHom B hS G hG (pointsSheafSection B hS G hG c) = c :=
  rfl

private theorem pointsSheafHom_add {T : BigFppfOver B S hS}
    (a b : (pointsSheaf B S hS G hG).obj.obj (op T)) :
    pointsSheafHom B hS G hG (a + b) = pointsSheafHom B hS G hG a * pointsSheafHom B hS G hG b :=
  rfl

private theorem pointsSheafHom_map {T T' : BigFppfOver B S hS} (f : T' ⟶ T)
    (a : (pointsSheaf B S hS G hG).obj.obj (op T)) :
    pointsSheafHom B hS G hG (((pointsSheaf B S hS G hG).obj.map f.op).hom a) =
      (Over.post B.inclusion).map f ≫ pointsSheafHom B hS G hG a :=
  rfl

private theorem mem_ker_pointsSheaf_iff (T : BigFppfOver B S hS)
    (a : (pointsSheaf B S hS G hG).obj.obj (op T)) :
    a ∈ (((pointsSheaf B S hS G hG).toBaseChangePushforward z).hom.app (op T)).hom.ker ↔
      (Over.post B.inclusion).map (Sheaf.baseChangeFst z T) ≫ pointsSheafHom B hS G hG a = 1 := by
  have e : pointsSheafSection B hS G hG
      ((Over.post B.inclusion).map (Sheaf.baseChangeFst z T) ≫ pointsSheafHom B hS G hG a) =
      ((pointsSheaf B S hS G hG).obj.map (Sheaf.baseChangeFst z T).op).hom a := rfl
  rw [AddMonoidHom.mem_ker, Sheaf.toBaseChangePushforward_hom_app]
  exact (Eq.congr_left e).symm.trans (ofMul_eq_zero
    (A := (Over.post B.inclusion).obj ((Over.map z).obj ((Over.pullback z).obj T)) ⟶ G))

private theorem mem_ker_additiveGroupSheaf_iff (T : BigFppfOver B S hS)
    (x : (BigFppfOver.additiveGroupSheaf S B hS).obj.obj (op T)) :
    x ∈ (((BigFppfOver.additiveGroupSheaf S B hS).toBaseChangePushforward z).hom.app
        (op T)).hom.ker ↔
      (B.inclusion.map (Sheaf.baseChangeFst z T).left).appTop.hom x = 0 :=
  Iff.rfl

private theorem appTop_eq_additiveGroupSheaf_map {T T' : BigFppfOver B S hS} (f : T' ⟶ T)
    (x : (BigFppfOver.additiveGroupSheaf S B hS).obj.obj (op T)) :
    (B.inclusion.map f.left).appTop.hom x =
      ((BigFppfOver.additiveGroupSheaf S B hS).obj.map f.op).hom x :=
  rfl

/-- **The kernel of reduction of a smooth commutative group scheme is a vector group.** Let `S`
be an affine scheme whose ring of global functions is local, `G` a smooth commutative group
scheme over `S`, `z : Z ⟶ S` a morphism, and `U` an object of the big fppf site of `S` such that
`U ×_S Z ⟶ U` is a first-order thickening. There is `g` such that for every `T` over `U` the
group of points `T ⟶ G` restricting to the unit on `T ×_S Z` (the kernel of the map of the sheaf
of points to its base change along `z`) is isomorphic to `I_T ^ g`, where `I_T` is the kernel of
`Γ(T, 𝒪_T) ⟶ Γ(T ×_S Z, 𝒪)`, compatibly with restriction along every `T' ⟶ T`. -/
theorem exists_addEquiv_ker_toBaseChangePushforward_pointsSheaf [IsAffine S]
    [IsLocalRing Γ(S, ⊤)] [Smooth G.hom] (U : BigFppfOver B S hS)
    (hU : Stacks.Thickenings.IsFirstOrderThickening
      (B.inclusion.map (Sheaf.baseChangeFst z U).left)) :
    ∃ (g : ℕ) (θ : ∀ (T : BigFppfOver B S hS) (_ : T ⟶ U),
        (((pointsSheaf B S hS G hG).toBaseChangePushforward z).hom.app (op T)).hom.ker ≃+
        (Fin g → (((BigFppfOver.additiveGroupSheaf S B hS).toBaseChangePushforward z).hom.app
          (op T)).hom.ker)),
      ∀ (T T' : BigFppfOver B S hS) (t : T ⟶ U) (f : T' ⟶ T)
        (a : (pointsSheaf B S hS G hG).obj.obj (op T))
        (ha : a ∈ (((pointsSheaf B S hS G hG).toBaseChangePushforward z).hom.app (op T)).hom.ker)
        (ha' : ((pointsSheaf B S hS G hG).obj.map f.op).hom a ∈
          (((pointsSheaf B S hS G hG).toBaseChangePushforward z).hom.app (op T')).hom.ker)
        (k : Fin g),
        ((θ T' (f ≫ t) ⟨_, ha'⟩ k : _) : (BigFppfOver.additiveGroupSheaf S B hS).obj.obj (op T')) =
          ((BigFppfOver.additiveGroupSheaf S B hS).obj.map f.op).hom (θ T t ⟨a, ha⟩ k).1 := by
  obtain ⟨s₀, hs₀⟩ := Scheme.exists_forall_specializes_of_isLocalRing S
  have hy := GrpObj.specializes_unitSection G s₀ hs₀
  let : Algebra Γ(S, ⊤) (G.left.presheaf.stalk ((GrpObj.unitSection G).base s₀)) :=
    (G.hom.appTop ≫ G.left.presheaf.germ ⊤ _ trivial).hom.toAlgebra
  have halg : ∀ r, algebraMap Γ(S, ⊤) (G.left.presheaf.stalk ((GrpObj.unitSection G).base s₀)) r =
      (G.left.presheaf.germ ⊤ _ trivial).hom (G.hom.appTop.hom r) := fun _ ↦ rfl
  obtain ⟨hfs, hef⟩ :=
    Scheme.Hom.formallySmooth_essFiniteType_stalk G.hom ((GrpObj.unitSection G).base s₀)
  let ε : G.left.presheaf.stalk ((GrpObj.unitSection G).base s₀) →ₐ[Γ(S, ⊤)] Γ(S, ⊤) :=
    { ((GrpObj.unitSection G).stalkToΓOfSpecializes _ hy).hom with
      commutes' := fun r ↦ by
        change ((GrpObj.unitSection G).stalkToΓOfSpecializes _ hy).hom
          ((G.left.presheaf.germ ⊤ _ trivial).hom (G.hom.appTop.hom r)) = r
        rw [Scheme.Hom.stalkToΓOfSpecializes_germ_appTop (𝟙 S) _ _ hy
          (GrpObj.unitSection_comp_hom G)]
        rfl }
  have hε : ∀ f, ε f = ((GrpObj.unitSection G).stalkToΓOfSpecializes _ hy).hom f := fun _ ↦ rfl
  obtain ⟨g, v, hv⟩ := KaehlerDifferential.exists_derivation_coordinates.{u, u} ε
  -- the first-order thickenings `T ×_S Z ⟶ T`
  have hthick : ∀ (T : BigFppfOver B S hS) (_ : T ⟶ U),
      Function.Surjective ((Over.post B.inclusion).map (Sheaf.baseChangeFst z T)).left.base ∧
      ∀ c d : Γ(((Over.post B.inclusion).obj T).left, ⊤),
        ((Over.post B.inclusion).map (Sheaf.baseChangeFst z T)).left.appTop.hom c = 0 →
        ((Over.post B.inclusion).map (Sheaf.baseChangeFst z T)).left.appTop.hom d = 0 →
        c * d = 0 := by
    intro T t
    have hT := isFirstOrderThickening_baseChangeFst_of_hom B hS hZ z t hU
    have := hT.1
    have hsq := Scheme.ker_appTop_pow_eq_bot
      (B.inclusion.map (Sheaf.baseChangeFst z T).left) inferInstance hT.2
    refine ⟨hT.isThickening.2, fun c d hc hd ↦ ?_⟩
    have hm : c * d ∈
        RingHom.ker (B.inclusion.map (Sheaf.baseChangeFst z T).left).appTop.hom ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul hc hd
    rw [hsq] at hm
    exact hm
  -- the isomorphisms, one object at a time
  have key : ∀ (T : BigFppfOver B S hS) (t : T ⟶ U),
      ∃ e : (((pointsSheaf B S hS G hG).toBaseChangePushforward z).hom.app (op T)).hom.ker ≃+
        (Fin g → (((BigFppfOver.additiveGroupSheaf S B hS).toBaseChangePushforward z).hom.app
          (op T)).hom.ker),
      ∀ a k, (((e a k : (BigFppfOver.additiveGroupSheaf S B hS).obj.obj (op T)) :
          Γ(((Over.post B.inclusion).obj T).left, ⊤))) =
        Scheme.Hom.stalkDiff ((Over.post B.inclusion).obj T).hom (GrpObj.unitSection G) _ hy
          (pointsSheafHom B hS G hG a.1).left
          (GrpObj.specializes_of_comp_eq_one G s₀ hs₀ _ (hthick T t).1
            ((mem_ker_pointsSheaf_iff B hS hZ z G hG T a.1).1 a.2)) (v k) := by
    intro T t
    obtain ⟨hi, h2⟩ := hthick T t
    have hker : ∀ a : (((pointsSheaf B S hS G hG).toBaseChangePushforward z).hom.app
        (op T)).hom.ker, (Over.post B.inclusion).map (Sheaf.baseChangeFst z T) ≫
          pointsSheafHom B hS G hG a.1 = 1 :=
      fun a ↦ (mem_ker_pointsSheaf_iff B hS hZ z G hG T a.1).1 a.2
    let φ : (((pointsSheaf B S hS G hG).toBaseChangePushforward z).hom.app (op T)).hom.ker →+
        (Fin g → (((BigFppfOver.additiveGroupSheaf S B hS).toBaseChangePushforward z).hom.app
          (op T)).hom.ker) :=
      AddMonoidHom.mk' (fun a k ↦ ⟨(Scheme.Hom.stalkDiff ((Over.post B.inclusion).obj T).hom
            (GrpObj.unitSection G) _ hy (pointsSheafHom B hS G hG a.1).left
            (GrpObj.specializes_of_comp_eq_one G s₀ hs₀ _ hi (hker a)) (v k) :
              (BigFppfOver.additiveGroupSheaf S B hS).obj.obj (op T)),
          (mem_ker_additiveGroupSheaf_iff B hS hZ z T _).2
            (Scheme.Hom.appTop_stalkDiff _ _ _ hy _ _ _
              (GrpObj.left_comp_eq_of_comp_eq_one G _ (hker a)) _)⟩)
        (fun a b ↦ funext fun k ↦ Subtype.ext (by
          exact congrFun (GrpObj.stalkDiff_mul G s₀ hs₀ _ hi h2 (pointsSheafHom B hS G hG a.1)
            (pointsSheafHom B hS G hG b.1) (hker a) (hker b)) (v k)))
    have hinj : Function.Injective φ := fun a b hab ↦ by
      apply Subtype.ext
      exact GrpObj.eq_of_stalkDiff_coordinates_eq G s₀ hs₀ _ hi halg ε hε v h2
        (fun M _ _ ↦ (hv M).1) (pointsSheafHom B hS G hG a.1) (pointsSheafHom B hS G hG b.1)
        (hker a) (hker b) (fun k ↦ congrArg (fun m ↦ ((m k :
          (BigFppfOver.additiveGroupSheaf S B hS).obj.obj (op T)) :
            Γ(((Over.post B.inclusion).obj T).left, ⊤))) hab)
    have hsurj : Function.Surjective φ := fun m ↦ by
      obtain ⟨c, hc, hck⟩ := GrpObj.exists_stalkDiff_coordinates_eq G s₀ hs₀ _ hi halg ε hε v h2
        (fun M _ _ ↦ (hv M).2)
        (fun k ↦ ((m k : (BigFppfOver.additiveGroupSheaf S B hS).obj.obj (op T)) :
          Γ(((Over.post B.inclusion).obj T).left, ⊤)))
        (fun k ↦ (mem_ker_additiveGroupSheaf_iff B hS hZ z T _).1 (m k).2)
      refine ⟨⟨pointsSheafSection B hS G hG c, (mem_ker_pointsSheaf_iff B hS hZ z G hG T _).2 hc⟩,
        funext fun k ↦ Subtype.ext ?_⟩
      exact hck k
    exact ⟨AddEquiv.ofBijective φ ⟨hinj, hsurj⟩, fun a k ↦ rfl⟩
  choose θ hθ using key
  refine ⟨g, θ, fun T T' t f a ha ha' k ↦ ?_⟩
  have h₁ := hθ T' (f ≫ t) ⟨_, ha'⟩ k
  have h₂ := hθ T t ⟨a, ha⟩ k
  have hfa : (pointsSheafHom B hS G hG (((pointsSheaf B S hS G hG).obj.map f.op).hom a)).left =
      ((Over.post B.inclusion).map f).left ≫ (pointsSheafHom B hS G hG a).left := by
    rw [pointsSheafHom_map, Over.comp_left]
  have hsa : ∀ x, (pointsSheafHom B hS G hG a).left.base x ⤳ (GrpObj.unitSection G).base s₀ :=
    GrpObj.specializes_of_comp_eq_one G s₀ hs₀ _ (hthick T t).1
      ((mem_ker_pointsSheaf_iff B hS hZ z G hG T a).1 ha)
  have hsfa : ∀ x, (((Over.post B.inclusion).map f).left ≫
      (pointsSheafHom B hS G hG a).left).base x ⤳ (GrpObj.unitSection G).base s₀ := fun x ↦ by
    rw [Scheme.Hom.comp_apply]
    exact hsa _
  rw [← appTop_eq_additiveGroupSheaf_map, h₂, h₁,
    Scheme.Hom.stalkDiff_congr _ _ _ hy hfa _ hsfa,
    Scheme.Hom.stalkDiff_comp ((Over.post B.inclusion).obj T).hom (GrpObj.unitSection G) _ hy
      ((Over.post B.inclusion).map f).left (Over.w ((Over.post B.inclusion).map f)) _ hsa hsfa]
  rfl

end AlgebraicGeometry

end
