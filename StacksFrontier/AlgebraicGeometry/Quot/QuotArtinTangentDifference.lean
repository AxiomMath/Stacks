module

public import StacksFrontier.Deformation.ModuleDeformation.CopowerExtension

/-!
# The difference of two deformations of a quotient over a copower extension

Let `𝒜` be an abelian `k`-linear category, `q₀ : F₀ ⟶ Q₀` an epimorphism with kernel
`ι₀ : 𝒦₀ ⟶ F₀`, and `V` a finite-dimensional `k`-vector space. Let `0 ⟶ F₀ ⊗ V ⟶ P ⟶ F₀ ⟶ 0`
be an extension by a copower (`Deformation.ModuleDeformation.CopowerExtension`). A lift of `q₀`
over `P` (`Deformation.ModuleDeformation.CopowerQuotientLift`) is an extension
`0 ⟶ Q₀ ⊗ V ⟶ E ⟶ Q₀ ⟶ 0` together with a map `g : P ⟶ E` compatible with both extensions.

For two such lifts `t` and `x` the *difference* `𝒦₀ ⟶ Q₀ ⊗ V` is defined: a section of `𝒦₀`
lifts to a section of the kernel of `g_t`, whose image under `g_x` lies in `Q₀ ⊗ V` and is
independent of the choice of the lift. With a fixed base lift `t`, the difference has the
following two properties:

* it separates lifts: if two lifts `x`, `y` have the same difference with `t`, every morphism
  killed by `g_x` is killed by `g_y`;
* it is natural in `V`, for maps of the data over a linear map `f : V ⟶ W`.

## Main definitions

* `Deformation.ModuleDeformation.CopowerQuotientLift`: a lift of `q₀` over a copower extension.
* `Deformation.ModuleDeformation.CopowerQuotientLift.difference`: the difference `𝒦₀ ⟶ Q₀ ⊗ V`.

## Main results

* `Deformation.ModuleDeformation.CopowerQuotientLift.epi_kernelToBase`: a section of `𝒦₀` lifts
  to the kernel of `g`.
* `Deformation.ModuleDeformation.CopowerQuotientLift.comp_g_eq_zero_of_difference_eq`: the
  difference separates lifts.
* `Deformation.ModuleDeformation.CopowerQuotientLift.difference_naturality`: the difference is
  natural in `V`.
-/

@[expose] public noncomputable section

namespace Deformation.ModuleDeformation

open CategoryTheory CategoryTheory.Limits

attribute [local instance] Abelian.hasFiniteBiproducts

universe v w u₁ v₁

variable {k : Type w} [Field k] {𝒜 : Type u₁} [Category.{v₁} 𝒜] [Abelian 𝒜] [Linear k 𝒜]

/-- The map `F₀ ⊗ V ⟶ Q₀ ⊗ V` of copowers induced by `q₀ : F₀ ⟶ Q₀`. -/
abbrev copowerMapLeft {F₀ Q₀ : 𝒜} (q₀ : F₀ ⟶ Q₀) (V : FGModuleCat.{v} k) :
    copowerObj F₀ V ⟶ copowerObj Q₀ V :=
  biproduct.map fun _ => q₀

/-- If `μ v ≫ g = q₀ ≫ μ' v` for every `v`, then the induced maps out of the copowers satisfy
`copowerDesc F₀ μ ≫ g = copowerMapLeft q₀ V ≫ copowerDesc Q₀ μ'`. -/
theorem copowerDesc_comp_of_comp {F₀ Q₀ E E' : 𝒜} (q₀ : F₀ ⟶ Q₀) {V : FGModuleCat.{v} k}
    (μ : ↥V →ₗ[k] (F₀ ⟶ E)) (μ' : ↥V →ₗ[k] (Q₀ ⟶ E')) (g : E ⟶ E')
    (h : ∀ v, μ v ≫ g = q₀ ≫ μ' v) :
    copowerDesc F₀ μ ≫ g = copowerMapLeft q₀ V ≫ copowerDesc Q₀ μ' := by
  ext i
  rw [ι_copowerDesc_assoc, h, biproduct.ι_map_assoc, ι_copowerDesc]

/-- A lift of the quotient `q₀ : F₀ ⟶ Q₀` over a copower extension `P` of `F₀`: a copower
extension of `Q₀` and a map `g` from `P` to its middle term compatible with the projections and
with the families of multiplications. -/
structure CopowerQuotientLift {F₀ Q₀ : 𝒜} (q₀ : F₀ ⟶ Q₀) {V : FGModuleCat.{v} k}
    (A : CopowerExtension (k := k) F₀ V) where
  /-- The extension of `Q₀`. -/
  ext : CopowerExtension (k := k) Q₀ V
  /-- The map of middle terms. -/
  g : A.E ⟶ ext.E
  /-- `g` is compatible with the projections to `F₀` and `Q₀`. -/
  g_p : g ≫ ext.p = A.p ≫ q₀
  /-- `g` is compatible with the multiplications. -/
  μ_g : ∀ v, A.μ v ≫ g = q₀ ≫ ext.μ v

namespace CopowerQuotientLift

/-- Projecting `φ ≫ g` to `Q₀` is the same as projecting `φ` to `F₀` and applying `q₀`. -/
private theorem comp_g_comp_p {F₀ Q₀ : 𝒜} {q₀ : F₀ ⟶ Q₀} {V : FGModuleCat.{v} k}
    {A : CopowerExtension (k := k) F₀ V} (x : CopowerQuotientLift q₀ A) {W : 𝒜} (φ : W ⟶ A.E) :
    (φ ≫ x.g) ≫ x.ext.p = (φ ≫ A.p) ≫ q₀ := by
  rw [Category.assoc, x.g_p, Category.assoc]

variable {F₀ Q₀ K : 𝒜} {q₀ : F₀ ⟶ Q₀} {ι₀ : K ⟶ F₀} (w₀ : ι₀ ≫ q₀ = 0)
  (hK : (ShortComplex.mk ι₀ q₀ w₀).Exact) [Mono ι₀] [Epi q₀]
  {V : FGModuleCat.{v} k} {A : CopowerExtension (k := k) F₀ V}

/-- The inclusion `Q₀ ⊗ V ⟶ E` of a lift. -/
abbrev μ' (x : CopowerQuotientLift q₀ A) : copowerObj Q₀ V ⟶ x.ext.E :=
  copowerDesc Q₀ x.ext.μ

/-- The inclusion `Q₀ ⊗ V ⟶ E` of a lift is a monomorphism. -/
instance mono_μ' (x : CopowerQuotientLift q₀ A) : Mono x.μ' :=
  x.ext.shortExact.mono_f

omit [Epi q₀] in
/-- The extension `Q₀ ⊗ V ⟶ E ⟶ Q₀` of a lift is exact. -/
theorem exact_ext (x : CopowerQuotientLift q₀ A) :
    (ShortComplex.mk x.μ' x.ext.p (by
      ext i; rw [ι_copowerDesc_assoc, x.ext.μ_p, comp_zero])).Exact :=
  x.ext.shortExact.exact

omit [Epi q₀] in
/-- `g` restricted to `F₀ ⊗ V` is `q₀ ⊗ V` followed by the inclusion of `Q₀ ⊗ V`. -/
theorem copowerDesc_comp_g (x : CopowerQuotientLift q₀ A) :
    copowerDesc F₀ A.μ ≫ x.g = copowerMapLeft q₀ V ≫ x.μ' :=
  copowerDesc_comp_of_comp q₀ A.μ x.ext.μ x.g x.μ_g

omit [Epi q₀] in
/-- The kernel of `g`, projected to `F₀`, is killed by `q₀`. -/
theorem kernel_ι_g_p_q (x : CopowerQuotientLift q₀ A) :
    (kernel.ι x.g ≫ A.p) ≫ q₀ = 0 := by
  rw [← comp_g_comp_p, kernel.condition, zero_comp]

/-- The map from the kernel of `g` to `𝒦₀`: the projection to `F₀`, which lands in `𝒦₀`. -/
def kernelToBase (x : CopowerQuotientLift q₀ A) : kernel x.g ⟶ K :=
  hK.lift (kernel.ι x.g ≫ A.p) (kernel_ι_g_p_q x)

omit [Epi q₀] in
/-- `kernelToBase` followed by `𝒦₀ ⟶ F₀` is the projection of the kernel of `g` to `F₀`. -/
@[reassoc]
theorem kernelToBase_ι (x : CopowerQuotientLift q₀ A) :
    kernelToBase w₀ hK x ≫ ι₀ = kernel.ι x.g ≫ A.p :=
  hK.lift_f _ _

/-- The copower extension `F₀ ⊗ V ⟶ P ⟶ F₀` is exact. -/
theorem exact_A : (ShortComplex.mk (copowerDesc F₀ A.μ) A.p (by
      ext i; rw [ι_copowerDesc_assoc, A.μ_p, comp_zero])).Exact :=
  A.shortExact.exact

/-- The projection `P ⟶ F₀` is an epimorphism. -/
instance : Epi A.p := A.shortExact.epi_g

omit [Epi q₀] in
/-- The composite `F₀ ⊗ V ⟶ P ⟶ F₀` is zero. -/
@[reassoc]
theorem copowerDesc_p : copowerDesc F₀ A.μ ≫ A.p = 0 := by
  ext i; rw [ι_copowerDesc_assoc, A.μ_p, comp_zero]

/-- The inclusion `F₀ ⊗ V ⟶ P` is a monomorphism. -/
instance : Mono (copowerDesc F₀ A.μ) := A.shortExact.mono_f

include hK in
/-- Every section of `𝒦₀` lifts to the kernel of `g`: `kernelToBase` is an epimorphism. -/
theorem epi_kernelToBase (x : CopowerQuotientLift q₀ A) : Epi (kernelToBase w₀ hK x) := by
  let P₁ := pullback A.p ι₀
  let a₁ : P₁ ⟶ A.E := pullback.fst A.p ι₀
  let b₁ : P₁ ⟶ K := pullback.snd A.p ι₀
  have hab : a₁ ≫ A.p = b₁ ≫ ι₀ := pullback.condition
  have hc : (a₁ ≫ x.g) ≫ x.ext.p = 0 := by
    rw [comp_g_comp_p, hab, Category.assoc, w₀, comp_zero]
  let c : P₁ ⟶ copowerObj Q₀ V := (exact_ext x).lift (a₁ ≫ x.g) hc
  have hcμ : c ≫ x.μ' = a₁ ≫ x.g := (exact_ext x).lift_f _ _
  let P₂ := pullback c (copowerMapLeft q₀ V)
  let e₁ : P₂ ⟶ P₁ := pullback.fst c (copowerMapLeft q₀ V)
  let e₂ : P₂ ⟶ copowerObj F₀ V := pullback.snd c (copowerMapLeft q₀ V)
  have he : e₁ ≫ c = e₂ ≫ copowerMapLeft q₀ V := pullback.condition
  let m : P₂ ⟶ A.E := e₁ ≫ a₁ - e₂ ≫ copowerDesc F₀ A.μ
  have hm : m ≫ x.g = 0 := by
    simp only [m, Preadditive.sub_comp, Category.assoc, copowerDesc_comp_g]
    rw [← hcμ, ← Category.assoc e₁, he, Category.assoc, sub_self]
  let m' : P₂ ⟶ kernel x.g := kernel.lift x.g m hm
  have hfac : m' ≫ kernelToBase w₀ hK x = e₁ ≫ b₁ := by
    rw [← cancel_mono ι₀, Category.assoc, kernelToBase_ι, kernel.lift_ι_assoc]
    simp only [m, Preadditive.sub_comp, Category.assoc, copowerDesc_p, comp_zero, sub_zero]
    rw [hab]
  have : Epi b₁ := Abelian.epi_pullback_of_epi_f A.p ι₀
  have : Epi e₁ := Abelian.epi_pullback_of_epi_g c (copowerMapLeft q₀ V)
  have : Epi (m' ≫ kernelToBase w₀ hK x) := by rw [hfac]; infer_instance
  exact epi_of_epi m' (kernelToBase w₀ hK x)

/-- The image under `g_x` of the kernel of `g_t`, as a map to `Q₀ ⊗ V`. -/
def kernelDifference (t x : CopowerQuotientLift q₀ A) : kernel t.g ⟶ copowerObj Q₀ V :=
  (exact_ext x).lift (kernel.ι t.g ≫ x.g) (by
    rw [Category.assoc, x.g_p, ← Category.assoc, ← kernelToBase_ι w₀ hK t, Category.assoc, w₀,
      comp_zero])

omit [Epi q₀] in
/-- `kernelDifference t x` followed by the inclusion of `Q₀ ⊗ V` is `g_x` on the kernel of
`g_t`. -/
@[reassoc]
theorem kernelDifference_μ' (t x : CopowerQuotientLift q₀ A) :
    kernelDifference w₀ hK t x ≫ x.μ' = kernel.ι t.g ≫ x.g :=
  (exact_ext x).lift_f _ _

omit [Epi q₀] in
/-- `kernelDifference t x` vanishes on the kernel of `kernelToBase`. -/
theorem kernel_ι_kernelDifference (t x : CopowerQuotientLift q₀ A) :
    kernel.ι (kernelToBase w₀ hK t) ≫ kernelDifference w₀ hK t x = 0 := by
  let z := kernel.ι (kernelToBase w₀ hK t) ≫ kernel.ι t.g
  have hz : z ≫ A.p = 0 := by
    simp only [z, Category.assoc, ← kernelToBase_ι w₀ hK t, kernel.condition_assoc, zero_comp]
  let b := (exact_A (A := A)).lift z hz
  have hb : b ≫ copowerDesc F₀ A.μ = z := (exact_A (A := A)).lift_f _ _
  have hbt : b ≫ copowerMapLeft q₀ V = 0 := by
    rw [← cancel_mono t.μ', zero_comp, Category.assoc, ← copowerDesc_comp_g, ← Category.assoc,
      hb]
    simp [z]
  rw [← cancel_mono x.μ', zero_comp, Category.assoc, kernelDifference_μ', ← Category.assoc]
  show z ≫ x.g = 0
  rw [← hb, Category.assoc, copowerDesc_comp_g, ← Category.assoc, hbt, zero_comp]

/-- The difference `𝒦₀ ⟶ Q₀ ⊗ V` of the lift `x` with the lift `t`. -/
def difference (t x : CopowerQuotientLift q₀ A) : K ⟶ copowerObj Q₀ V :=
  haveI := epi_kernelToBase w₀ hK t
  Abelian.epiDesc (kernelToBase w₀ hK t) (kernelDifference w₀ hK t x)
    (kernel_ι_kernelDifference w₀ hK t x)

/-- `kernelToBase` followed by the difference is `kernelDifference`. -/
@[reassoc]
theorem kernelToBase_difference (t x : CopowerQuotientLift q₀ A) :
    kernelToBase w₀ hK t ≫ difference w₀ hK t x = kernelDifference w₀ hK t x := by
  have := epi_kernelToBase w₀ hK t
  exact Abelian.comp_epiDesc _ _ _

/-- The defining property of the difference. -/
theorem kernelToBase_difference_μ' (t x : CopowerQuotientLift q₀ A) :
    kernelToBase w₀ hK t ≫ difference w₀ hK t x ≫ x.μ' = kernel.ι t.g ≫ x.g := by
  rw [kernelToBase_difference_assoc, kernelDifference_μ']

/-- The difference with a fixed lift separates lifts: if `x` and `y` have the same
difference with `t`, every morphism into `P` killed by `g_x` is killed by `g_y`. -/
theorem comp_g_eq_zero_of_difference_eq (t x y : CopowerQuotientLift q₀ A)
    (h : difference w₀ hK t x = difference w₀ hK t y) {W : 𝒜} (φ : W ⟶ A.E)
    (hφ : φ ≫ x.g = 0) : φ ≫ y.g = 0 := by
  have hφq : (φ ≫ A.p) ≫ q₀ = 0 := by
    rw [← comp_g_comp_p, hφ, zero_comp]
  let a : W ⟶ K := hK.lift (φ ≫ A.p) hφq
  have ha : a ≫ ι₀ = φ ≫ A.p := hK.lift_f _ _
  have := epi_kernelToBase w₀ hK t
  let W' := pullback a (kernelToBase w₀ hK t)
  let e : W' ⟶ W := pullback.fst a (kernelToBase w₀ hK t)
  let a' : W' ⟶ kernel t.g := pullback.snd a (kernelToBase w₀ hK t)
  have hea : e ≫ a = a' ≫ kernelToBase w₀ hK t := pullback.condition
  have : Epi e := Abelian.epi_pullback_of_epi_g a (kernelToBase w₀ hK t)
  let δ : W' ⟶ A.E := e ≫ φ - a' ≫ kernel.ι t.g
  have hδ : δ ≫ A.p = 0 := by
    simp only [δ, Preadditive.sub_comp, Category.assoc, ← ha, ← kernelToBase_ι w₀ hK t]
    rw [← Category.assoc e, hea, Category.assoc, sub_self]
  let b := (exact_A (A := A)).lift δ hδ
  have hb : b ≫ copowerDesc F₀ A.μ = δ := (exact_A (A := A)).lift_f _ _
  have hφ' : e ≫ φ = a' ≫ kernel.ι t.g + b ≫ copowerDesc F₀ A.μ := by
    rw [hb]; simp [δ]
  have key : ∀ z : CopowerQuotientLift q₀ A, e ≫ φ ≫ z.g =
      (a' ≫ kernelToBase w₀ hK t ≫ difference w₀ hK t z + b ≫ copowerMapLeft q₀ V) ≫ z.μ' := by
    intro z
    rw [← Category.assoc, hφ', Preadditive.add_comp, Preadditive.add_comp, Category.assoc,
      Category.assoc, Category.assoc, Category.assoc, kernelToBase_difference_μ',
      copowerDesc_comp_g, Category.assoc]
  have hx := key x
  rw [hφ, comp_zero] at hx
  have hx' := (cancel_mono x.μ').1 (hx.symm.trans zero_comp.symm)
  have hy := key y
  rw [← h, hx', zero_comp] at hy
  rw [← cancel_epi e, comp_zero]
  exact hy

/-! ### Naturality in the coefficient space -/

variable {W : FGModuleCat.{v} k} {B : CopowerExtension (k := k) F₀ W}

/-- Naturality of the difference: let `f : V ⟶ W` be a linear map, `Φ : P_V ⟶ P_W` a map of
the copower extensions of `F₀` compatible with the projections, and `t, x` over `V`, `t', x'`
over `W` lifts with maps `Φ_t`, `Φ_x` of their middle terms intertwining the `g`, with `Φ_x`
carrying each `μ v` to `μ (f v)`; then the difference of `x'` with `t'` is the difference of `x`
with `t` followed by `Q₀ ⊗ f`. -/
theorem difference_naturality (f : V ⟶ W) (Φ : A.E ⟶ B.E) (hΦ : Φ ≫ B.p = A.p)
    (t x : CopowerQuotientLift q₀ A) (t' x' : CopowerQuotientLift q₀ B)
    (Φt : t.ext.E ⟶ t'.ext.E) (hΦt : t.g ≫ Φt = Φ ≫ t'.g)
    (Φx : x.ext.E ⟶ x'.ext.E) (hΦx : x.g ≫ Φx = Φ ≫ x'.g)
    (hμ : ∀ v, x.ext.μ v ≫ Φx = x'.ext.μ (f.hom.hom v)) :
    difference w₀ hK t' x' = difference w₀ hK t x ≫ copowerMap Q₀ f := by
  have hκ : (kernel.ι t.g ≫ Φ) ≫ t'.g = 0 := by
    rw [Category.assoc, ← hΦt, ← Category.assoc, kernel.condition, zero_comp]
  let κ : kernel t.g ⟶ kernel t'.g := kernel.lift t'.g (kernel.ι t.g ≫ Φ) hκ
  have hκu : κ ≫ kernelToBase w₀ hK t' = kernelToBase w₀ hK t := by
    rw [← cancel_mono ι₀, Category.assoc, kernelToBase_ι, kernel.lift_ι_assoc, Category.assoc,
      hΦ, kernelToBase_ι]
  have hμx : x.μ' ≫ Φx = copowerMap Q₀ f ≫ x'.μ' :=
    copowerDesc_comp Q₀ x.ext.μ x'.ext.μ f Φx hμ
  have := epi_kernelToBase w₀ hK t
  refine (cancel_epi (kernelToBase w₀ hK t)).1 ((cancel_mono x'.μ').1 ?_)
  calc (kernelToBase w₀ hK t ≫ difference w₀ hK t' x') ≫ x'.μ'
      = κ ≫ kernelToBase w₀ hK t' ≫ difference w₀ hK t' x' ≫ x'.μ' := by
        rw [← hκu]; simp only [Category.assoc]
    _ = κ ≫ kernel.ι t'.g ≫ x'.g := by rw [kernelToBase_difference_μ']
    _ = kernel.ι t.g ≫ Φ ≫ x'.g := by rw [kernel.lift_ι_assoc, Category.assoc]
    _ = kernel.ι t.g ≫ x.g ≫ Φx := by rw [hΦx]
    _ = kernelToBase w₀ hK t ≫ difference w₀ hK t x ≫ x.μ' ≫ Φx := by
        rw [← Category.assoc (kernel.ι t.g), ← kernelToBase_difference_μ' w₀ hK t x]
        simp only [Category.assoc]
    _ = _ := by rw [hμx]; simp only [Category.assoc]

end CopowerQuotientLift

end Deformation.ModuleDeformation

end
