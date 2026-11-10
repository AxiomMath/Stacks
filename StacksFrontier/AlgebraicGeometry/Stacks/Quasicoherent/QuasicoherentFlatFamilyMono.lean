module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentFlatFamilyDetection
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentModulesAbelian

/-!
# Monomorphisms of quasi-coherent modules on a flat jointly surjective family (Stacks 0GQF)

The injectivity clause of **Stacks 0GQF**.  Let `𝒳` be an algebraic stack and `x_i : U_i → 𝒳`,
`i ∈ I`, flat objects with `∐ x_i : ∐ U_i → 𝒳` surjective, and let `φ : 𝓕 ⟶ 𝓖` be an arrow of
`QCoh(𝒪_𝒳)`.  Then `φ` is injective — a monomorphism of the abelian category `QCoh(𝒪_𝒳)` — if
and only if each restriction `φ_i = φ|_{(U_i)_{étale}}` is injective.

The "if" half is `AlgebraicGeometry.Stack.mono_of_restrictMapToSmallEtale`.  The "only if" half
is the source's "the structure of abelian category on `QCoh(𝒪_𝒳)` is such that `φ` is injective
if and only if `φ|_{U_étale}` is": the kernel of `φ` in `QCoh(𝒪_𝒳)` has, at every flat object,
the kernel of `φ` on sections as its sections
(`AlgebraicGeometry.Stack.AlgebraicStacks.injective_and_range_eq_ker_of_isLimit_kernelFork`),
and the objects of `(U_i)_{étale}` are flat objects of `𝒳`.

## Main results

* `AlgebraicGeometry.Stack.injective_app_flatObject_of_mono`: a monomorphism of `QCoh(𝒪_𝒳)` is
  injective on sections at every flat object.
* `AlgebraicGeometry.Stack.mono_iff_restrictMapToSmallEtale`: **Stacks 0GQF**, injectivity.

## References

* [Stacks Project, Tag 0GQF](https://stacks.math.columbia.edu/tag/0GQF)
* [Stacks Project, Tag 06WV](https://stacks.math.columbia.edu/tag/06WV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : AlgebraicStacks.{u, w} B S hS}
  {F G : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids} (φ : F ⟶ G)

/-- **A monomorphism of `QCoh(𝒪_𝒳)` is injective on sections at every flat object.**  Its
kernel in the abelian category `QCoh(𝒪_𝒳)` vanishes, and at a flat object the sections of that
kernel are the kernel of `φ` on sections. -/
theorem injective_app_flatObject_of_mono [Mono φ] {w : 𝒳.val.val.obj}
    (hw : flatObject B S hS 𝒳.val w) : Function.Injective (φ.hom.val.app (op w)) := by
  have hk := AlgebraicStacks.injective_and_range_eq_ker_of_isLimit_kernelFork B S hS 𝒳 φ
    (kernelIsKernel φ) w hw
  have h0 : kernel.ι φ = 0 := (cancel_mono φ).1 (by simp)
  have hker : LinearMap.ker (φ.hom.val.app (op w)).hom = ⊥ := by
    rw [← hk.2]
    change LinearMap.range ((kernel.ι φ).hom.val.app (op w)).hom = ⊥
    rw [h0]
    exact LinearMap.range_eq_bot.2 rfl
  exact LinearMap.ker_eq_bot.1 hker

variable (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  {I : Type*} (x : I → 𝒳.val.val.obj) (hflat : ∀ i, flatObject B S hS 𝒳.val (x i))
  (hsurj : ∀ q : AlgebraicStacks.points B S hS 𝒳, ∃ i, q ∈ Set.range
    (AlgebraicStacks.pointsMap B S hS
      (fibreObjectStackMap B S hS 𝒳 (𝒳.val.val.p.obj (x i)) (Functor.Fiber.mk rfl))))

include hflat hsurj in
/-- **Stacks 0GQF, injectivity.**  Let `𝒳` be an algebraic stack and `x_i : U_i → 𝒳`, `i ∈ I`,
flat objects with `∐ x_i : ∐ U_i → 𝒳` surjective.  An arrow `φ` of `QCoh(𝒪_𝒳)` is injective (a
monomorphism of the abelian category `QCoh(𝒪_𝒳)`) if and only if each restriction
`φ_i = φ|_{(U_i)_{étale}}` is injective on all sections. -/
@[stacks 0GQF "injectivity"]
theorem mono_iff_restrictMapToSmallEtale :
    Mono φ ↔ ∀ i V, Function.Injective ((restrictMapToSmallEtale B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (x i) ((PresheafOfModules.toPresheaf _).map φ.hom.val)).app V) :=
  ⟨fun _ i V => injective_app_flatObject_of_mono φ
      (flatObject_smallEtaleToStack_obj B E h S hS (x i) (hflat i) V.unop),
    mono_of_restrictMapToSmallEtale E h φ x hflat hsurj⟩

end AlgebraicGeometry.Stack

end
