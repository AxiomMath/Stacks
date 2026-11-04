module

public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.SectionModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.LeftGradedPullback
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.GradedCommutative

/-!
# The pullback of a relative `Proj` situation along a morphism of base schemes

Let `s` be a relative `Proj` situation over `S` — a quasi-coherent, commutative, nonnegatively
graded `𝒪_S`-algebra `𝒜` — and let `g : S' ⟶ S` be a morphism of schemes. Then `𝒜' = g^*𝒜` is
again such an algebra on `S'`, and this file packages it as the situation `s.pullback g`. For a
graded `𝒜`-module `ℳ`, `ℳ' = g^*ℳ` is a graded `𝒜'`-module by
`Stacks.Conormal.leftGradedPullback`.

The base-change constructions for relative `Proj` and for the sheaf attached to a graded module
are stated for a situation `s'` over `S'` with an identification `Φ` of its algebra with `g^*𝒜`
and a degreewise identification `Ψ` of a graded module with `g^*ℳ`, compatible with the actions.
For `s' = s.pullback g` and `ℳ' = g^*ℳ` both identifications are the identity, and this file
supplies them together with the compatibility.

## Main definitions

* `Stacks.RelativeProj.Situation.pullback`: **the pullback situation** `g^*𝒜` over `S'`.
* `Stacks.RelativeProj.Situation.pullbackUnitalHom`: the identification of the algebra of
  `s.pullback g` with `g^*𝒜`, the identity.
* `Stacks.RelativeProj.Situation.pullbackModuleIdHom`: the identification of the pieces of
  `g^*ℳ` with the pullbacks of the pieces of `ℳ`, the identity.

## Main results

* `Stacks.RelativeProj.Situation.isIso_pullbackUnitalHom_app`: the identification of the
  algebras is an isomorphism in every degree.
* `Stacks.RelativeProj.Situation.pullbackSection_leftGradedPullback_smul`: pulling a product of a
  homogeneous section of `𝒜` and one of `ℳ` back to an open `W' ≤ g⁻¹W` is the product of the
  pullbacks.
* `Stacks.RelativeProj.Situation.pullbackModuleIdHom_compat`: the identity identifications are
  compatible with the actions.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.RelativeProj.Situation

/-- **The pullback of a relative `Proj` situation along a morphism of base schemes**: the graded
algebra `g^*𝒜` over `S'`. Its pieces are quasi-coherent, it vanishes in negative degrees and its
multiplication is commutative because those of `𝒜` are. -/
public abbrev pullback (s : Situation.{u}) {S' : Scheme.{u}} (g : S' ⟶ s.base) : Situation.{u} where
  base := S'
  algebra := Stacks.Conormal.gradedPullback g s.algebra
  mul_comm := Stacks.Conormal.gradedPullback_mul_comm g s.algebra s.mul_comm
  negative_isZero := Stacks.Conormal.gradedPullback_negative_isZero g s.algebra s.negative_isZero
  isQuasicoherent := Stacks.Conormal.gradedPullback_isQuasicoherent g s.algebra s.isQuasicoherent

variable (s : Situation.{u}) {S' : Scheme.{u}} (g : S' ⟶ s.base)

/-- The base of `s.pullback g` is `S'`. -/
@[simp] public theorem pullback_base : (s.pullback g).base = S' := rfl

/-- The algebra of `s.pullback g` is the pullback `g^*𝒜` of the algebra of `s`. -/
@[simp] public theorem pullback_algebra :
    (s.pullback g).algebra = Stacks.Conormal.gradedPullback g s.algebra := rfl

/-- The identification of the algebra of `s.pullback g` with the pullback of the algebra of `s`:
the identity. -/
public def pullbackUnitalHom :
    SheafOfModules.GradedAlgebra.UnitalHom (Stacks.Conormal.gradedPullback g s.algebra)
      (s.pullback g).algebra :=
  SheafOfModules.GradedAlgebra.UnitalHom.id (Stacks.Conormal.gradedPullback g s.algebra)

/-- Every degree component of `pullbackUnitalHom s g` is the identity. -/
@[simp] public theorem pullbackUnitalHom_app (n : ℤ) :
    (pullbackUnitalHom s g).app n = 𝟙 _ := rfl

/-- The identification of the algebras is an isomorphism in every degree. -/
public theorem isIso_pullbackUnitalHom_app (m : ℕ) : IsIso ((pullbackUnitalHom s g).app (m : ℤ)) :=
  inferInstanceAs (IsIso (𝟙 _))

variable {s} (ℳ : SheafOfModules.LeftGradedModule.{u, u, u} s.algebra)

/-- The pieces of `g^*ℳ`, as a graded module over the algebra of `s.pullback g`, are
quasi-coherent as soon as those of `ℳ` are. -/
public instance isQuasicoherent_leftGradedPullback_piece [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent]
    (n : ℤ) :
    ((Stacks.Conormal.leftGradedPullback g ℳ : SheafOfModules.LeftGradedModule.{u, u, u}
      (s.pullback g).algebra).piece n).IsQuasicoherent :=
  Stacks.Conormal.leftGradedPullback_isQuasicoherent g ℳ n

/-- The identification of the pieces of `g^*ℳ` with the pullbacks of the pieces of `ℳ`: the
identity. -/
public def pullbackModuleIdHom (n : ℤ) :
    (Scheme.Modules.pullback g).obj (ℳ.piece n) ⟶
      (Stacks.Conormal.leftGradedPullback g ℳ : SheafOfModules.LeftGradedModule.{u, u, u}
        (s.pullback g).algebra).piece n :=
  𝟙 _

/-- Pulling back the product of a homogeneous section `a` of `𝒜` and a homogeneous section `x`
of `ℳ` over `W` to an open `W' ≤ g⁻¹W` gives the product of the pullbacks of `a` and `x`. -/
public theorem pullbackSection_leftGradedPullback_smul (i n : ℤ) (W : s.base.Opens)
    (W' : S'.Opens) (h : W' ≤ g ⁻¹ᵁ W) (a : (s.algebra.piece i).val.obj (op W))
    (x : (ℳ.piece n).val.obj (op W)) :
    Scheme.Modules.pullbackSection g (ℳ.piece (i + n)) W W' h (ℳ.smul i n (op W) a x) =
      (Stacks.Conormal.leftGradedPullback g ℳ).smul i n (op W')
        (Scheme.Modules.pullbackSection g (s.algebra.piece i) W W' h a)
        (Scheme.Modules.pullbackSection g (ℳ.piece n) W W' h x) := by
  have h1 := Stacks.Conormal.leftGradedPullback_smul_pullbackSection g ℳ i n W a x
  have h2 := (Stacks.Conormal.leftGradedPullback g ℳ).smul_naturality i n (homOfLE h).op
      (Scheme.Modules.pullbackSection g (s.algebra.piece i) W (g ⁻¹ᵁ W) le_rfl a)
      (Scheme.Modules.pullbackSection g (ℳ.piece n) W (g ⁻¹ᵁ W) le_rfl x)
  rw [h1] at h2
  rw [← Stacks.AlgebraicGeometry.ModuleLimits.pullbackSection_shrink g
      (ℳ.piece (i + n)) W (g ⁻¹ᵁ W) W' le_rfl h h,
    ← Stacks.AlgebraicGeometry.ModuleLimits.pullbackSection_shrink g
      (s.algebra.piece i) W (g ⁻¹ᵁ W) W' le_rfl h h,
    ← Stacks.AlgebraicGeometry.ModuleLimits.pullbackSection_shrink g
      (ℳ.piece n) W (g ⁻¹ᵁ W) W' le_rfl h h]
  exact h2

/-- The identity identifications `pullbackUnitalHom s g` and `pullbackModuleIdHom g ℳ` are
compatible with the actions of the algebras on the modules. -/
public theorem pullbackModuleIdHom_compat (i : ℕ) (n : ℤ) (W : s.base.Opens)
    (W' : (s.pullback g).base.Opens) (h : W' ≤ g ⁻¹ᵁ W) (a : s.sectionPieces W i)
    (x : sectionModulePieces ℳ W n) :
    pieceSectionModuleHom (s' := s.pullback g) g (pullbackModuleIdHom g ℳ) ((i : ℤ) + n) W W' h
        (ℳ.smul (i : ℤ) n (op W) a x)
      = (Stacks.Conormal.leftGradedPullback g ℳ : SheafOfModules.LeftGradedModule.{u, u, u}
            (s.pullback g).algebra).smul (i : ℤ) n (op W')
          (pieceSectionHom (s' := s.pullback g) g (pullbackUnitalHom s g) i W W' h a)
          (pieceSectionModuleHom (s' := s.pullback g) g (pullbackModuleIdHom g ℳ) n W W' h x) :=
  pullbackSection_leftGradedPullback_smul g ℳ (i : ℤ) n W W' h a x

end Stacks.RelativeProj.Situation

end
