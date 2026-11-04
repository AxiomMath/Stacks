module

public import StacksFrontier.AlgebraicGeometry.Stacks.TensorFunctors.TildeCounit
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalStructureMorphismComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.AffineMorphismConstructionA
public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffineGroupoidPresentation

/-!
# Stacks 0GRK: tensor functors out of `QCoh(𝒪_𝒳)` restricted along a scheme

Let `𝒳` be an algebraic stack with affine diagonal, `R` a ring and `F : QCoh(𝒪_𝒳) ⥤ Mod_R` a
right exact tensor functor commuting with direct sums.  Let `g : U ⟶ 𝒳` be a morphism from an
affine scheme `U` with ring of global functions `A`.  Then `C = F(g_{QCoh,*}𝒪_U)` is a commutative
`R`-algebra, and there is a ring map `A → C` such that `F ∘ g_{QCoh,*} : Mod_A ⥤ Mod_R` sends
`M` to `M ⊗_A C` viewed as an `R`-module.

## Affine diagonal

The proof of Stacks 0GRK uses the affine diagonal only to know that `g` is affine
(Stacks 0GQE).  In the source "`𝒳` has affine diagonal" is absolute: by the conventions of
Morphisms of Stacks, Definition 050D, it is the diagonal of `𝒳` over `Spec ℤ`.  Here algebraic
stacks are algebraic stacks over a base scheme `S`, and the absolute diagonal is the diagonal of
the view of `𝒳` over the terminal scheme `⊤_ Scheme`
(`AlgebraicGeometry.Stack.AlgebraicStacks.viewOverIntegers`, Construction A of Stacks 04X5), which
is how the base states the absolute notions of Stacks 050D
(for instance `AlgebraicGeometry.Stack.AlgebraicStacks.IsAbsolutelySeparated`).  With that reading
`g` is affine for every affine `U`
(`AlgebraicGeometry.Stack.AlgebraicStacks.isAffineHom_of_isAffineHom_diagonal_viewOverIntegers`),
and the registered statement carries exactly the source's hypotheses.

The relative reading, with `Δ : 𝒳 ⟶ 𝒳 ×_S 𝒳`, would make the statement false over a non-separated
base.  Let `S` be the affine plane over a field `k` with doubled origin, `𝒳 = S` (its diagonal over
`S` is an isomorphism, so affine), `g : U ⟶ S` one of the two open affine planes `U = Spec A`,
`A = k[x, y]`, and `F = Γ(V, j^*(-)) : QCoh(𝒪_S) ⥤ Mod_{Γ(V)}` restriction to the *other* open
affine plane `j : V ⟶ S` followed by global sections; `F` is an exact tensor functor commuting with
direct sums since `V` is affine.  Then `F(g_{QCoh,*} M~) = Γ(U ∩ V, M~)` with `U ∩ V` the plane
minus the origin.  This functor of `M` is not right exact: it carries the presentation
`A² ⟶ A ⟶ A/(x, y) ⟶ 0` (the first map `(x, y)`) to `A² ⟶ A ⟶ 0 ⟶ 0`, because
`Γ(U ∩ V, 𝒪) = A` and `A/(x, y)` is supported at the origin, and the cokernel `k` of
`A² ⟶ A` is not `0`.  But `M ↦ M ⊗_A C` is right exact for every ring map `A → C`.  (The
absolute diagonal of this `S` is not affine: its inverse image of `U × V` is `U ∩ V`, which is
not affine.)  Under the relative reading
the statement holds once `U ⟶ S` is affine: that is
`exists_ringHom_tensorFunctor_comp_quasicoherentPushforward_of_isAffineHom_structureMorphism`
in the namespace `AlgebraicGeometry.Stack`.
The underlying theorem `AlgebraicGeometry.Stack.affineTensorFunctorIso` needs only that `g` is
affine, and no hypothesis on `𝒳`.

## Main results

* `AlgebraicGeometry.Stack.exists_ringHom_tensorFunctor_comp_affineQuasicoherentPushforward`:
  the statement for an affine `g`.
* `AlgebraicGeometry.Stack.exists_ringHom_tensorFunctor_comp_quasicoherentPushforward`:
  **Stacks 0GRK**, for `𝒳` with affine absolute diagonal, with `F ∘ g_{QCoh,*}` described both on
  `Mod_A` (through `M ↦ M~`) and on `QCoh(𝒪_U)` (through `Γ(U, -)`).
* `exists_ringHom_tensorFunctor_comp_quasicoherentPushforward_of_isAffineHom_structureMorphism`:
  the same for `𝒳` with affine diagonal over `S` and `U` affine over `S`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack

attribute [local instance] FibredSite.monoidalCategoryQuasicoherentModules
  AlgebraicStacks.quasicoherentSymmetricCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {U : BigFppfOver B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}
  {R : Type u} [CommRing R]
  (F : AlgebraicStacks.quasicoherentModules B S hS 𝒳 ⥤ ModuleCat.{u} R) [F.LaxBraided]
  [F.Additive] [PreservesFiniteColimits F] [∀ J : Type u, PreservesColimitsOfShape (Discrete J) F]

/-- **Stacks 0GRK for an affine 1-morphism `g : U ⟶ 𝒳` out of a scheme.**
`C = F(g_{QCoh,*}𝒪_U)` is a commutative `R`-algebra (`AlgebraicGeometry.Stack.affineTensorAlgebra`
with its instances) and there is a ring map `φ : A → C` such that `M ↦ F(g_{QCoh,*} M~)` is
`M ↦ M ⊗_A C` viewed as an `R`-module. -/
theorem exists_ringHom_tensorFunctor_comp_affineQuasicoherentPushforward
    (g : schemeStack.{u, w} B S hS U ⟶ 𝒳) (hg : AlgebraicStacks.IsAffineHom B S hS g) :
    ∃ φ : schemeGlobalRing U →+* affineTensorAlgebra g hg F,
      Nonempty (tildeQuasicoherent.{u, w} U ⋙ affineQuasicoherentPushforward g hg ⋙ F ≅
        ModuleCat.extendScalars φ ⋙
          ModuleCat.restrictScalars (algebraMap R (affineTensorAlgebra g hg F))) :=
  ⟨affineTensorRingHom g hg F, ⟨affineTensorFunctorIso g hg F⟩⟩

/-- **Stacks 0GRK, relative form.**  Let `𝒳` be an algebraic stack with affine diagonal
`Δ : 𝒳 ⟶ 𝒳 ×_S 𝒳` over the base `S`, `R` a ring and `F : QCoh(𝒪_𝒳) ⥤ Mod_R` a right exact tensor
functor commuting with direct sums.  Let `g : U ⟶ 𝒳` be a morphism from an affine scheme `U`, with
ring of global functions `A`, such that `U ⟶ S` is affine.  Then `g` is affine (Stacks 0GQE over
`S`), `C = F(g_{QCoh,*}𝒪_U)` is a commutative `R`-algebra and there is a ring map `φ : A → C` such
that `F ∘ g_{QCoh,*}` sends `M` to `M ⊗_A C` seen as an `R`-module, on `Mod_A` and on `QCoh(𝒪_U)`.
Without the hypothesis on `U ⟶ S` this relative form is false over a non-separated base, see the
module docstring; the source's statement, with the absolute diagonal, is
`AlgebraicGeometry.Stack.exists_ringHom_tensorFunctor_comp_quasicoherentPushforward`. -/
theorem exists_ringHom_tensorFunctor_comp_quasicoherentPushforward_of_isAffineHom_structureMorphism
    (hΔ : Stack.IsAffineHom B S hS (diagonal.{u, u, u + 1} B S hS 𝒳.val))
    (hUaff : IsAffineOver B S hS U)
    (hU : AlgebraicStacks.IsAffineHom B S hS
      (structureMorphism.{u, w} B S hS (schemeStack.{u, w} B S hS U)))
    (g : schemeStack.{u, w} B S hS U ⟶ 𝒳) :
    ∃ hg : AlgebraicStacks.IsAffineHom B S hS g,
      ∃ φ : schemeGlobalRing U →+* affineTensorAlgebra g hg F,
        Nonempty (tildeQuasicoherent.{u, w} U ⋙ affineQuasicoherentPushforward g hg ⋙ F ≅
          ModuleCat.extendScalars φ ⋙
            ModuleCat.restrictScalars (algebraMap R (affineTensorAlgebra g hg F))) ∧
        Nonempty (affineQuasicoherentPushforward g hg ⋙ F ≅
          quasicoherentGlobalSections.{u, w} U ⋙ ModuleCat.extendScalars φ ⋙
            ModuleCat.restrictScalars (algebraMap R (affineTensorAlgebra g hg F))) := by
  have hrel : Stack.IsAffineHom B S hS
      (relativeDiagonalAlgebraicStacks B S hS (structureMorphism.{u, w} B S hS 𝒳)).hom :=
    (relativeProperty_diagonal_iff_relativeDiagonal_structureMorphism B S hS 𝒳
      (fun _ _ f => Space.IsAffineHom B S hS f.hom)).mp hΔ
  have hg : AlgebraicStacks.IsAffineHom B S hS g :=
    AlgebraicStacks.isAffineHom_of_comp_of_isAffineHom_relativeDiagonal B S hS g
      (structureMorphism.{u, w} B S hS (schemeStack.{u, w} B S hS U))
      (structureMorphism.{u, w} B S hS 𝒳) (eqToIso (comp_structureMorphism B S hS g).symm) hU
      hrel
  exact ⟨hg, affineTensorRingHom g hg F, ⟨affineTensorFunctorIso g hg F⟩,
    ⟨affineTensorFunctorGlobalSectionsIso g hg F hUaff⟩⟩

/-- **Stacks 0GRK.**  Let `𝒳` be an algebraic stack with affine diagonal, `R` a ring and
`F : QCoh(𝒪_𝒳) ⥤ Mod_R` a right exact tensor functor (additive, preserving finite colimits, lax
symmetric monoidal) which commutes with direct sums.  Let `g : U ⟶ 𝒳` be a morphism with `U` an
affine scheme, with ring of global functions `A`.  Then `g` is affine, and

1. `C = F(g_{QCoh,*}𝒪_U)` is a commutative `R`-algebra
   (`AlgebraicGeometry.Stack.affineTensorAlgebra` with its `CommRing` and `Algebra R`
   instances), and
2. there is a ring map `φ : A → C`

such that `F ∘ g_{QCoh,*}` sends `M` to `M ⊗_A C` seen as an `R`-module: both as a functor
`Mod_A ⥤ Mod_R` through `M ↦ M~`, and as a functor `QCoh(𝒪_U) ⥤ Mod_R` through
`N ↦ Γ(U, N)`, which is how `QCoh(𝒪_U)` is `Mod_A`
(`AlgebraicGeometry.Stack.tildeCounitIso`).

"Affine diagonal" is absolute, as in the source (Morphisms of Stacks, Definition 050D): it is the
diagonal of the view of `𝒳` over the terminal scheme `Spec ℤ`
(`AlgebraicGeometry.Stack.AlgebraicStacks.viewOverIntegers`), which lies in every big fppf site
(`AlgebraicGeometry.Stack.contains_terminalScheme`).  That `g` is affine is
`AlgebraicGeometry.Stack.AlgebraicStacks.isAffineHom_of_isAffineHom_diagonal_viewOverIntegers`
(Stacks 0GQE over `Spec ℤ`). -/
@[stacks 0GRK]
theorem exists_ringHom_tensorFunctor_comp_quasicoherentPushforward
    (hΔ : Stack.IsAffineHom B (⊤_ Scheme.{u}) (contains_terminalScheme B)
      (diagonal.{u, u, u + 1} B (⊤_ Scheme.{u}) (contains_terminalScheme B)
        (AlgebraicStacks.viewOverIntegers B S hS (contains_terminalScheme B) 𝒳).val))
    (hUaff : IsAffineOver B S hS U) (g : schemeStack.{u, w} B S hS U ⟶ 𝒳) :
    ∃ hg : AlgebraicStacks.IsAffineHom B S hS g,
      ∃ φ : schemeGlobalRing U →+* affineTensorAlgebra g hg F,
        Nonempty (tildeQuasicoherent.{u, w} U ⋙ affineQuasicoherentPushforward g hg ⋙ F ≅
          ModuleCat.extendScalars φ ⋙
            ModuleCat.restrictScalars (algebraMap R (affineTensorAlgebra g hg F))) ∧
        Nonempty (affineQuasicoherentPushforward g hg ⋙ F ≅
          quasicoherentGlobalSections.{u, w} U ⋙ ModuleCat.extendScalars φ ⋙
            ModuleCat.restrictScalars (algebraMap R (affineTensorAlgebra g hg F))) := by
  have hg : AlgebraicStacks.IsAffineHom B S hS g :=
    AlgebraicStacks.isAffineHom_of_isAffineHom_diagonal_viewOverIntegers B S hS
      (contains_terminalScheme B) hUaff hΔ g
  exact ⟨hg, affineTensorRingHom g hg F, ⟨affineTensorFunctorIso g hg F⟩,
    ⟨affineTensorFunctorGlobalSectionsIso g hg F hUaff⟩⟩

end AlgebraicGeometry.Stack
