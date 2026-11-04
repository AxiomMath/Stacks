module

public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Factorization
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceModuli.OtherRoot
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The covering involution of a family of binary quadrics

Let `P` be a scheme with an invertible module `L` and two generating sections `z₀, z₁` (a
morphism `P ⟶ ℙ¹_ℤ`, [Stacks, Tag 01NE]), and an invertible module `M` with sections `A, B, C`
without common zero. The *quadric* `Z ⊂ P` is the zero scheme of `A z₀² + B z₀ z₁ + C z₁²`, a
global section of `(M ⊗ L) ⊗ L`. By the universal property of the zero scheme
([Stacks, Tag 02OR]) a morphism `f : T ⟶ P` factors through `Z` exactly when `f^*(z₀, z₁)` is a
root of the binary quadratic form with coefficients `f^*(A, B, C)`.

Suppose now that `P = W × ℙ¹` is a product, with projections `π` and `τ`, that `(L, z)` is the
pullback of `(𝒪(1), (T₀, T₁))` along `τ` and that the coefficients are pulled back from `W`. Then
`Z ⟶ W` is a family of binary quadrics, of degree two over `W`, and exchanging the two roots is an
automorphism of `Z` over `W`: the morphism `σ : Z ⟶ Z` with components the projection to `W` and
the other root `σ₃ : Z ⟶ ℙ¹` of `Stacks.BinaryQuadric.otherRoot`. It factors through `Z` because
the other root is a root, it is an involution because the other root of the other root is the
root, and it satisfies the line-bundle identity

  `σ^*(L|_Z) ⊗ (L|_Z)² ≅ M|_Z ⊗ L|_Z`,

while it fixes every module pulled back from `W`. For the cyclically symmetric
`(2, 2, 2)`-surfaces of `S × ℙ¹ × ℙ¹ × ℙ¹` of [Stacks, Tag 0DSR] this is the covering involution
of the projection to the first two factors, and the identity is
`σ^*𝓗₂ + 𝓗₂ ≡ 2𝓗₀ + 2𝓗₁`.

## Main definitions

* `Stacks.ProjectiveSpaceModuli.GeneratingTuple.IsDeterminedBy`: a pair only depending on the
  component in `W`.
* `Stacks.BinaryQuadric.quadric`: the zero scheme of `A z₀² + B z₀ z₁ + C z₁²`.
* `Stacks.BinaryQuadric.quadricOtherRoot`: the other root `σ₃ : Z ⟶ ℙ¹`.
* `Stacks.BinaryQuadric.quadricInvolution`: the covering involution `σ : Z ⟶ Z` over `W`.
* `Stacks.BinaryQuadric.quadricInvolutionPullbackIso`: `σ^*(𝓔|_Z) ≅ 𝓔|_Z` for `𝓔` pulled back
  from `W`.
* `Stacks.BinaryQuadric.quadricInvolutionTwistIso`: `σ^*(L|_Z) ⊗ (L|_Z)² ≅ M|_Z ⊗ L|_Z`.

## Main results

* `Stacks.BinaryQuadric.factorsThrough_quadric_iff`: the points of the quadric.
* `Stacks.BinaryQuadric.quadricInvolution_subschemeι_π` and
  `Stacks.BinaryQuadric.quadricInvolution_subschemeι_τ`: `σ` is a morphism over `W` and is the
  other root on the factor `ℙ¹`.
* `Stacks.BinaryQuadric.quadricInvolution_comp_self`: `σ ∘ σ = id`.

## Implementation notes

The product structure is the hypothesis `IsPullback π τ (terminal.from W) (terminal.from ℙ¹)`, so
that `P` can be any model of `W × ℙ¹`; `AlgebraicGeometry.cubeProduct.isPullback_forgetThird_proj`
provides it for `S × ℙ¹ × ℙ¹ × ℙ¹`. The coefficients and the point are arbitrary generating tuples
on `P`: the coefficients are only asked to be determined by `π`
(`Stacks.ProjectiveSpaceModuli.GeneratingTuple.IsDeterminedBy`: two morphisms into `P` with the
same component in `W` pull them back to identified pairs), which holds for a pullback from `W`
(`Stacks.ProjectiveSpaceModuli.isDeterminedBy_pullbackTuple`), and the point is identified in the
sense of Tag 01NE with the tautological pair of `τ`. The quadric is the zero scheme of their own
binary form, so that a form written in any coordinates on `P` can be used directly.

## References

* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
* [Stacks Project, Tag 0DSR](https://stacks.math.columbia.edu/tag/0DSR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.ProjectiveFromSections Stacks.InvertibleStalk Stacks.ProjectiveSpaceModuli

universe u

namespace Stacks.ProjectiveSpaceModuli

variable {X Y Z : Scheme.{u}} {n : ℕ}

/-- The pullback of a pair along a composite is the pullback of the pullback. -/
theorem isomorphic_pullbackTuple_comp (g : Z ⟶ Y) (f : Y ⟶ X) (t : GeneratingTuple X n) :
    Isomorphic (pullbackTuple g (pullbackTuple f t)) (pullbackTuple (g ≫ f) t) :=
  ⟨(Scheme.Modules.pullbackComp g f).app t.bundle, fun i =>
    AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_comp g f t.bundle (t.coord i)⟩

/-- The pullback of a pair only depends on the morphism. -/
theorem isomorphic_pullbackTuple_of_eq {f f' : Y ⟶ X} (e : f = f') (t : GeneratingTuple X n) :
    Isomorphic (pullbackTuple f t) (pullbackTuple f' t) := by
  subst e
  exact isomorphic_refl _

/-- **A pair on `X` is determined by `π : X ⟶ Y`** when its pullbacks along any two morphisms
with the same composite with `π` are identified in the sense of Tag 01NE: the pair only depends
on the component in `Y`. -/
def GeneratingTuple.IsDeterminedBy (t : GeneratingTuple X n) (π : X ⟶ Y) : Prop :=
  ∀ ⦃T : Scheme.{u}⦄ (f g : T ⟶ X), f ≫ π = g ≫ π →
    Isomorphic (pullbackTuple f t) (pullbackTuple g t)

/-- **A pair pulled back along `π` is determined by `π`.** -/
theorem isDeterminedBy_pullbackTuple (π : X ⟶ Y) (t : GeneratingTuple Y n) :
    (pullbackTuple π t).IsDeterminedBy π := fun _ f g e =>
  isomorphic_trans (isomorphic_pullbackTuple_comp f π t)
    (isomorphic_trans (isomorphic_pullbackTuple_of_eq e t)
      (isomorphic_symm (isomorphic_pullbackTuple_comp g π t)))

/-- Being determined by `π` only depends on the pair up to the identification of Tag 01NE. -/
theorem GeneratingTuple.IsDeterminedBy.of_isomorphic {t t' : GeneratingTuple X n} {π : X ⟶ Y}
    (h : t.IsDeterminedBy π) (ht : Isomorphic t t') : t'.IsDeterminedBy π := fun _ f g e =>
  isomorphic_trans (pullbackTuple_isomorphic f (isomorphic_symm ht))
    (isomorphic_trans (h f g e) (pullbackTuple_isomorphic g ht))

end Stacks.ProjectiveSpaceModuli

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The tensor product of two isomorphisms of `𝒪_X`-modules. -/
def tensorObjCongr {A A' B B' : X.Modules} (e : A ≅ A') (e' : B ≅ B') :
    Scheme.Modules.tensorObj A B ≅ Scheme.Modules.tensorObj A' B' :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso e).app B ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor _).obj A').mapIso e'

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.BinaryQuadric

variable {P : Scheme.{u}} (c : GeneratingTuple P 2) (t : GeneratingTuple P 1)

/-- The invertible module `(M ⊗ L) ⊗ L` of which the binary quadratic form with coefficients
`c = (M, (A, B, C))` evaluated at `t = (L, (z₀, z₁))` is a section. -/
abbrev quadricModule : P.Modules :=
  Scheme.Modules.tensorObj (Scheme.Modules.tensorObj c.bundle t.bundle) t.bundle

/-- The module `(M ⊗ L) ⊗ L` is invertible. -/
instance isInvertible_quadricModule :
    AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property
      (quadricModule c t) :=
  (inferInstance : Stacks.Ample.IsInvertibleModule P (quadricModule c t))

/-- **The quadric** `Z(A z₀² + B z₀ z₁ + C z₁²) ⊂ P`: the zero scheme of the value of the binary
quadratic form with coefficients `c` at `t`. -/
@[sga "7 XII 1.1" "special case"]
abbrev quadric : P.IdealSheafData :=
  Stacks.Divisors.zeroScheme P (quadricModule c t) (eval c t)

/-- **The points of the quadric.** A morphism `f : T ⟶ P` factors through the quadric exactly when
the pullback of `t` is a root of the pulled-back binary quadratic form. -/
@[sga "7 XII 1.1" "special case"]
theorem factorsThrough_quadric_iff {T : Scheme.{u}} (f : T ⟶ P) :
    (∃ g : T ⟶ (quadric c t).subscheme, g ≫ (quadric c t).subschemeι = f) ↔
      IsRoot (pullbackTuple f c) (pullbackTuple f t) := by
  rw [← Stacks.Divisors.pullbackSection_eq_zero_iff_factorsThrough_zeroScheme]
  have key : ∀ x : T, ∃ (i₀ : Fin 3) (j₀ : Fin 2)
      (hc : x ∈ Stacks.Ample.nonvanishingLocus (pullbackTuple f c).bundle
        ((pullbackTuple f c).coord i₀))
      (ht : x ∈ Stacks.Ample.nonvanishingLocus (pullbackTuple f t).bundle
        ((pullbackTuple f t).coord j₀))
      (e : Γ(quadricModule c t, ⊤)) (he : f x ∈ Stacks.Ample.nonvanishingLocus _ e),
      stalkCoord _ (mem_nonvanishingLocus_pullbackGlobalSections f he)
          (pullbackGlobalSections f _ (eval c t)) =
        quadPoly (tupleCoord _ hc) (tupleCoord _ ht) := by
    intro x
    obtain ⟨i₀, hc⟩ := c.exists_mem_nonvanishingLocus (f x)
    obtain ⟨j₀, ht⟩ := t.exists_mem_nonvanishingLocus (f x)
    have hE := mem_nonvanishingLocus_tensorSectionsAt
      (mem_nonvanishingLocus_tensorSectionsAt hc ht) ht
    refine ⟨i₀, j₀, mem_nonvanishingLocus_pullbackGlobalSections f hc,
      mem_nonvanishingLocus_pullbackGlobalSections f ht, _, hE, ?_⟩
    refine (stalkCoord_pullbackGlobalSections f hE _).trans ?_
    refine (congrArg (f.stalkMap x).hom
      (stalkCoord_eval_eq_quadPoly (c := c) (t := t) hc ht)).trans ?_
    refine (map_quadPoly _ _ _).trans ?_
    rw [tupleCoord_pullbackTuple f c hc, tupleCoord_pullbackTuple f t ht]
  constructor
  · intro h0
    refine isRoot_of_forall_quadPoly _ _ fun x => ?_
    obtain ⟨i₀, j₀, hc, ht, _, _, hk⟩ := key x
    refine ⟨i₀, j₀, hc, ht, hk.symm.trans ?_⟩
    rw [h0]
    exact stalkCoord_zero _
  · intro h
    refine eq_zero_of_forall_stalkCoord_eq_zero _ fun x => ?_
    obtain ⟨i₀, j₀, hc, ht, _, _, hk⟩ := key x
    exact ⟨_, _, hk.trans (quadPoly_tupleCoord_eq_zero hc ht h)⟩

/-- On the quadric, its inclusion is a root. -/
theorem isRoot_quadric :
    IsRoot (pullbackTuple (quadric c t).subschemeι c) (pullbackTuple (quadric c t).subschemeι t) :=
  (factorsThrough_quadric_iff c t _).1 ⟨𝟙 _, Category.id_comp _⟩

/-- **The other root on the quadric**, `σ₃ : Z ⟶ ℙ¹`: the other root of the binary quadratic
form at the root given by the inclusion. -/
abbrev quadricOtherRoot : (quadric c t).subscheme ⟶ projectiveSpaceAtUniverse.{u} 1 :=
  otherRoot (isRoot_quadric c t)

/-! ### The covering involution of a family of quadrics over `W` -/

variable {W : Scheme.{u}} {π : P ⟶ W} {τ : P ⟶ projectiveSpaceAtUniverse.{u} 1}
  (hP : IsPullback π τ (terminal.from W) (terminal.from (projectiveSpaceAtUniverse.{u} 1)))
  (hc : c.IsDeterminedBy π) (ht : Isomorphic t (tautological τ))

include ht in
/-- A point pulled back along `f` is, up to the identification of Tag 01NE, the tautological pair
of `f ≫ τ`. -/
theorem isomorphic_pullbackTuple_tautological {T : Scheme.{u}} (f : T ⟶ P) :
    Isomorphic (pullbackTuple f t) (tautological (f ≫ τ)) :=
  isomorphic_trans (pullbackTuple_isomorphic f ht)
    (isomorphic_symm (Quotient.exact (pointsOfHom_comp f τ)))

/-- The tautological pairs of two equal morphisms are identified. -/
theorem isomorphic_tautological_of_eq {T : Scheme.{u}} {g g' : T ⟶ projectiveSpaceAtUniverse.{u} 1}
    (e : g = g') : Isomorphic (tautological g) (tautological g') := by
  subst e
  exact isomorphic_refl _

/-- A point pulled back along `f` is identified with the tautological pair of any `g = f ≫ τ`. -/
private theorem isomorphic_pullbackTuple_tautological_of_eq (ht : Isomorphic t (tautological τ))
    {T : Scheme.{u}} {f : T ⟶ P} {g : T ⟶ projectiveSpaceAtUniverse.{u} 1} (e : f ≫ τ = g) :
    Isomorphic (pullbackTuple f t) (tautological g) :=
  e ▸ isomorphic_pullbackTuple_tautological t ht f

/-- The morphism `Z ⟶ P` with components the projection of `Z` to `W` and the other root. -/
def quadricInvolutionToAmbient : (quadric c t).subscheme ⟶ P :=
  hP.lift ((quadric c t).subschemeι ≫ π) (quadricOtherRoot c t) (terminal.hom_ext _ _)

include hc ht in
/-- The morphism with components the projection to `W` and the other root factors through the
quadric: the other root is a root. -/
theorem exists_quadricInvolution :
    ∃ g : (quadric c t).subscheme ⟶ (quadric c t).subscheme,
      g ≫ (quadric c t).subschemeι = quadricInvolutionToAmbient c t hP := by
  refine (factorsThrough_quadric_iff c t _).2 (isRoot_of_isomorphic
    (isRoot_otherRoot (isRoot_quadric c t)) ?_ ?_)
  · exact hc _ _ (by rw [quadricInvolutionToAmbient, IsPullback.lift_fst])
  · refine isomorphic_symm (isomorphic_pullbackTuple_tautological_of_eq t ht ?_)
    rw [quadricInvolutionToAmbient, IsPullback.lift_snd]

/-- **The covering involution of the quadric** over `W`: on the fibre over a point of `W` it
exchanges the two roots of the binary quadratic form. -/
def quadricInvolution : (quadric c t).subscheme ⟶ (quadric c t).subscheme :=
  (exists_quadricInvolution c t hP hc ht).choose

/-- The involution followed by the inclusion of the quadric. -/
@[reassoc]
theorem quadricInvolution_subschemeι :
    quadricInvolution c t hP hc ht ≫ (quadric c t).subschemeι =
      quadricInvolutionToAmbient c t hP :=
  (exists_quadricInvolution c t hP hc ht).choose_spec

/-- **The involution is a morphism over `W`.** -/
@[reassoc]
theorem quadricInvolution_subschemeι_π :
    quadricInvolution c t hP hc ht ≫ (quadric c t).subschemeι ≫ π =
      (quadric c t).subschemeι ≫ π := by
  rw [quadricInvolution_subschemeι_assoc, quadricInvolutionToAmbient, IsPullback.lift_fst]

/-- **On the factor `ℙ¹` the involution is the other root.** -/
@[reassoc]
theorem quadricInvolution_subschemeι_τ :
    quadricInvolution c t hP hc ht ≫ (quadric c t).subschemeι ≫ τ = quadricOtherRoot c t := by
  rw [quadricInvolution_subschemeι_assoc, quadricInvolutionToAmbient, IsPullback.lift_snd]

/-- The pullback of the root along the involution is the other root. -/
theorem isomorphic_pullbackTuple_quadricInvolution :
    Isomorphic (pullbackTuple (quadricInvolution c t hP hc ht)
        (pullbackTuple (quadric c t).subschemeι t))
      (tautological (quadricOtherRoot c t)) :=
  isomorphic_trans (isomorphic_pullbackTuple_comp _ _ t)
    (isomorphic_pullbackTuple_tautological_of_eq t ht (by
      rw [Category.assoc, quadricInvolution_subschemeι_τ]))

/-- **The covering involution is an involution**: `σ ∘ σ = id`, because the other root of the
other root is the root. -/
theorem quadricInvolution_comp_self :
    quadricInvolution c t hP hc ht ≫ quadricInvolution c t hP hc ht = 𝟙 _ := by
  set σ := quadricInvolution c t hP hc ht
  set ι := (quadric c t).subschemeι
  have h₀ := isRoot_quadric c t
  have h₁ := isRoot_pullbackTuple h₀ σ
  have hc₁ : Isomorphic (pullbackTuple σ (pullbackTuple ι c)) (pullbackTuple ι c) :=
    isomorphic_trans (isomorphic_pullbackTuple_comp σ ι c)
      (hc _ _ (by rw [Category.assoc, quadricInvolution_subschemeι_π]))
  have hι : (pointsEquiv _ 1).symm ⟦pullbackTuple ι t⟧ = ι ≫ τ := by
    rw [show (⟦pullbackTuple ι t⟧ : Points _ 1) = ⟦tautological (ι ≫ τ)⟧ from
      Quotient.sound (isomorphic_pullbackTuple_tautological t ht ι)]
    exact (pointsEquiv _ 1).symm_apply_apply (ι ≫ τ)
  have key : σ ≫ σ ≫ ι ≫ τ = ι ≫ τ := by
    calc σ ≫ σ ≫ ι ≫ τ = σ ≫ otherRoot h₀ := by rw [quadricInvolution_subschemeι_τ]
      _ = otherRoot h₁ := (otherRoot_pullbackTuple h₀ σ).symm
      _ = otherRoot (isRoot_of_isomorphic h₁ hc₁
          (isomorphic_pullbackTuple_quadricInvolution c t hP hc ht)) :=
        (otherRoot_congr h₁ hc₁ (isomorphic_pullbackTuple_quadricInvolution c t hP hc ht)).symm
      _ = otherRoot (isRoot_otherRoot h₀) := rfl
      _ = ι ≫ τ := (otherRoot_otherRoot h₀).trans hι
  refine (cancel_mono ι).1 ?_
  rw [Category.assoc, Category.id_comp]
  refine hP.hom_ext ?_ ?_
  · simp only [Category.assoc, σ, ι, quadricInvolution_subschemeι_π]
  · simpa only [Category.assoc] using key

/-! ### Modules on the quadric under the involution -/

/-- **The involution acts trivially on modules pulled back from `W`.** -/
theorem quadricInvolution_subschemeι_comp_of_factors {Y : Scheme.{u}} {g : P ⟶ Y}
    (hg : ∃ k : W ⟶ Y, π ≫ k = g) :
    quadricInvolution c t hP hc ht ≫ (quadric c t).subschemeι ≫ g =
      (quadric c t).subschemeι ≫ g := by
  obtain ⟨k, rfl⟩ := hg
  rw [quadricInvolution_subschemeι_π_assoc]

/-- **The pullback along the involution of a module pulled back from `W`** is that module:
`σ^*(𝓔|_Z) ≅ 𝓔|_Z` for `𝓔 = g^*𝓖` with `g` factoring through `π`. -/
def quadricInvolutionPullbackIso {Y : Scheme.{u}} (g : P ⟶ Y) (hg : ∃ k : W ⟶ Y, π ≫ k = g)
    (G : Y.Modules) :
    (Scheme.Modules.pullback (quadricInvolution c t hP hc ht)).obj
        ((Scheme.Modules.pullback (quadric c t).subschemeι).obj
          ((Scheme.Modules.pullback g).obj G)) ≅
      (Scheme.Modules.pullback (quadric c t).subschemeι).obj
        ((Scheme.Modules.pullback g).obj G) :=
  (Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackComp _ _).app G ≪≫
    (Scheme.Modules.pullbackCongr (by
      rw [Category.assoc, quadricInvolution_subschemeι_comp_of_factors c t hP hc ht hg])).app G ≪≫
    ((Scheme.Modules.pullbackComp _ _).app G).symm

/-- **The line-bundle identity of the covering involution**: for `𝓛 = L|_Z` and `𝓜 = M|_Z`,
`σ^*𝓛 ⊗ 𝓛² ≅ 𝓜 ⊗ 𝓛`. It is `Stacks.BinaryQuadric.otherRootTwistIso` on `Z`: the pullback of
`𝓛` along `σ` is the pullback of `𝒪(1)` along the other root. -/
def quadricInvolutionTwistIso :
    Scheme.Modules.tensorObj
        ((Scheme.Modules.pullback (quadricInvolution c t hP hc ht)).obj
          ((Scheme.Modules.pullback (quadric c t).subschemeι).obj t.bundle))
        (Scheme.Modules.tensorObj ((Scheme.Modules.pullback (quadric c t).subschemeι).obj t.bundle)
          ((Scheme.Modules.pullback (quadric c t).subschemeι).obj t.bundle)) ≅
      Scheme.Modules.tensorObj ((Scheme.Modules.pullback (quadric c t).subschemeι).obj c.bundle)
        ((Scheme.Modules.pullback (quadric c t).subschemeι).obj t.bundle) :=
  Scheme.Modules.tensorObjCongr
      (isomorphic_pullbackTuple_quadricInvolution c t hP hc ht).choose (Iso.refl _) ≪≫
    otherRootTwistIso (isRoot_quadric c t)

end Stacks.BinaryQuadric

end
