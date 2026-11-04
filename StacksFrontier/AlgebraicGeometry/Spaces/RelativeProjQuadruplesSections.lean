module

public import StacksFrontier.AlgebraicGeometry.RelativeProjTwistChartBridge.ClassifyingOverBase
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjQuadruplesRepresentability

/-!
# The fibre of the functor of quadruples is the sections of the relative Proj

In Situation 0849 let `X` be an algebraic space over a scheme `S`, let `𝒜` be a quasi-coherent
graded `𝒪_X`-algebra and let `F` be the functor of quadruples of Stacks 084A.  The second
assertion of Stacks 084B is a canonical isomorphism `Proj_Z(g^*𝒜) = Z ×_X F`; read at a `T`-point
`f` of `X` it says that the fibre of `F(T)` over `f` is the set of **sections** of the structure
morphism `Proj_T(f^*𝒜) ⟶ T`, because a `T`-point of `T ×_X F` over the identity of `T` is exactly
such a section.

`StacksFrontier/AlgebraicGeometry/Spaces/RelativeProjQuadruplesRepresentability.lean` attached to
every point of the fibre its morphism `T ⟶ Proj_T(f^*𝒜)` and proved that distinct points get
distinct morphisms, so the fibre is a *subset* of the morphisms.  Its implementation notes name
the one input that was missing for the image to be identified: the statement that the morphism
attached to a point, followed by the structure morphism of the relative homogeneous spectrum, is
the morphism to the base that the point records.  That statement is now
`...RelativeProjInvertibleMorphism.F.classifyingMorphism_comp_toBase`, and this file spends it:
the fibre of `F(T)` over `f` is in bijection with the sections of `Proj_T(f^*𝒜) ⟶ T`.

## Main results

* `AlgebraicGeometry.Space.GradedAlgebraPoints.F.projMorphism_comp_toBase`: the morphism attached
  to a point of the fibre is a **section** of `Proj_T(f^*𝒜) ⟶ T`.
* `AlgebraicGeometry.Space.GradedAlgebraPoints.F.sectionEquiv`: the fibre of `F(T)` over a
  `T`-point `f` of `X` **is** the set of sections of `Proj_T(f^*𝒜) ⟶ T`, by the morphism
  attached to a point.  This is the second assertion of Stacks 084B at the point `f`, on the
  points of the two functors.
* `AlgebraicGeometry.Space.GradedAlgebraPoints.F.sectionEquiv_comap`: the bijection is compatible
  with restricting the family along `g : X' ⟶ X`, which is the third assertion of Stacks 084B for
  it.

## Implementation notes

**What this file is not.**  It is not Stacks 084B.  Everything below is stated for a family of
quasi-coherent graded algebras on the scheme points of `X` taken as data — the
`AlgebraicGeometry.Space.GradedAlgebraPoints.ofQuasicoherentFamily` of the previous file — and
not for the restriction `f^*𝒜` of a graded algebra on `X`, and it is stated at one point `f` at a
time rather than as an isomorphism of functors.  Both gaps are recorded in the implementation
notes of `StacksFrontier/AlgebraicGeometry/Spaces/RelativeProjQuadruples.lean`, and neither is
closed here.  No declaration in this file carries a Stacks attribute.

**How the image is identified.**  A point of the fibre of `F(T)` over `f` is a class of
quadruples of `f^*𝒜` over the *identity* of the scheme of `T`, so the morphism to the base it
records is that identity, by
`AlgebraicGeometry.Space.GradedAlgebraPoints.F.toSchemeF`.  The over-base identity therefore
reads: the attached morphism composed with the structure morphism is the identity, i.e. the
attached morphism is a section.  Conversely a section is the image of the point of the extended
functor the representing bijection attaches to it, that point is a point of the union because the
test scheme is quasi-compact, and the over-base identity computes its morphism to the base to be
the identity — so it lies in the fibre.  The inclusion of the union into its extension,
`...RelativeProjInvertibleMorphism.F.toLim`, is the inverse of
`...RelativeProjQcohSheaf.F.limEquiv` on a quasi-compact test scheme, which is the content of
`AlgebraicGeometry.Space.GradedAlgebraPoints.F.limEquiv_symm_eq_toLim` below.

**Quasi-compactness of the test object is not a weakening**, for the reason given in the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/RelativeProjQuadruplesRepresentability.lean`: the source's
`F(T)` is the union of the sets of quadruples exactly on a quasi-compact `T`.

## References

* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 084A](https://stacks.math.columbia.edu/tag/084A)
* [Stacks Project, Tag 0849](https://stacks.math.columbia.edu/tag/0849)
* [Stacks Project, Tag 01NY](https://stacks.math.columbia.edu/tag/01NY)
* [Stacks Project, Tag 01NZ](https://stacks.math.columbia.edu/tag/01NZ)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

open AlgebraicGeometry Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

universe u

namespace AlgebraicGeometry.Space

namespace GradedAlgebraPoints

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

variable (alg : ∀ T : BigFppfOver B S hS, (yoneda.obj T ⟶ X) →
  SheafGradedAlgebra ((BigFppfOver.toScheme B S hS).obj T))

/-! ### The inclusion of the union into its extension -/

/-- **On a quasi-compact test scheme the inclusion of the union of the sets of quadruples into its
extension over the quasi-compact opens is the inverse of the identification of the two.**

Both sides send a point `ξ` of the union to the compatible family whose value at `g : W ⟶ T` is
the pullback of `ξ` along `g`. -/
theorem F.limEquiv_symm_eq_toLim {Z : Scheme.{u}} (A : SheafGradedAlgebra Z)
    (T : Scheme.{u}) (hT : CompactSpace T)
    (ξ : Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.F (situationAlgebra A) T) :
    (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.F.limEquiv
        (situationAlgebra A) T hT).symm ξ =
      Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.F.toLim A ξ :=
  rfl

/-- The point of the extended functor attached to a point of a fibre of `F(T)` is the image of the
corresponding point of the scheme-level union under that inclusion. -/
theorem F.limPoint_eq_toLim (T : BigFppfOver B S hS)
    (hT : CompactSpace ((BigFppfOver.toScheme B S hS).obj T)) (f : yoneda.obj T ⟶ X)
    (q : F.fibre (ofQuasicoherentFamily alg) T f) :
    F.limPoint alg T hT f q =
      Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.F.toLim (alg T f)
        (F.toSchemeF (ofQuasicoherentFamily alg) T f q) :=
  rfl

/-! ### The attached morphism is a section -/

/-- **The morphism attached to a point of the fibre is a section of the relative homogeneous
spectrum.**

A point of the fibre of `F(T)` over a `T`-point `f` of `X` is a class of quadruples of `f^*𝒜`
over the identity of the scheme of `T`, so the morphism to the base it records is that identity;
the over-base identity
`...RelativeProjInvertibleMorphism.F.classifyingMorphism_comp_toBase` for the representation of
Tags 01NY and 01NZ then says that the attached morphism, followed by the structure morphism of
`Proj_T(f^*𝒜)`, is the identity. -/
theorem F.projMorphism_comp_toBase (T : BigFppfOver B S hS)
    (hT : CompactSpace ((BigFppfOver.toScheme B S hS).obj T)) (f : yoneda.obj T ⟶ X)
    (q : F.fibre (ofQuasicoherentFamily alg) T f) :
    F.projMorphism alg T hT f q ≫ (relativeProj (alg T f)).toBase =
      CategoryStruct.id ((BigFppfOver.toScheme B S hS).obj T) := by
  rw [F.projMorphism, F.limPoint_eq_toLim]
  exact Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.homEquiv_symm_toLim_comp_toBase
    (alg T f) (F.toSchemeF (ofQuasicoherentFamily alg) T f q)

/-- **Every section comes from a point of the fibre.**

The representing bijection of Tags 01NY and 01NZ attaches to a section a point of the extended
functor, which on a quasi-compact test scheme is a point of the union; the over-base identity
computes the morphism to the base that point records to be the identity, so the point lies in the
fibre of `F(T)` over `f`. -/
theorem F.surjective_projMorphism_sections (T : BigFppfOver B S hS)
    (hT : CompactSpace ((BigFppfOver.toScheme B S hS).obj T)) (f : yoneda.obj T ⟶ X)
    (k : (BigFppfOver.toScheme B S hS).obj T ⟶ (relativeProj (alg T f)).scheme)
    (hk : k ≫ (relativeProj (alg T f)).toBase =
      CategoryStruct.id ((BigFppfOver.toScheme B S hS).obj T)) :
    ∃ q : F.fibre (ofQuasicoherentFamily alg) T f, F.projMorphism alg T hT f q = k := by
  obtain ⟨ζ, hζ⟩ :
      ∃ ζ : Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.F
          (situationAlgebra (alg T f)) ((BigFppfOver.toScheme B S hS).obj T),
        ζ = Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.F.limEquiv
          (situationAlgebra (alg T f)) ((BigFppfOver.toScheme B S hS).obj T) hT
            ((relativeProjRepresentableByFunctorUnconditional (alg T f)).homEquiv k) :=
    ⟨_, rfl⟩
  have htoLim : Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.F.toLim (alg T f) ζ =
      (relativeProjRepresentableByFunctorUnconditional (alg T f)).homEquiv k := by
    rw [← F.limEquiv_symm_eq_toLim (alg T f) _ hT, hζ]
    exact Equiv.symm_apply_apply _ _
  have hbase : ζ.1 = CategoryStruct.id ((BigFppfOver.toScheme B S hS).obj T) := by
    have h1 :=
      Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.homEquiv_symm_toLim_comp_toBase
        (alg T f) ζ
    rw [htoLim, Equiv.symm_apply_apply, hk] at h1
    exact h1.symm
  clear hζ
  obtain ⟨g, c⟩ := ζ
  obtain rfl : g = CategoryStruct.id ((BigFppfOver.toScheme B S hS).obj T) := hbase
  refine ⟨c, ?_⟩
  show (relativeProjRepresentableByFunctorUnconditional (alg T f)).homEquiv.symm
      (Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.F.toLim (alg T f)
        ⟨CategoryStruct.id ((BigFppfOver.toScheme B S hS).obj T), c⟩) = k
  rw [htoLim]
  exact Equiv.symm_apply_apply _ _

/-! ### The fibre is the set of sections -/

/-- **The fibre of `F(T)` over a `T`-point of `X` is the set of sections of the relative
homogeneous spectrum of the restricted algebra.**

This is the second assertion of Stacks 084B read at the point `f`, on the points of the two
functors: a `T`-point of `T ×_X F` over the identity of `T` is a point of the fibre of `F(T)` over
`f`, and a `T`-point of `Proj_T(f^*𝒜)` over the identity of `T` is a section of its structure
morphism.

Injectivity is
`AlgebraicGeometry.Space.GradedAlgebraPoints.F.injective_projMorphism`, which the previous file
proves from the representability of Tags 01NY and 01NZ; surjectivity onto the sections is
`AlgebraicGeometry.Space.GradedAlgebraPoints.F.surjective_projMorphism_sections`, which the
over-base identity supplies. -/
def F.sectionEquiv (T : BigFppfOver B S hS)
    (hT : CompactSpace ((BigFppfOver.toScheme B S hS).obj T)) (f : yoneda.obj T ⟶ X) :
    F.fibre (ofQuasicoherentFamily alg) T f ≃
      {k : (BigFppfOver.toScheme B S hS).obj T ⟶ (relativeProj (alg T f)).scheme //
        k ≫ (relativeProj (alg T f)).toBase =
          CategoryStruct.id ((BigFppfOver.toScheme B S hS).obj T)} :=
  Equiv.ofBijective
    (fun q => ⟨F.projMorphism alg T hT f q, F.projMorphism_comp_toBase alg T hT f q⟩)
    ⟨fun _ _ h => F.injective_projMorphism alg T hT f (congrArg Subtype.val h),
      fun k => by
        obtain ⟨q, hq⟩ := F.surjective_projMorphism_sections alg T hT f k.1 k.2
        exact ⟨q, Subtype.ext hq⟩⟩

/-- The section of `Proj_T(f^*𝒜) ⟶ T` attached by `F.sectionEquiv` to a point `q` of the fibre is
`F.projMorphism alg T hT f q`. -/
@[simp] theorem F.sectionEquiv_apply (T : BigFppfOver B S hS)
    (hT : CompactSpace ((BigFppfOver.toScheme B S hS).obj T)) (f : yoneda.obj T ⟶ X)
    (q : F.fibre (ofQuasicoherentFamily alg) T f) :
    (F.sectionEquiv alg T hT f q).1 = F.projMorphism alg T hT f q :=
  rfl

/-- **Compatibility with further base change.**  For `g : X' ⟶ X` the bijection for the restricted
family at a `T`-point `f` of `X'` is the bijection for the original family at the `T`-point
`f ≫ g` of `X`: the same bijection, onto the sections of the same relative homogeneous spectrum
`Proj_T((g ∘ f)^*𝒜) ⟶ T`.

Both sides are the same term, because the restricted family is the original family reindexed along
composition with `g`, which is
`AlgebraicGeometry.Space.GradedAlgebraPoints.comap_ofQuasicoherentFamily`. -/
theorem F.sectionEquiv_comap (g : X' ⟶ X) (T : BigFppfOver B S hS)
    (hT : CompactSpace ((BigFppfOver.toScheme B S hS).obj T)) (f : yoneda.obj T ⟶ X') :
    F.sectionEquiv (fun T f => alg T (f ≫ g)) T hT f = F.sectionEquiv alg T hT (f ≫ g) :=
  rfl

end GradedAlgebraPoints

end AlgebraicGeometry.Space

end
