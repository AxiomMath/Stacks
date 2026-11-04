module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.BoundedAbove
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentBiproduct
import StacksCore.Tactic.EgaSgaAttribute

/-!
# An `m`-pseudo-coherent approximation already proves `m`-pseudo-coherence

Stacks 08CC part (1) establishes `m`-pseudo-coherence of an object of `D(𝒪_X)` from local
approximations by *strictly perfect* complexes. This file weakens the approximating object to an
arbitrary `m`-pseudo-coherent one: if `φ : A ⟶ B` is an isomorphism on cohomology in every degree
above `m` and an epimorphism in degree `m`, and `A` is `m`-pseudo-coherent, then so is `B`.

The mechanism is the cone. Completing `φ` to a distinguished triangle `A ⟶ B ⟶ C ⟶ A⟦1⟧`, the
long exact cohomology sequence forces `H^j(C) = 0` for every `j ≥ m`, so `C` is
`m`-pseudo-coherent for trivial reasons
(`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_isZero_homology_ge`), and Stacks 08CD
part (2) applied to that triangle gives `B`.

Both halves of Stacks 09VA need the cone computation. In the forward direction the triangle is
the one on a strictly perfect approximation of `E`, whose cone therefore has no cohomology from
degree `m` upwards; in the converse direction it is the triangle on the chosen map
`𝒪_Z^{⊕n}[-p] ⟶ E`, whose cone has no cohomology from degree `p` upwards. Both are the statement
below with its two hypotheses read at the appropriate degree.

## Main results

* `CategoryTheory.isZero_homology_obj₃_of_distinguished`: the cone of a morphism which is an
  isomorphism on cohomology above `m` and an epimorphism in degree `m` has no cohomology in any
  degree at least `m`.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_approximation`: Stacks 08CC part (1)
  with an `m`-pseudo-coherent approximating object in place of a strictly perfect one.

## Implementation notes

The vanishing is read off three consecutive terms of the long exact sequence of the triangle for
the homological functor `DerivedCategory.homologyFunctor`, through Mathlib's
`CategoryTheory.Functor.homologySequence_exact₁`, `homologySequence_exact₂` and
`homologySequence_exact₃`, in the idiom already used by
`CategoryTheory.isIso_homology_of_homotopyTriangleMorphism` in
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/PseudoCoherentTriangle.lean`. The three steps are:
`H^j(mor₂) = 0` because `H^j(mor₁)` is an epimorphism; the connecting map `δ` is a monomorphism
because `H^j(mor₂) = 0`; and `δ = 0` because `H^{j+1}(mor₁)` is a monomorphism. A monomorphism
which is zero has a zero source.

The shift sequence of `DerivedCategory.homologyFunctor C 0` is set up so that its `j`-th member
is `DerivedCategory.homologyFunctor C j` by `rfl`
(`DerivedCategory.shift_homologyFunctor`), so no transport between the two spellings is needed.

## References

* [Stacks Project, Lemma 20.46.9 (Tag 08CC)](https://stacks.math.columbia.edu/tag/08CC)
* [Stacks Project, Lemma 20.46.10 (Tag 08CD)](https://stacks.math.columbia.edu/tag/08CD)
* [Stacks Project, Lemma 20.49.2 (Tag 09VA)](https://stacks.math.columbia.edu/tag/09VA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated StrictlyPerfect

universe d u v₁ u₁

namespace CategoryTheory

/-- **The cone of a morphism which is an isomorphism on cohomology above `m` and an epimorphism in
degree `m` has no cohomology in any degree at least `m`.**

Three consecutive terms of the long exact cohomology sequence of the triangle do it. Exactness at
`H^j(B)` and surjectivity of `H^j(A) ⟶ H^j(B)` make `H^j(B) ⟶ H^j(C)` zero; exactness at `H^j(C)`
then makes the connecting map `δ : H^j(C) ⟶ H^{j+1}(A)` a monomorphism; and exactness at
`H^{j+1}(A)` together with injectivity of `H^{j+1}(A) ⟶ H^{j+1}(B)` makes `δ` zero. -/
@[sga "6 I 1.4.2" "(ii) ⇒ (i)"]
public theorem isZero_homology_obj₃_of_distinguished {C : Type u₁} [Category.{v₁} C] [Abelian C]
    [HasDerivedCategory.{d} C] (m : ℤ) (T : Triangle (DerivedCategory C))
    (hT : T ∈ distinguishedTriangles)
    (hiso : ∀ j : ℤ, m < j → IsIso ((DerivedCategory.homologyFunctor C j).map T.mor₁))
    (hepi : Epi ((DerivedCategory.homologyFunctor C m).map T.mor₁)) (j : ℤ) (hj : m ≤ j) :
    IsZero ((DerivedCategory.homologyFunctor C j).obj T.obj₃) := by
  have hepij : Epi ((DerivedCategory.homologyFunctor C j).map T.mor₁) := by
    rcases eq_or_lt_of_le hj with rfl | hlt
    · exact hepi
    · have := hiso j hlt
      infer_instance
  have hmonoj : Mono ((DerivedCategory.homologyFunctor C (j + 1)).map T.mor₁) := by
    have := hiso (j + 1) (by omega)
    infer_instance
  set F := DerivedCategory.homologyFunctor C 0 with hF
  -- `H^j(T.mor₂) = 0`, by exactness at `H^j(T.obj₂)` and surjectivity of `H^j(T.mor₁)`.
  have hmor₂ : (DerivedCategory.homologyFunctor C j).map T.mor₂ = 0 :=
    (F.homologySequence_exact₂ T hT j).epi_f_iff.mp hepij
  -- The connecting map is a monomorphism, by exactness at `H^j(T.obj₃)`.
  have hδmono : Mono (F.homologySequenceδ T j (j + 1) rfl) :=
    (F.homologySequence_exact₃ T hT j (j + 1) rfl).mono_g hmor₂
  -- The connecting map is zero, by exactness at `H^{j+1}(T.obj₁)` and injectivity there.
  have hδzero : F.homologySequenceδ T j (j + 1) rfl = 0 :=
    (F.homologySequence_exact₁ T hT j (j + 1) rfl).mono_g_iff.mp hmonoj
  have hid : 𝟙 ((F.shift j).obj T.obj₃) ≫ F.homologySequenceδ T j (j + 1) rfl =
      0 ≫ F.homologySequenceδ T j (j + 1) rfl := by
    rw [hδzero, comp_zero, zero_comp]
  exact (IsZero.iff_id_eq_zero _).mpr (hδmono.right_cancellation _ _ hid)

end CategoryTheory

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u, u}} [HasDerivedCategory.{d} (OXMod.{u, u} X)]

/-- **Stacks 08CC part (1) with an `m`-pseudo-coherent approximation.** Let `φ : A ⟶ B` be a
morphism of `D(𝒪_X)` which is an isomorphism on cohomology in every degree above `m` and an
epimorphism in degree `m`, and let `A` be `m`-pseudo-coherent. Then `B` is `m`-pseudo-coherent.

Complete `φ` to a distinguished triangle `A ⟶ B ⟶ C ⟶ A⟦1⟧`. Its third term has no cohomology
from degree `m` upwards (`CategoryTheory.isZero_homology_obj₃_of_distinguished`), hence is
`m`-pseudo-coherent, and so is its first term; Stacks 08CD part (2) gives the second.

This is what makes a *non*-strictly-perfect approximation usable, and it is the form in which
both halves of Stacks 09VA pass from a local approximation to the conclusion. -/
public theorem isPseudoCoherentFrom_of_approximation (m : ℤ)
    {A B : DerivedCategory (OXMod.{u, u} X)} (hA : IsPseudoCoherentFrom A m) (φ : A ⟶ B)
    (hiso : ∀ j : ℤ, m < j → IsIso ((DerivedCategory.homologyFunctor _ j).map φ))
    (hepi : Epi ((DerivedCategory.homologyFunctor _ m).map φ)) :
    IsPseudoCoherentFrom B m := by
  obtain ⟨Cone, g, h, hT⟩ := distinguished_cocone_triangle φ
  refine isPseudoCoherentFrom_obj₂_of_distinguished m (Triangle.mk φ g h) hT hA ?_
  exact isPseudoCoherentFrom_of_isZero_homology_ge _ m fun j hj =>
    isZero_homology_obj₃_of_distinguished m (Triangle.mk φ g h) hT hiso hepi j hj

end AlgebraicGeometry.RingedSpace

end
