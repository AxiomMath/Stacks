module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Representing a morphism of `D^b(A)` by a roof of uniformly bounded complexes

Let `A` be an abelian category with a derived category. An object of the bounded derived
category `D^b(A)` is, by definition, an object of `D(A)` which is cohomologically bounded; it
is *not* given to us as a complex. This file records that a morphism between two such objects
can always be presented completely concretely: there are honest cochain complexes `F` and `G`,
each strictly concentrated in degrees `[a, b]` for **one** pair of bounds `a ≤ b` serving both,
isomorphisms identifying the two objects with `F` and `G` in `D(A)`, and a right fraction
`inv (Q.map s) ≫ Q.map g` through a third complex `P`, also strictly in `[a, b]`, which
represents the morphism under those identifications.

## The argument

Both halves are already in Mathlib; the work is only in making their bounds agree.

`DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE` turns each of the two objects into a
complex, but with its own bounds: `F` lands in `[aF, bF]` and `G` in `[aG, bG]`, read off the
`IsGE`/`IsLE` witnesses packaged in the boundedness property of the objects.
`DerivedCategory.right_fac_of_isStrictlyLE_of_isStrictlyGE`, which produces the roof, needs its
source and target to share a lower bound, so the two intervals have to be merged first: with
`a = min aF aG` and `b = max bF bG`, `CochainComplex.isStrictlyGE_of_ge` and
`CochainComplex.isStrictlyLE_of_le` widen both complexes to `[a, b]`, and the lemma then returns
`P` already strictly in `[a, b]` as well. Finally, the equation Mathlib gives is a
factorization of `eA.inv ≫ f ≫ eB.hom`, the transport of `f` along the two identifications,
which is turned into the stated equation by cancelling `eA`.

Uniform bounds are what makes this usable. A consumer which has to move a morphism of `D^b(A)`
across an equivalence of categories, or apply a degreewise construction to the complexes
representing it, needs the three complexes to be bounded by the *same* integers; separate
bounds per complex would have to be merged again at every such step.

## Main results

* `DerivedCategory.Bounded.exists_roof`: a morphism of `D^b(A)` is represented by a right
  fraction between cochain complexes which are all strictly bounded by one pair of integers.
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory Category Limits

namespace DerivedCategory.Bounded

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- An object of `D(A)` with cohomology in `[aX, bX]` is isomorphic to a complex strictly
concentrated in any larger interval `[a, b]`. -/
private theorem exists_iso_Q_obj_of_bounds (X : DerivedCategory C) (aX bX a b : ℤ)
    [X.IsGE aX] [X.IsLE bX] (ha : a ≤ aX) (hb : bX ≤ b) :
    ∃ F : CochainComplex C ℤ, F.IsStrictlyGE a ∧ F.IsStrictlyLE b ∧
      Nonempty (X ≅ DerivedCategory.Q.obj F) := by
  obtain ⟨F, _, _, e⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE X aX bX
  exact ⟨F, F.isStrictlyGE_of_ge a aX ha, F.isStrictlyLE_of_le bX b hb, e⟩

/-- A morphism `f` between two objects of the bounded derived category `D^b(A)` is represented
by a **roof of uniformly bounded complexes**: there are cochain complexes `F`, `G` and `P` and
integers `a`, `b` such that all three of `F`, `G`, `P` are strictly concentrated in degrees
`[a, b]`, there are isomorphisms `eA : A ≅ Q.obj F` and `eB : B ≅ Q.obj G` in `D(A)`, and there
are a quasi-isomorphism `s : P ⟶ F` and a map `g : P ⟶ G` whose right fraction
`inv (Q.map s) ≫ Q.map g` is `f` read through `eA` and `eB`.

The single pair of bounds `a`, `b` covering all three complexes is the point: it is what lets a
consumer feed the whole roof to a degreewise construction, or transport it along an equivalence,
without renegotiating bounds at each step. -/
theorem exists_roof (A B : DerivedCategory.Bounded C) (f : A.obj ⟶ B.obj) :
    ∃ (F G P : CochainComplex C ℤ) (a b : ℤ),
      F.IsStrictlyGE a ∧ F.IsStrictlyLE b ∧
      G.IsStrictlyGE a ∧ G.IsStrictlyLE b ∧
      P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      ∃ (eA : A.obj ≅ DerivedCategory.Q.obj F)
        (eB : B.obj ≅ DerivedCategory.Q.obj G)
        (s : P ⟶ F) (_ : IsIso (DerivedCategory.Q.map s))
        (g : P ⟶ G),
        eA.hom ≫ inv (DerivedCategory.Q.map s) ≫ DerivedCategory.Q.map g =
          f ≫ eB.hom := by
  obtain ⟨⟨aF, haF⟩, ⟨bF, hbF⟩⟩ := A.property
  obtain ⟨⟨aG, haG⟩, ⟨bG, hbG⟩⟩ := B.property
  -- Merge the two intervals into one pair of bounds serving both complexes.
  obtain ⟨F, hFa, hFb, ⟨eA⟩⟩ := exists_iso_Q_obj_of_bounds A.obj aF bF (min aF aG) (max bF bG)
    (by omega) (by omega)
  obtain ⟨G, hGa, hGb, ⟨eB⟩⟩ := exists_iso_Q_obj_of_bounds B.obj aG bG (min aF aG) (max bF bG)
    (by omega) (by omega)
  -- With a common lower bound available, the calculus of fractions supplies the roof.
  obtain ⟨P, hPge, hPle, s, hs, g, hg⟩ :=
    DerivedCategory.right_fac_of_isStrictlyLE_of_isStrictlyGE
      (C := C) (min aF aG) (max bF bG) (eA.inv ≫ f ≫ eB.hom)
  refine ⟨F, G, P, min aF aG, max bF bG, hFa, hFb, hGa, hGb, hPge, hPle, eA, eB, s, hs, g, ?_⟩
  calc
    eA.hom ≫ inv (DerivedCategory.Q.map s) ≫ DerivedCategory.Q.map g =
        eA.hom ≫ eA.inv ≫ f ≫ eB.hom := by rw [hg]
    _ = f ≫ eB.hom := by simp

end DerivedCategory.Bounded

end
