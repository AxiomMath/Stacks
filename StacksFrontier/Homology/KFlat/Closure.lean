module

public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.Triangle

@[expose] public section

/-!
# Closure properties of K-flatness: translation, direct sums, split extensions

Let `R` be a commutative ring. K-flatness of a cochain complex of `R`-modules (Stacks 06XZ) is
stable under three operations beyond the two recognition principles of
`StacksFrontier.Homology.KFlat.Flat`:

* translation, `K` K-flat implies `K⟦n⟧` K-flat;
* arbitrary direct sums, a coproduct of K-flat complexes being K-flat;
* two-out-of-three along a *degreewise split* short exact sequence.

The third is what the two-out-of-three property of
`CochainComplex.KFlat.kFlat_two_out_of_three` (Stacks 0BYH) cannot supply: that statement
requires the quotient to be termwise flat, which a direct sum of translates of a merely K-flat
complex is not. A degreewise splitting replaces that hypothesis, because the splitting is itself
the termwise direct-sum decomposition that flatness was being used to produce.

## Main results

* `CochainComplex.kFlat_of_iso`: K-flatness transports along an isomorphism of complexes.
* `CochainComplex.KFlat.kFlat_shift`: a translate of a K-flat complex is K-flat.
* `CochainComplex.KFlat.kFlat_coproduct`: a coproduct of K-flat complexes is K-flat.
* `CochainComplex.KFlat.kFlat_two_out_of_three_of_degreewiseSplit`: if two of the three terms of
  a degreewise split short exact sequence of complexes are K-flat, so is the third.

## Implementation notes

*Translation.* `Tot(M ⊗_R -)` is `(curriedTensor _).map₂CochainComplex.obj M`, which carries
Mathlib's `Functor.CommShift ℤ` instance — the Koszul-signed comparison
`Tot(M ⊗ K⟦n⟧) ≅ Tot(M ⊗ K)⟦n⟧` of Stacks 0FNG. So the translate of an acyclic complex is all
that is needed, which is `acyclic_shiftFunctor`.

*Direct sums.* This is the argument of `CochainComplex.KFlat.kFlat_colimit` (Stacks 06Y3) run
with the shape `Discrete ι` instead of a filtered category. Filteredness enters that proof
only through exactness of colimits of the given shape in `ModuleCat R`; for a coproduct that is
Grothendieck's AB4, which holds in a module category. The rest — that
`Tot(M ⊗_R -)` commutes with colimits, because tensoring with a fixed module is a left adjoint
and the total complex is formed degreewise from coproducts — is the shared toolkit of
`StacksFrontier.Homology.KFlat.Flat`, reused here through
`CochainComplex.KFlat.preservesColimit_mapBifunctorObj` and
`CochainComplex.KFlat.preservesColimit_totalFunctor`.

*Split extensions.* A degreewise split short exact sequence of cochain complexes gives a
distinguished triangle in the homotopy category,
`CochainComplex.trianglehOfDegreewiseSplit_distinguished`, and K-flatness is a two-out-of-three
property of distinguished triangles by
`CochainComplex.KFlat.kFlat_two_out_of_three_of_distTriang` (Stacks 06Y2). This is the route the
proof of Stacks 0BYZ takes, which is why it cites 06Y2 and not 0BYH.

*Universes.* Translation and direct sums are stated with the module universe `max u v`
independent of the ring's universe `u`, as `CochainComplex.KFlat` itself is, the index type of
the coproduct lying in the module universe. The split two-out-of-three is stated at `v = u`,
the generality of `CochainComplex.KFlat.kFlat_two_out_of_three_of_distTriang`, whose homotopy
category of `ModuleCat.{u} R` is where the triangle lives.

## References

* [The Stacks Project, Tag 06XZ](https://stacks.math.columbia.edu/tag/06XZ), K-flatness.
* [The Stacks Project, Tag 06Y2](https://stacks.math.columbia.edu/tag/06Y2), two-out-of-three
  for a distinguished triangle.
* [The Stacks Project, Tag 06Y3](https://stacks.math.columbia.edu/tag/06Y3), filtered colimits.
* [The Stacks Project, Tag 0FNG](https://stacks.math.columbia.edu/tag/0FNG), the comparison of
  the total tensor product with the translation.
-/

open CategoryTheory MonoidalCategory Limits

universe u v

namespace CochainComplex

/-- **K-flatness transports along an isomorphism of complexes.** Tensoring with a fixed complex
is a functor, so it carries an isomorphism `K ≅ L` to an isomorphism `Tot(M ⊗_R K) ≅
Tot(M ⊗_R L)`, and acyclicity transports along that. Every closure property below is stated for
one representative of an isomorphism class and reaches the others through this. -/
theorem kFlat_of_iso {R : Type u} [CommRing R]
    {K L : CochainComplex (ModuleCat.{max u v} R) ℤ} (e : K ≅ L) (hK : K.KFlat) : L.KFlat := by
  let _ := ModuleCat.liftedModuleMonoidalStruct.{u, v} (R := R)
  let _ := ModuleCat.liftedModuleMonoidal.{u, v} (R := R)
  intro M hM
  exact HomologicalComplex.Acyclic.of_iso
    (((curriedTensor (ModuleCat.{max u v} R)).map₂CochainComplex.obj M).mapIso e) (hK M hM)

end CochainComplex

namespace CochainComplex.KFlat

/-- **A translate of a K-flat complex is K-flat.** Tensoring with a fixed complex commutes with
the translation (Stacks 0FNG, the `Functor.CommShift` instance of
`Functor.map₂CochainComplex`), and a translate of an acyclic complex is acyclic. -/
theorem kFlat_shift {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ) (hK : K.KFlat) (n : ℤ) :
    (K⟦n⟧).KFlat := by
  let _ := ModuleCat.liftedModuleMonoidalStruct.{u, v} (R := R)
  let _ := ModuleCat.liftedModuleMonoidal.{u, v} (R := R)
  intro M hM
  exact HomologicalComplex.Acyclic.of_iso
    ((((curriedTensor (ModuleCat.{max u v} R)).map₂CochainComplex.obj M).commShiftIso n).app K).symm
    (acyclic_shiftFunctor _ (hK M hM) n)

/-- **A coproduct of K-flat complexes is K-flat.** Tensoring with a fixed complex commutes with
coproducts, and a coproduct of acyclic complexes of modules is acyclic because coproducts are
exact in a module category. -/
theorem kFlat_coproduct {R : Type u} [CommRing R] {ι : Type (max u v)}
    (K : ι → CochainComplex (ModuleCat.{max u v} R) ℤ)
    (hK : ∀ i, (K i).KFlat) : (∐ K).KFlat := by
  let _ := ModuleCat.liftedModuleMonoidalStruct.{u, v} (R := R)
  let _ := ModuleCat.liftedModuleMonoidal.{u, v} (R := R)
  intro M hM
  let D : Discrete ι ⥤ CochainComplex (ModuleCat.{max u v} R) ℤ := Discrete.functor K
  let G := ((curriedTensor (ModuleCat.{max u v} R)).mapBifunctorHomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj M
  let T := HomologicalComplex₂.totalFunctor (ModuleCat.{max u v} R) (ComplexShape.up ℤ)
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)
  let F := G ⋙ T
  have : HasExactColimitsOfShape (Discrete ι) (ModuleCat.{max u v} R) :=
    HasExactColimitsOfShape.domain_of_functor (Discrete ι)
      (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v})
  have : PreservesColimit D F := by
    have (X : ModuleCat.{max u v} R) :
        PreservesColimitsOfShape (Discrete ι) ((curriedTensor (ModuleCat.{max u v} R)).obj X) :=
      (ihom.adjunction X).leftAdjoint_preservesColimits.preservesColimitsOfShape
    have : PreservesColimit D G :=
      preservesColimit_mapBifunctorObj D M (curriedTensor (ModuleCat.{max u v} R))
    let _ : HasColimit (D ⋙ G) :=
      ⟨⟨G.mapCocone (colimit.cocone D), isColimitOfPreserves G (colimit.isColimit D)⟩⟩
    have : PreservesColimit (D ⋙ G) T := preservesColimit_totalFunctor (ComplexShape.up ℤ) (D ⋙ G)
    exact comp_preservesColimit G T
  exact HomologicalComplex.Acyclic.of_iso (preservesColimitIso F D).symm
    (acyclic_colimit (D ⋙ F) (fun j ↦ hK j.as M hM))

/-- **K-flatness is a two-out-of-three property along a degreewise split short exact sequence.**
Unlike `CochainComplex.KFlat.kFlat_two_out_of_three` (Stacks 0BYH) this asks nothing of the
flatness of the terms: a degreewise splitting already exhibits the middle term as the termwise
direct sum of the outer two, and it produces a distinguished triangle in the homotopy category,
where two-out-of-three is Stacks 06Y2. -/
theorem kFlat_two_out_of_three_of_degreewiseSplit {R : Type u} [CommRing R]
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (σ : ∀ n, (S.map
      (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) n)).Splitting) :
    (S.X₂.KFlat → S.X₃.KFlat → S.X₁.KFlat) ∧
      (S.X₁.KFlat → S.X₃.KFlat → S.X₂.KFlat) ∧
      (S.X₁.KFlat → S.X₂.KFlat → S.X₃.KFlat) :=
  kFlat_two_out_of_three_of_distTriang _ _ _
    (CochainComplex.trianglehOfDegreewiseSplit_distinguished S σ)

end CochainComplex.KFlat

end
