module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAcyclic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedHomotopyCategoryTriangulated
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedQuasiIsomorphisms
public import StacksFrontier.CategoryTheory.Triangulated.Quotient

/-!
# The quasi-isomorphisms of `K(Mod(A, d))` are a saturated multiplicative system

Let `X` be a ringed site and let `A` be a sheaf of differential graded `O`-algebras on it. The
quasi-isomorphisms `Qis` of the homotopy category `K(Mod(A, d))` of right differential graded
`A`-modules are a *saturated multiplicative system compatible with the triangulated structure*:
they satisfy MS1 (identities and composition), MS2 (the two Ore conditions), MS3 (the two
cancellation conditions), MS4 (saturation) and the two compatibility axioms MS5 and MS6 with the
distinguished triangles.

## Main results

* `SheafOfModules.DifferentialGradedModule.quasiIsomorphisms_eq_trW`: an arrow of
  `K(Mod(A, d))` is a quasi-isomorphism exactly when the third vertex of a distinguished
  triangle on it is acyclic.
* `SheafOfModules.DifferentialGradedModule.quasiIsomorphisms_hasLeftCalculusOfFractions`,
  `SheafOfModules.DifferentialGradedModule.quasiIsomorphisms_hasRightCalculusOfFractions`:
  **axioms MS2 and MS3**, a left and a right calculus of fractions.
* `SheafOfModules.DifferentialGradedModule.quasiIsomorphisms_isCompatibleWithTriangulation`:
  **compatibility with the triangulated structure.**
* `SheafOfModules.DifferentialGradedModule.quasiIsomorphisms_isSaturated`: **the
  quasi-isomorphisms are a saturated multiplicative system**, in the sense of
  `CategoryTheory.MorphismProperty.IsSaturated` (Stacks Project Tag 05Q8).

## Implementation notes

The source reduces the lemma to complexes of `O`-modules through the exact functor forgetting
the action of `A`. That reduction is replaced here by the identification of `Qis` with the class
`(acyclic A).trW` of arrows whose cone is acyclic, for the strictly full saturated triangulated
subcategory of acyclic objects of Tag 0FT3: once that identification is available, MS2, MS3, MS5
and MS6 are the general statement about a triangulated subcategory of a triangulated category,
Stacks Project Tag 05RG, and MS4 is the equivalence in that same tag between saturation of the
class of arrows and saturation of the subcategory, whose right-hand side is Tag 0FT3 again.
The homotopy category is triangulated by Tag 0FS7,
`SheafOfModules.DifferentialGradedModule.HomotopyCategory.instIsTriangulated`, which is what
makes all of this available; MS1 and MS4 are also proved directly, in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedDerivedCategory.lean` and
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedQuasiIsomorphisms.lean`.

The identification itself is proved on a distinguished triangle. Such a triangle is isomorphic
to the triangle of an *admissible short exact sequence* `M → N → P` of right differential graded
modules, `SheafOfModules.DifferentialGradedModule.HomotopyCategory.distinguished_iff`, whose
chosen splitting makes `M^• → N^• → P^•` a degreewise split short exact sequence of complexes of
sheaves of `O`-modules,
`SheafOfModules.DifferentialGradedModule.split_shortExact`. For a short exact sequence of
complexes the first arrow is a quasi-isomorphism exactly when the third complex is acyclic,
`SheafOfModules.DifferentialGradedModule.quasiIso_f_iff_acyclic_X₃`, and both sides of the
identification transport along the isomorphism of triangles — the class of quasi-isomorphisms
because it respects isomorphisms of arrows, the acyclic objects because they are strictly full.
So no comparison of the translations of `K(Mod(A, d))` with the shift of complexes *on
morphisms* is needed, and in particular the identification `H^i(f) = H^0(f[i])` that the source
uses is not required.

The hypotheses `HasSheafify X.J AddCommGrpCat.{w}` and
`X.J.WEqualsLocallyBijective AddCommGrpCat.{w}` are what make `SheafOfModules.{w} X.ringSheaf`
abelian, and hence make cohomology of its cochain complexes available; they replace the source's
standing convention that a site admits sheafification. The base is a ringed site, as in the
source, because that is the only setting in which this development has the triangulated
structure on `K(Mod(A, d))`.

## References

* [Stacks Project, Tag 0FT4](https://stacks.math.columbia.edu/tag/0FT4)
* [Stacks Project, Tag 0FT3](https://stacks.math.columbia.edu/tag/0FT3)
* [Stacks Project, Tag 0FS7](https://stacks.math.columbia.edu/tag/0FS7)
* [Stacks Project, Tag 05RG](https://stacks.math.columbia.edu/tag/05RG)
* [Stacks Project, Tag 05Q8](https://stacks.math.columbia.edu/tag/05Q8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v w

namespace SheafOfModules.DifferentialGradedModule

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  (A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The first arrow of a distinguished triangle of the homotopy category of right differential
graded `A`-modules is a quasi-isomorphism exactly when its third vertex is acyclic.

The triangle is isomorphic to the triangle of an admissible short exact sequence `M → N → P`,
whose splitting exhibits `M^• → N^• → P^•` as a short exact sequence of complexes of sheaves of
`O`-modules; for such a sequence the first arrow is a quasi-isomorphism exactly when `P^•` is
acyclic. -/
theorem quasiIsomorphisms_iff_acyclic_obj₃
    (T : Triangle (HomotopyCategory.{u, v, w} A))
    (hT : T ∈ distTriang (HomotopyCategory.{u, v, w} A)) :
    quasiIsomorphisms A T.mor₁ ↔ acyclic.{u, v, w} A T.obj₃ := by
  rw [HomotopyCategory.distinguished_iff] at hT
  obtain ⟨M, N, P, f, g, δ, E, hf, hg, ⟨e⟩, -⟩ := hT
  have h₁ : quasiIsomorphisms A T.mor₁ ↔
      quasiIsomorphisms A ((HomotopyCategory.quotient A).map f) :=
    (quasiIsomorphisms A).arrow_mk_iso_iff
      (Arrow.isoMk (Triangle.π₁.mapIso e) (Triangle.π₂.mapIso e) e.hom.comm₁.symm)
  have h₂ : acyclic.{u, v, w} A T.obj₃ ↔
      acyclic.{u, v, w} A ((HomotopyCategory.quotient A).obj P) :=
    (acyclic.{u, v, w} A).prop_iff_of_iso (Triangle.π₃.mapIso e)
  rw [h₁, h₂, quasiIsomorphisms_quotient_map_iff]
  exact quasiIso_f_iff_acyclic_X₃ (split_shortExact A f g E hf hg)

/-- The quasi-isomorphisms of the homotopy category of right differential graded `A`-modules are
the arrows whose cone is acyclic: the class attached by Stacks Project Tag 05RG to the
triangulated subcategory of acyclic objects of Tag 0FT3. -/
theorem quasiIsomorphisms_eq_trW :
    quasiIsomorphisms A = (acyclic.{u, v, w} A).trW :=
  MorphismProperty.ext _ _ fun _ _ f => by
    obtain ⟨Z, g, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle f
    exact (quasiIsomorphisms_iff_acyclic_obj₃ A _ hT).trans
      (((acyclic.{u, v, w} A).trW_iff_of_distinguished _ hT).symm)

/-- The quasi-isomorphisms are the arrows fitting into a distinguished triangle whose third
vertex is isomorphic to an acyclic object: the hypothesis of Stacks Project Tag 05RG. -/
private theorem quasiIsomorphisms_iff_isoClosure
    ⦃M N : HomotopyCategory.{u, v, w} A⦄ (f : M ⟶ N) :
    quasiIsomorphisms A f ↔ ∃ (Z : HomotopyCategory.{u, v, w} A) (g : N ⟶ Z)
      (h : Z ⟶ M⟦(1 : ℤ)⟧), Triangle.mk f g h ∈ distTriang (HomotopyCategory.{u, v, w} A) ∧
        (acyclic.{u, v, w} A).isoClosure Z := by
  rw [quasiIsomorphisms_eq_trW, ← ObjectProperty.trW_isoClosure]
  exact ⟨fun ⟨Z, g, h, hT, hZ⟩ => ⟨Z, g, h, hT, hZ⟩,
    fun ⟨Z, g, h, hT, hZ⟩ => ⟨Z, g, h, hT, hZ⟩⟩

/-- Stacks Project Tag 05RG for the subcategory of acyclic objects: the quasi-isomorphisms are a
multiplicative system compatible with the triangulated structure, and they are saturated exactly
when the subcategory of acyclic objects is. -/
private theorem quasiIsomorphisms_localization_properties :
    ((quasiIsomorphisms A).HasLeftCalculusOfFractions ∧
        (quasiIsomorphisms A).HasRightCalculusOfFractions ∧
        (quasiIsomorphisms A).IsCompatibleWithTriangulation) ∧
      ((quasiIsomorphisms A).IsSaturated ↔ (acyclic.{u, v, w} A).IsSaturated) :=
  ObjectProperty.hasCalculusOfFractions_isCompatibleWithTriangulation_and_isSaturated_iff
    (acyclic.{u, v, w} A) (quasiIsomorphisms A) (quasiIsomorphisms_iff_isoClosure A)

/-- **Stacks Project, Tag 0FT4.** Axioms MS2 and MS3 for the quasi-isomorphisms of the homotopy
category of right differential graded `A`-modules, in their left form: the left Ore condition
and the left cancellation condition, which together with MS1 are a left calculus of
fractions. -/
@[stacks 0FT4 "axioms MS2 and MS3: the left calculus of fractions"]
instance quasiIsomorphisms_hasLeftCalculusOfFractions :
    (quasiIsomorphisms A).HasLeftCalculusOfFractions :=
  (quasiIsomorphisms_localization_properties.{u, v, w} A).1.1

/-- **Stacks Project, Tag 0FT4.** Axioms MS2 and MS3 for the quasi-isomorphisms of the homotopy
category of right differential graded `A`-modules, in their right form: the right Ore condition
and the right cancellation condition, which together with MS1 are a right calculus of
fractions. -/
@[stacks 0FT4 "axioms MS2 and MS3: the right calculus of fractions"]
instance quasiIsomorphisms_hasRightCalculusOfFractions :
    (quasiIsomorphisms A).HasRightCalculusOfFractions :=
  (quasiIsomorphisms_localization_properties.{u, v, w} A).1.2.1

/-- **Stacks Project, Tag 0FT4.** The quasi-isomorphisms of the homotopy category of right
differential graded `A`-modules are compatible with its triangulated structure: a morphism of
distinguished triangles whose first two components are quasi-isomorphisms may be completed by a
third which is one as well. -/
@[stacks 0FT4 "compatibility with the triangulated structure"]
instance quasiIsomorphisms_isCompatibleWithTriangulation :
    (quasiIsomorphisms A).IsCompatibleWithTriangulation :=
  (quasiIsomorphisms_localization_properties.{u, v, w} A).1.2.2

/-- **Stacks Project, Tag 0FT4.** The quasi-isomorphisms of the homotopy category of right
differential graded `A`-modules are a saturated multiplicative system: MS1, the two Ore
conditions MS2, the two cancellation conditions MS3 and the saturation axiom MS4. Saturation
comes from that of the subcategory of acyclic objects, Stacks Project Tag 0FT3. -/
@[stacks 0FT4 "Qis is a saturated multiplicative system"]
theorem quasiIsomorphisms_isSaturated : (quasiIsomorphisms A).IsSaturated :=
  (quasiIsomorphisms_localization_properties.{u, v, w} A).2.mpr
    (acyclic_isSaturated.{u, v, w} A)

end SheafOfModules.DifferentialGradedModule

end
