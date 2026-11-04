module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.SolutionSheaf
public import StacksFrontier.CategoryTheory.Sites.Topos.PushforwardSectionsRingEquiv

/-!
# The coordinate functions of an étale presentation, carried along a morphism of ringed topoi

This is step (3) of the proof of [Stacks Project, Tag 04I6], by the route its closing paragraph
takes: the comparison between `g⁻¹h_V` and the sheaf represented by `X ×_Y V` is produced by
pushing the *coordinate functions* of a standard presentation of `V` through the structure map of
`(g, g^♯)`, and the equations go along because a ring homomorphism carries a relation to its
image.

Let `(g, g^♯)` be a morphism of the small étale ringed topoi of two schemes `X` and `Y` of a big
étale site, let `V` be an affine étale chart of `Y` with a standard presentation
`Γ(V, ⊤) = Γ(Y, ⊤)[x₁, …, xₙ]/(P₁, …, Pₙ)`, let `U` be an étale chart of `X` and let `s` be a
section of `g⁻¹h_V` over `U`.  The pair `(U, s)` determines a ring homomorphism

`Γ(V, ⊤) ⟶ Γ(U, ⊤)`,

namely `g^♯` at `V` followed by the ring isomorphism
`MorphismOfTopoi.inverseImageYonedaRingEquiv`, which identifies the sections of `g_*𝒪_X` over `V`
with the maps `g⁻¹h_V ⟶ 𝒪_X`, and then evaluation at `s`.  Being a ring homomorphism, it carries
the `n` coordinate functions `xᵢ` to a *solution* of the presented system over `Γ(U, ⊤)`.  That
solution is the value at `(U, s)` of the comparison map which step (3) asks for.

## Main definitions

* `AlgebraicGeometry.comparisonCoord` — the `n` coordinates of the comparison, each a map of
  sheaves `g⁻¹h_V ⟶ 𝒪_X`, obtained by transporting `g^♯(xᵢ)` across the ring isomorphism.
* `AlgebraicGeometry.comparisonRingHom` — for a chart `U` of `X` and a section `s` of `g⁻¹h_V`
  over `U`, the induced ring homomorphism `Γ(V, ⊤) ⟶ Γ(U, ⊤)`.

## Main results

* `AlgebraicGeometry.isSolution_comparisonCoord` — **the equations of the presentation survive**:
  the values of the `n` coordinates at `(U, s)` solve the system `P` over `Γ(U, ⊤)`, with the
  coefficients pushed along `AlgebraicGeometry.comparisonRingHom` composed with the structure map
  of `V`.
* `AlgebraicGeometry.comparisonRingHom_presCoord` — the value of the `i`-th coordinate at
  `(U, s)` is the image of `xᵢ` under that ring homomorphism, so the solution is literally the
  tuple of coordinate functions pushed through `g^♯`.

## What this does not do

The coefficient ring map of `AlgebraicGeometry.isSolution_comparisonCoord` is
`comparisonRingHom U s` composed with the structure map `Γ(Y, ⊤) ⟶ Γ(V, ⊤)` of the chart `V`.
To read the resulting solution as a point of `X ×_Y V` over `U` — which is what identifies the
comparison's target with the representable sheaf `h_{X ×_Y V}` and so completes step (3) — that
coefficient map has still to be identified with

`Γ(Y, ⊤) --φ--> Γ(X, ⊤) --restrict--> Γ(U, ⊤)`,

where `φ` is `AlgebraicGeometry.RingedToposHom.globalSectionsMap`, the ring map of the source's
first paragraph.  That identification is *not* carried out in this file, but it is **proved**, in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/ComparisonCoefficients.lean`:
`AlgebraicGeometry.comparisonRingHom_comp_appTop_schemeStructureHom` is the equality of ring
homomorphisms and `AlgebraicGeometry.isSolution_comparisonCoord_globalSectionsMap` is
`AlgebraicGeometry.isSolution_comparisonCoord` restated with the identified coefficient map.  It
is housed there rather than here because its content —
`MorphismOfTopoi.sectionsEvalRingHom_inverseImageYonedaRingEquiv_symm_map_from_terminal`, that a
*global* section of `g_*𝒪_X` restricted to `V` and transported across
`MorphismOfTopoi.inverseImageYonedaRingEquiv` is the *constant* generalized element of the global
function on `X` — is a statement about an arbitrary morphism of topoi, and because the identity
`hT.from U` of the small étale site needs
`AlgebraicGeometry.SmallEtale.toScheme_map_from_final`, which this file does not import.

Nothing here carries a `@[stacks 04I6]` tag.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open Stacks.Sheaves.ToposPullback Stacks.EtaleCohomology AlgebraicGeometry.SmallEtale

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X Y : Scheme.{u}} (hX : B.Contains X) (hY : B.Contains Y)
  (g : RingedToposHom
    (RingedSite.toRingedTopos (smallEtaleRingedSite B X hX))
    (RingedSite.toRingedTopos (smallEtaleRingedSite B Y hY)))

section Coordinates

variable [IsAffine Y] {n : ℕ} {P : Fin n → MvPolynomial (Fin n) Γ(Y, ⊤)}
  (V : SmallEtale B Y hY) [IsAffine ((SmallEtale.toScheme B Y hY).obj V)]
  (pres : StandardPresentationOver ((SmallEtale.toScheme B Y hY).obj V)
    (schemeStructureHom B Y hY V) P)

/-- The `i`-th coordinate function of a standard presentation, as a global function on the chart
it presents: the image of `xᵢ` under the identification `Γ(V, ⊤) ≅ Γ(Y, ⊤)[x]/(P)`. -/
def presCoord (i : Fin n) : Γ((SmallEtale.toScheme B Y hY).obj V, ⊤) :=
  pres.iso.inv.hom (Ideal.Quotient.mk (Ideal.span (Set.range P)) (MvPolynomial.X i))

/-- **The coordinate functions of a standard presentation solve the presented system.**  This is
`Stacks.EtaleCohomology.homOverEquivSolutions` read at the identity morphism of the chart: the
`Y`-morphism `𝟙_V` is named by the tuple of coordinate functions. -/
theorem isSolution_presCoord :
    MvPolynomial.IsSolution P (schemeStructureHom B Y hY V).appTop.hom
      (presCoord B hY V pres) :=
  have h := (homOverEquivSolutions ((SmallEtale.toScheme B Y hY).obj V)
    ((SmallEtale.toScheme B Y hY).obj V) (schemeStructureHom B Y hY V)
    (schemeStructureHom B Y hY V) P pres ⟨CategoryStruct.id _, Category.id_comp _⟩).2
  by
    refine (funext fun i => ?_ : _ = presCoord B hY V pres) ▸ h
    rw [homOverEquivSolutions_apply_coe, presCoord, Scheme.Hom.id_appTop, Category.comp_id]

end Coordinates

section Comparison

variable [IsAffine Y] {n : ℕ} {P : Fin n → MvPolynomial (Fin n) Γ(Y, ⊤)}
  (V : SmallEtale B Y hY) [IsAffine ((SmallEtale.toScheme B Y hY).obj V)]
  (pres : StandardPresentationOver ((SmallEtale.toScheme B Y hY).obj V)
    (schemeStructureHom B Y hY V) P)

/-- The sheaf of rings `𝒪_X` of the small étale site of `X`, with commutativity forgotten: the
coefficient sheaf of the generalized-element calculus below. -/
abbrev smallEtaleRingSheaf : Sheaf (SmallEtale.topology B X hX) RingCat.{u} :=
  (sheafCompose (SmallEtale.topology B X hX) (forget₂ CommRingCat.{u} RingCat.{u})).obj
    (SmallEtale.commRingStructureSheaf B X hX)

/-- **The sections of `g_*𝒪_X` over an étale chart `V` of `Y` are the maps `g⁻¹h_V ⟶ 𝒪_X`, as
rings.**  This is `MorphismOfTopoi.inverseImageYonedaRingEquiv` at the small étale ringed topoi,
and it is the identification which the closing paragraph of the proof of
[Stacks Project, Tag 04I6] uses to read a section of `g_*𝒪_X` as a function on `g⁻¹h_V`. -/
abbrev inverseImageHomRingEquiv :
    (g.toToposHom.inverseImage.obj ((SmallEtale.topology B Y hY).yoneda.obj V) ⟶
        ringSheaf (smallEtaleRingSheaf B hX)) ≃+*
      (sectionsFunctor (SmallEtale.topology B Y hY) (op V)).obj
        (ringSheaf (pullbackRingSheaf (SmallEtale.topology B Y hY)
          g.toToposHom.pushforward (smallEtaleRingSheaf B hX))) :=
  MorphismOfTopoi.inverseImageYonedaRingEquiv g.toToposHom (smallEtaleRingSheaf B hX) V

/-- **The `i`-th coordinate of the comparison of step (3) of Stacks 04I6.**  The structure map
`g^♯` sends the `i`-th coordinate function `xᵢ ∈ Γ(V, ⊤)` of the presentation to a section of
`g_*𝒪_X` over `V`, and `AlgebraicGeometry.inverseImageHomRingEquiv` reads that section as a map
of sheaves `g⁻¹h_V ⟶ 𝒪_X`.

These `n` maps are the comparison, in coordinates: no product `(𝒪_X)ⁿ` is formed, and the
equations of the presentation hold for them by
`AlgebraicGeometry.isSolution_comparisonCoord`. -/
def comparisonCoord (i : Fin n) :
    g.toToposHom.inverseImage.obj ((SmallEtale.topology B Y hY).yoneda.obj V) ⟶
      ringSheaf (smallEtaleRingSheaf B hX) :=
  (inverseImageHomRingEquiv B hX hY g V).symm
    ((g.fSharp.hom.app (op V)).hom (presCoord B hY V pres i))

/-- **The ring homomorphism `Γ(V, ⊤) ⟶ Γ(U, ⊤)` which the comparison induces at a section.**
For an étale chart `U` of `X` and a section `s` of `g⁻¹h_V` over `U`, this is `g^♯` at `V`,
followed by the ring isomorphism `AlgebraicGeometry.inverseImageHomRingEquiv` reading a section of
`g_*𝒪_X` as a map out of `g⁻¹h_V`, followed by evaluation at `s`.

It is a *ring* homomorphism, and that is the whole content of step (3) of the proof of
[Stacks Project, Tag 04I6]: a relation holding among the coordinate functions in `Γ(V, ⊤)` holds
among their images. -/
def comparisonRingHom (U : (SmallEtale B X hX)ᵒᵖ)
    (s : (sectionsFunctor (SmallEtale.topology B X hX) U).obj
      (g.toToposHom.inverseImage.obj ((SmallEtale.topology B Y hY).yoneda.obj V))) :
    Γ((SmallEtale.toScheme B Y hY).obj V, ⊤) →+*
      Γ((SmallEtale.toScheme B X hX).obj U.unop, ⊤) :=
  ((sectionsEvalRingHom U s).comp
      (inverseImageHomRingEquiv B hX hY g V).symm.toRingHom).comp
    (g.fSharp.hom.app (op V)).hom

omit [IsAffine Y] [IsAffine ((toScheme B Y hY).obj V)] in
/-- The value at `(U, s)` of the `i`-th coordinate of the comparison is the image of the `i`-th
coordinate function of the presentation under
`AlgebraicGeometry.comparisonRingHom`. -/
theorem comparisonRingHom_presCoord (U : (SmallEtale B X hX)ᵒᵖ)
    (s : (sectionsFunctor (SmallEtale.topology B X hX) U).obj
      (g.toToposHom.inverseImage.obj ((SmallEtale.topology B Y hY).yoneda.obj V)))
    (i : Fin n) :
    comparisonRingHom B hX hY g V U s (presCoord B hY V pres i) =
      (sectionsFunctor (SmallEtale.topology B X hX) U).map
        (comparisonCoord B hX hY g V pres i) s :=
  rfl

/-- **The equations of the presentation survive the comparison.**  At every étale chart `U` of
`X` and every section `s` of `g⁻¹h_V` over `U`, the values of the `n` coordinates of the
comparison form a solution of the system `P` over `Γ(U, ⊤)`, the coefficients being pushed along
`AlgebraicGeometry.comparisonRingHom` composed with the structure map of the chart `V`.

This is the source's closing argument: the coordinate functions solve the system in `Γ(V, ⊤)` by
`AlgebraicGeometry.isSolution_presCoord`, and `AlgebraicGeometry.comparisonRingHom` is a ring
homomorphism, so `MvPolynomial.isSolution_comp` applies.  No left exactness of `g⁻¹`, no product
`(𝒪_X)ⁿ` and no limit diagram is used: the only input beyond the presentation is that the
identification of the sections of `g_*𝒪_X` over `V` with the maps `g⁻¹h_V ⟶ 𝒪_X` is one of
rings. -/
theorem isSolution_comparisonCoord (U : (SmallEtale B X hX)ᵒᵖ)
    (s : (sectionsFunctor (SmallEtale.topology B X hX) U).obj
      (g.toToposHom.inverseImage.obj ((SmallEtale.topology B Y hY).yoneda.obj V))) :
    MvPolynomial.IsSolution P
      ((comparisonRingHom B hX hY g V U s).comp
        (schemeStructureHom B Y hY V).appTop.hom)
      (fun i => (sectionsFunctor (SmallEtale.topology B X hX) U).map
        (comparisonCoord B hX hY g V pres i) s) :=
  MvPolynomial.isSolution_comp (P := P) (schemeStructureHom B Y hY V).appTop.hom
    (comparisonRingHom B hX hY g V U s) (isSolution_presCoord B hY V pres)

end Comparison

end AlgebraicGeometry

end
