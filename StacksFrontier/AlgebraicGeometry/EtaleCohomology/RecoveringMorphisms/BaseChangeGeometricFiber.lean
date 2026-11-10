module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.BaseChangeChartSolutions
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.GeometricFiberSolutions

/-!
# The geometric fibre of the base-changed chart of Stacks 04I6

Step (3) of the proof of [Stacks Project, Tag 04I6] compares `g⁻¹h_V` with `h_{X ×_Y V}` on the
fibre at a geometric point `x̄` of `X`, where `V` is an affine étale chart of an affine `Y` and
`f : X ⟶ Y` is the morphism of schemes chosen in the first paragraph of that proof.  This file
computes the **target** side of that comparison:

the fibre at `x̄` of the sheaf represented by `X ×_Y V` is the set of solutions, in the étale local
ring `𝒪^{ét}_{X,x̄}`, of the system `P` presenting `V` over `Y`, its coefficients pushed along
`Γ(Y, ⊤) --f^♯--> Γ(X, ⊤) --germ--> 𝒪^{ét}_{X,x̄}`.

This is the second of the three identifications which the "Where the rest of Stacks 04I6 is"
section of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/AffineCase.lean` records as
separating step (3) from its conclusion: *the same at `X` for `X ×_Y V`, with coefficient map
`(g^♯)_p`* — the coefficient map here being spelled through `f` rather than through `g^♯`, which
is the same thing because `f` is chosen so that `(B.inclusion.map f).appTop` is
`AlgebraicGeometry.RingedToposHom.globalSectionsMap` of `(g, g^♯)`
(`AlgebraicGeometry.exists_schemeHom_appTop_eq_globalSectionsMap`).

Together with `AlgebraicGeometry.geometricPointFiberEquivEtaleLocalSolutions`, the source side,
this puts both fibres of the comparison in the form
`MvPolynomial.bijective_homOverMap_of_etale` — [Stacks Project, Tag 04GX] — is stated for: the
solutions of one and the same system over two strictly henselian local rings, the coefficients of
the second being those of the first pushed along the ring map between them.

## No base change of the presentation is needed

The system over `Γ(X, ⊤)` used here is `AlgebraicGeometry.baseChangePresentationSystem`, the
coefficientwise image of `P` along `f^♯`.  That is **not** a presentation of anything: the
assertion `Γ(X, ⊤) ⊗_{Γ(Y,⊤)} Γ(V, ⊤) = Γ(X, ⊤)[x]/(P^{f^♯})`, which earlier notes in this
directory recorded as an outstanding prerequisite, is not used.  What is used is only that being
a solution of `P^{f^♯}` over a `Γ(X, ⊤)`-algebra is being a solution of `P` over it regarded as a
`Γ(Y, ⊤)`-algebra, which is `MvPolynomial.isSolution_map_iff`, and the universal property of the
base-changed chart, which is `AlgebraicGeometry.SmallEtale.baseChangeHomEquivSolutions`.

## Main definitions

* `AlgebraicGeometry.baseChangePresentationSystem` — the system `P` with its coefficients pushed
  along `f^♯`.
* `AlgebraicGeometry.baseChangeSiteHomEquivSolutions` — the sections of `h_{X ×_Y V}` over a
  chart `U` of `X`, as the solutions of that system over `Γ(U, ⊤)`.
* `AlgebraicGeometry.baseChangeRepresentableIsoSolutionPresheaf` — the same as an isomorphism of
  presheaves on the small étale site of `X`.

## Main results

* `MvPolynomial.isSolution_map_iff` — pushing the coefficients of a system along a ring map does
  not change its solutions, read over the composite structure map.
* `AlgebraicGeometry.baseChangeHomEquivSolutions_naturality` — the description of the sections of
  `h_{X ×_Y V}` as solutions is natural in the chart `U`.
* `AlgebraicGeometry.baseChangeGeometricPointFiberEquivSolutions` — **the computation**: the lifts
  of a geometric point `x̄` of `X` to `X ×_Y V` are the solutions of `P` in `𝒪^{ét}_{X,x̄}` with
  coefficients pushed along the germ map composed with `f^♯`.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
* [Stacks Project, Tag 04GX](https://stacks.math.columbia.edu/tag/04GX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.SmallEtale Stacks.EtaleCohomology

universe u

namespace MvPolynomial

/-- **Pushing the coefficients of a system of polynomial equations along a ring map does not
change its solutions.**  A tuple in an `R'`-algebra `A` solves the system `P^ψ` obtained from
`P : Fin m → R[x₁, …, x_m]` by applying `ψ : R ⟶ R'` to its coefficients, read over the structure
map `g : R' ⟶ A`, exactly when it solves `P` itself read over the composite `g ∘ ψ`.

This is what makes a base change of the presentation unnecessary in step (3) of the proof of
[Stacks Project, Tag 04I6]: only the solution sets are compared, never the presented rings. -/
theorem isSolution_map_iff {R A : Type u} [CommRing R] [CommRing A] {R' : Type u} [CommRing R']
    {m : ℕ} (P : Fin m → MvPolynomial (Fin m) R) (ψ : R →+* R') (g : R' →+* A)
    (a : Fin m → A) :
    IsSolution (fun j => MvPolynomial.map ψ (P j)) g a ↔ IsSolution P (g.comp ψ) a :=
  forall_congr' fun j => by rw [MvPolynomial.map_map]

end MvPolynomial

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  (V : SmallEtale B Y.obj Y.property)
  [IsAffine Y.obj] [IsAffine ((SmallEtale.toScheme B Y.obj Y.property).obj V)]
  {n : ℕ} {P : Fin n → MvPolynomial (Fin n) Γ(Y.obj, ⊤)}

/-- The system presenting `V` over `Y`, with its coefficients pushed into the global functions on
`X` along the ring map of `f`.

Its solutions over a `Γ(X, ⊤)`-algebra are the solutions of `P` over that algebra regarded as a
`Γ(Y, ⊤)`-algebra, by `MvPolynomial.isSolution_map_iff`; it is not claimed to present
anything. -/
abbrev baseChangePresentationSystem : Fin n → MvPolynomial (Fin n) Γ(X.obj, ⊤) :=
  fun j => MvPolynomial.map (B.inclusion.map f).appTop.hom (P j)

variable (pres : StandardPresentationOver ((SmallEtale.toScheme B Y.obj Y.property).obj V)
    (schemeStructureHom B Y.obj Y.property V) P)

/-- **The description of the sections of `h_{X ×_Y V}` as solutions is natural in the chart.**
For `k : U' ⟶ U` a morphism of the small étale site of `X`, the solution naming the composite
`k ≫ a : U' ⟶ X ×_Y V` is the restriction along `k` of the solution naming `a`, coordinatewise.

Both sides are read off from the morphism of schemes `U ⟶ V` underlying the section, by
`Stacks.EtaleCohomology.homOverEquivSolutions_apply_coe`, and that morphism is precomposed with
`k` — which is `AlgebraicGeometry.SmallEtale.baseChangeHomEquiv_apply_coe` together with the
functoriality of `AlgebraicGeometry.SmallEtale.toScheme`. -/
theorem baseChangeHomEquivSolutions_naturality
    {U U' : SmallEtale B X.obj X.property} (k : U' ⟶ U)
    (a : U ⟶ (smallEtaleBaseChange B f).obj V) (i : Fin n) :
    (SmallEtale.baseChangeHomEquivSolutions B f V U' pres (k ≫ a)).1 i =
      ((SmallEtale.toScheme B X.obj X.property).map k).appTop.hom
        ((SmallEtale.baseChangeHomEquivSolutions B f V U pres a).1 i) := by
  have hcoe : (SmallEtale.baseChangeHomEquiv B f V U' (k ≫ a)).1 =
      (SmallEtale.toScheme B X.obj X.property).map k ≫
        (SmallEtale.baseChangeHomEquiv B f V U a).1 := by
    rw [SmallEtale.baseChangeHomEquiv_apply_coe, SmallEtale.baseChangeHomEquiv_apply_coe,
      Functor.map_comp, Category.assoc]
  change (homOverEquivSolutions _ _ _ _ P pres
      (SmallEtale.baseChangeHomEquiv B f V U' (k ≫ a))).1 i =
    ((SmallEtale.toScheme B X.obj X.property).map k).appTop.hom
      ((homOverEquivSolutions _ _ _ _ P pres (SmallEtale.baseChangeHomEquiv B f V U a)).1 i)
  rw [homOverEquivSolutions_apply_coe, homOverEquivSolutions_apply_coe, hcoe,
    Scheme.Hom.comp_appTop, ← Category.assoc, CommRingCat.hom_comp, RingHom.comp_apply]

/-- **The sections of `h_{X ×_Y V}` over a chart `U` of `X` are the solutions over `Γ(U, ⊤)` of
the pushed system.**  This is
`AlgebraicGeometry.SmallEtale.baseChangeHomEquivSolutions`, whose coefficient map is the structure
map of `U` over `Y`, read as the structure map of `U` over `X` followed by `f^♯`
(`AlgebraicGeometry.SmallEtale.appTop_schemeStructureHom_comp_inclusion_map`) and then absorbed
into the coefficients by `MvPolynomial.isSolution_map_iff`. -/
def baseChangeSiteHomEquivSolutions (U : SmallEtale B X.obj X.property) :
    (U ⟶ (smallEtaleBaseChange B f).obj V) ≃
      Solutions B X.obj X.property (baseChangePresentationSystem B f (P := P)) U :=
  (SmallEtale.baseChangeHomEquivSolutions B f V U pres).trans
    (Equiv.subtypeEquivRight fun a => by
      rw [MvPolynomial.isSolution_map_iff,
        ← SmallEtale.appTop_schemeStructureHom_comp_inclusion_map B f U])

/-- **The representable presheaf of the base-changed chart is the presheaf of solutions of the
pushed system**, on the small étale site of `X`.  This is
`AlgebraicGeometry.baseChangeSiteHomEquivSolutions` assembled over all charts, its naturality
being `AlgebraicGeometry.baseChangeHomEquivSolutions_naturality`. -/
def baseChangeRepresentableIsoSolutionPresheaf :
    ((SmallEtale.topology B X.obj X.property).yoneda.obj
        ((smallEtaleBaseChange B f).obj V)).obj ≅
      solutionPresheaf B X.obj X.property (baseChangePresentationSystem B f (P := P)) :=
  NatIso.ofComponents
    (fun U => (baseChangeSiteHomEquivSolutions B f V pres U.unop).toIso) <| by
    intro U U' k
    apply TypeCat.homEquiv.injective
    funext a
    simp only [TypeCat.homEquiv_apply, types_comp_apply]
    refine Subtype.ext (funext fun i => ?_)
    exact baseChangeHomEquivSolutions_naturality B f V pres k.unop a i

/-- **The lifts of a geometric point of `X` to the base-changed chart `X ×_Y V` are the points of
`V` with values in the étale local ring of `X` at that point.**  For an affine chart `V` of an
affine `Y` with a standard presentation `Γ(V, ⊤) = Γ(Y, ⊤)[x₁, …, x_n]/(P₁, …, P_n)` and a
geometric point `x̄` of `X`, the set of lifts of `x̄` to `X ×_Y V` is the set of solutions of `P`
in `𝒪^{ét}_{X,x̄}`, the coefficients being pushed along `f^♯` followed by the germ map.

This is the second of the three identifications owed by step (3) of the proof of
[Stacks Project, Tag 04I6].  It is
`AlgebraicGeometry.yonedaCompEtaleStalkPresheafFunctorIso` (the stalk of a representable presheaf
is the set of lifts), followed by
`AlgebraicGeometry.baseChangeRepresentableIsoSolutionPresheaf`, followed by
`AlgebraicGeometry.geometricFiberSolutionsEquiv` (the fibre of a presheaf of solutions is the
solution set over the étale local ring), with the coefficients unwound by
`MvPolynomial.isSolution_map_iff`.

Since the étale local ring is strictly henselian
(`AlgebraicGeometry.etaleLocalRing_strictHenselian`), this is the target set of
[Stacks Project, Tag 04GX] in the form `MvPolynomial.bijective_homOverMap_of_etale`. -/
def baseChangeGeometricPointFiberEquivSolutions (x : GeometricPoint X.obj) :
    (geometricPointFiber B X.obj X.property x).obj ((smallEtaleBaseChange B f).obj V) ≃
      {a : Fin n → ↥(etaleLocalRing B X.obj X.property x) //
        MvPolynomial.IsSolution P
          ((etaleCoefficientGerm B X.obj X.property x).comp
            (B.inclusion.map f).appTop.hom) a} :=
  (((yonedaCompEtaleStalkPresheafFunctorIso B X.obj X.property x).app
        ((smallEtaleBaseChange B f).obj V)).toEquiv).symm.trans
    ((((geometricPointSitePoint B X.obj X.property x).presheafFiber.mapIso
        (baseChangeRepresentableIsoSolutionPresheaf B f V pres)).toEquiv).trans
      ((geometricFiberSolutionsEquiv B X.obj X.property x
          (baseChangePresentationSystem B f (P := P))).trans
        (Equiv.subtypeEquivRight fun a => MvPolynomial.isSolution_map_iff P _ _ a)))

end AlgebraicGeometry

end
