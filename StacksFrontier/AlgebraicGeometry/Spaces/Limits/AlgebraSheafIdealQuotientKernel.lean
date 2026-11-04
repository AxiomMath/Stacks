module

public import StacksFrontier.CategoryTheory.Sites.Modules.IdealSubsheafLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AlgebraSheafIdealQuotientLift

/-!
# The kernel of the quotient of a sheaf of rings by a sheaf of ideals

`Stacks.Sites.quotientRingSheaf` divides a sheaf of commutative rings by a sheaf of ideals by
sheafifying the objectwise quotient, so the sections of `O/I` over an object of the site are not
`O(X)/I(X)` and nothing about them is visible by inspection.  **This file shows that the quotient
map `O ⟶ O/I` nevertheless kills exactly the sections of `I`**, so that `O/I` is a quotient by
`I` and not by something larger.

At the level of algebraic spaces this completes
`AlgebraicGeometry.Space.AlgebraSheaf.le_kerIdeal_toIdealQuotient`, which gives only the easy
inclusion, to the equality
`AlgebraicGeometry.Space.AlgebraSheaf.kerIdeal_toIdealQuotient`.

## Main results

* `Stacks.Sites.mem_of_toQuotientRingSheaf_app_eq_zero` and
  `Stacks.Sites.toQuotientRingSheaf_app_eq_zero_iff`: **a section of `O` is killed by
  `O ⟶ O/I` exactly when it lies in `I`.**
* `AlgebraicGeometry.Space.AlgebraSheaf.kerIdeal_toIdealQuotient`: **the kernel ideal of the
  quotient morphism `A ⟶ A/I` of algebra sheaves on an algebraic space is exactly `I`**, and
  `...toIdealQuotient_app_eq_zero_iff` is the sectionwise form.

## Implementation notes

### No cohomology, and no sections of a sheafification

The proof uses neither.  The quotient map is the objectwise class map
`Stacks.Sites.toQuotientPresheaf` followed by `CategoryTheory.toSheafify`, and `toSheafify` is
*locally injective* — `CategoryTheory.Presheaf.isLocallyInjective_toSheafify'`, available because
the local equivalences of presheaves of commutative rings on the site are the locally bijective
morphisms (`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective`).  So a section of `O`
whose class dies in `O/I` has a class dying in the *objectwise* quotient along every arrow of some
covering sieve, which says exactly that it restricts into `I` along every arrow of that sieve.
Membership in a sheaf of ideals is local — that is the `isSheaf` field of
`SheafOfModules.Submodule`, in the form used by
`Stacks.SheafOfModules.mem_of_sieveOfSection_mem` — so the section lies in `I` over the object
itself.

In particular no hypothesis is put on `I` beyond being a sheaf of ideals: it need not be
quasi-coherent, of finite type, or anything else, and the site is arbitrary.

### What this is a step towards

Quasi-coherence and finite presentation of `A/I` are not addressed here, and this lemma is not
enough for them on its own.  What it supplies is the **exactness** of the complex
`I ⟶ A ⟶ A/I`, which is what identifies the underlying module of `A/I` with the **cokernel** of
the inclusion of `I` into the underlying module of `A`; that identification is
`AlgebraicGeometry.Space.AlgebraSheaf.underlyingModuleIdealQuotientCokernelIso` in
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.AlgebraSheafIdealQuotientCokernel`, an epi-mono
factorisation argument in the balanced abelian category `AlgebraicGeometry.Space.Modules`
following the template `AlgebraicGeometry.Space.AlgebraSheaf.underlyingModuleImageIso`.  With it
`AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_unconditional` gives quasi-coherence of
`A/I` from quasi-coherence of `A` and of `I`, and
`AlgebraicGeometry.Space.surjective_val_app_of_epi_of_isQuasicoherentOnSite` turns the local
surjectivity of `A ⟶ A/I` into surjectivity on the sections over an affine étale chart, which
together with the result below identifies those sections with `A(U)/I(U)`.  The present lemma is
the kernel half of that identification.

## References

* [Stacks Project, Tag 082A](https://stacks.math.columbia.edu/tag/082A)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₁ u₁ u

namespace Stacks.Sites

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [HasWeakSheafify J CommRingCat.{u}] [J.WEqualsLocallyBijective CommRingCat.{u}]
    {O : Sheaf J CommRingCat.{u}}

/-- **A section of `O` killed by the quotient map `O ⟶ O/I` already lies in `I`.**

The quotient map is the objectwise class map followed by the comparison with the sheafification,
and the comparison is *locally injective*, so a section whose class dies in `O/I` has a class
dying in the objectwise quotient along every arrow of some covering sieve — that is, it restricts
into `I` along every arrow of a covering sieve.  Membership in a sheaf of ideals is local, so the
section lies in `I` over the object itself.

Together with `Stacks.Sites.toQuotientPresheaf_app_surjective` this says that `O ⟶ O/I` has
kernel exactly `I` on the sections over every object of the site, with no hypothesis on `I`
beyond being a sheaf of ideals and no cohomology. -/
theorem mem_of_toQuotientRingSheaf_app_eq_zero (I : IdealSubsheaf O) (X : Cᵒᵖ)
    (a : O.obj.obj X) (ha : ((toQuotientRingSheaf I).hom.app X).hom a = 0) :
    a ∈ I.obj X := by
  have hz : ((toSheafify J (quotientPresheaf I)).app X).hom
        ((toQuotientPresheaf I).app X a) =
      ((toSheafify J (quotientPresheaf I)).app X).hom 0 := by
    rw [map_zero]
    exact ha
  have hsieve := Presheaf.equalizerSieve_mem J (toSheafify J (quotientPresheaf I))
    ((toQuotientPresheaf I).app X a) 0 hz
  refine I.isSheaf a (J.superset_covering ?_ hsieve)
  intro Y g hg
  have hg' : (quotientPresheaf I).map g.op ((toQuotientPresheaf I).app X a) =
      (quotientPresheaf I).map g.op 0 := hg
  have hmem : O.obj.map g.op a ∈ sectionIdeal I (op Y) := by
    refine Ideal.Quotient.eq_zero_iff_mem.1 ?_
    refine Eq.trans ?_ (map_zero ((quotientPresheaf I).map g.op).hom)
    exact hg'
  exact hmem

/-- **The quotient map `O ⟶ O/I` kills exactly the sections of `I`.** -/
theorem toQuotientRingSheaf_app_eq_zero_iff (I : IdealSubsheaf O) (X : Cᵒᵖ)
    (a : O.obj.obj X) :
    ((toQuotientRingSheaf I).hom.app X).hom a = 0 ↔ a ∈ I.obj X := by
  refine ⟨mem_of_toQuotientRingSheaf_app_eq_zero I X a, fun ha => ?_⟩
  have h0 : ((toQuotientPresheaf I).app X).hom a = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 ha
  show ((toSheafify J (quotientPresheaf I)).app X).hom
    (((toQuotientPresheaf I).app X).hom a) = 0
  rw [h0, map_zero]

end Stacks.Sites

namespace AlgebraicGeometry.Space.AlgebraSheaf

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- **The kernel ideal of the quotient morphism `A ⟶ A/I` is exactly `I`.**

One inclusion is `AlgebraicGeometry.Space.AlgebraSheaf.le_kerIdeal_toIdealQuotient`; the other is
`Stacks.Sites.mem_of_toQuotientRingSheaf_app_eq_zero`, local injectivity of the comparison with
the sheafification together with locality of membership in a sheaf of ideals.

So the quotient of an algebra sheaf on an algebraic space by a sheaf of ideals is a quotient *by
that ideal* and not by a larger one, even though its sections over a chart are the sections of a
sheafification and not the objectwise quotient. -/
theorem kerIdeal_toIdealQuotient (A : AlgebraSheaf.{u, u} B S hS F hF) (I : A.IdealSheaf) :
    kerIdeal (A.toIdealQuotient I) = I :=
  le_antisymm
    (SheafOfModules.Submodule.le_iff.2 fun U a ha =>
      Stacks.Sites.mem_of_toQuotientRingSheaf_app_eq_zero.{u, u + 1, u} I U a
        ((mem_kerIdeal (A.toIdealQuotient I) U a).1 ha))
    (le_kerIdeal_toIdealQuotient A I)

/-- **A section of `A` is killed by the quotient morphism `A ⟶ A/I` exactly when it lies in
`I`.** -/
theorem toIdealQuotient_app_eq_zero_iff (A : AlgebraSheaf.{u, u} B S hS F hF) (I : A.IdealSheaf)
    (U : (SmallEtale B S hS F)ᵒᵖ) (a : A.right.obj.obj U) :
    ((A.toIdealQuotient I).right.hom.app U).hom a = 0 ↔ a ∈ I.obj U :=
  Stacks.Sites.toQuotientRingSheaf_app_eq_zero_iff.{u, u + 1, u} I U a

end AlgebraicGeometry.Space.AlgebraSheaf

end
