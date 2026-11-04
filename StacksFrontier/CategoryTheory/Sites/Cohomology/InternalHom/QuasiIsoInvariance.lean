module

public import Mathlib.Algebra.Homology.Functor
public import StacksFrontier.Algebra.Homology.HomotopyCategory.HomComplexQuasiIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexFunctoriality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionKInjectiveEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionOfModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.QuasiIsomorphismLocality
import StacksCore.Tactic.StacksAttribute

/-! # Well-definedness of the derived internal Hom on a ringed site

Let `(C, O)` be a ringed site, let `l : L' ⟶ L` be a quasi-isomorphism of complexes of
`O`-modules and let `i : I' ⟶ I` be a quasi-isomorphism between K-injective complexes of
`O`-modules. This file proves that the induced morphism of internal Hom complexes

`SheafHom(L, I') ⟶ SheafHom(L', I)`

of `AlgebraicGeometry.RingedSite.homMap` is again a quasi-isomorphism. This is what makes the
derived internal Hom well defined: computing `RHom(L, M)` by choosing a K-injective resolution
of `M` does not depend on the choices.

Quasi-isomorphy of a morphism of complexes of sheaves of modules is detected on the underlying
complexes of presheaves of abelian groups, hence objectwise on the site, and over an object `U`
the morphism is — by the characterisation of the internal Hom complex — pre- and
postcomposition with the restrictions `l|_U` and `i|_U` on the ordinary Hom complex of the
restricted complexes. Restriction to a slice site is exact and preserves K-injectivity
(Stacks 08FI), so the slicewise statement is the algebraic one,
`CochainComplex.HomComplex.homComplexMap_quasiIso`.

The statement is proved over a `AlgebraicGeometry.RingedSite.{c, u, u}` whose underlying
category is essentially `u`-small — objects in an arbitrary universe `c`, morphisms, structure
sheaf and modules in `u` — which covers the small étale site of a scheme, a
`AlgebraicGeometry.RingedSite.{u + 1, u, u}`. At `c = u` the extra hypotheses are all automatic
and the statement is the one about a `AlgebraicGeometry.RingedSite.{u, u, u}`; that
specialisation is recorded as `AlgebraicGeometry.RingedSite.homMap_quasiIso_of_collapsed`.

## Main results

* `AlgebraicGeometry.RingedSite.homMap_quasiIso` (Stacks 0A95).
* `AlgebraicGeometry.RingedSite.homMap_quasiIso_of_collapsed`: the same statement over a ringed
  site whose three universes coincide, where it needs no hypotheses beyond the tag's.

## Implementation notes

Quasi-isomorphy is transported back from presheaves of modules to sheaves of modules through
`PresheafOfModules.sheafification`, which is additive and preserves homology, and whose
composite with the forgetful functor is isomorphic to the identity; this is
`quasiIso_of_sheafification_quasiIso`. Note that this happens in the universe of the *internal
Hom* complex, `max c u`, not in the module universe `u`. The comparison between the internal
Hom complex over `U` and the ordinary Hom complex of the restrictions is the characterising
isomorphism `SheafHomComplex.sectionsIso`, so the morphism is conjugate to the algebraic one and
quasi-isomorphy transfers along an isomorphism of arrows.

Freeing the universe of the objects of the site costs exactly two inputs: the reduction to
presheaves just mentioned, and Stacks 08FI, K-injectivity descending to a slice site, which at
these universes is `Stacks.Cohomology.Localization.isKInjective_over_of_essentiallySmall`.
Everything else in the argument is universe generic.

## References

* [Stacks Project, Tag 0A95](https://stacks.math.columbia.edu/tag/0A95)
* [Stacks Project, Tag 08FI](https://stacks.math.columbia.edu/tag/08FI)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite CochainComplex.HomComplex

universe c u

namespace AlgebraicGeometry.RingedSite

/-- A morphism of complexes of sheaves of modules is a quasi-isomorphism as soon as the induced
morphism of the underlying complexes of presheaves of modules is one: sheafification is
additive, preserves homology, and its composite with the forgetful functor is isomorphic to the
identity.

The universe of the objects of the site, the universe of its morphisms, the universe of the ring
sheaf and the module universe are all free of each other; nothing in the proof uses a
coincidence between them. -/
theorem quasiIso_of_sheafification_quasiIso {D : Type c} [Category.{u} D]
    {K : GrothendieckTopology D} (R : Sheaf K RingCat.{u})
    [HasWeakSheafify K AddCommGrpCat.{max c u}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{max c u}]
    {A B : CochainComplex (SheafOfModules.{max c u} R) ℤ} (f : A ⟶ B)
    (hf : QuasiIso (((SheafOfModules.forget R).mapHomologicalComplex (ComplexShape.up ℤ)).map f)) :
    QuasiIso f := by
  let F := SheafOfModules.forget R
  let G := PresheafOfModules.sheafification (𝟙 R.obj)
  let cc := ComplexShape.up ℤ
  let _ : G.Additive := Functor.additive_of_preserves_binary_products G
  let sf := (G.mapHomologicalComplex cc).map ((F.mapHomologicalComplex cc).map f)
  have hsf : QuasiIso sf :=
    HomologicalComplex.quasiIso_map_of_preservesHomology ((F.mapHomologicalComplex cc).map f) G
  let e : F.mapHomologicalComplex cc ⋙ G.mapHomologicalComplex cc ≅
      𝟭 (CochainComplex (SheafOfModules.{max c u} R) ℤ) :=
    Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) cc ≪≫
      NatIso.mapHomologicalComplex
        (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit) cc ≪≫
      Functor.mapHomologicalComplexIdIso _ cc
  exact quasiIso_of_arrow_mk_iso sf f
    (Arrow.isoMk (e.app A) (e.app B) (by simpa [sf] using (e.hom.naturality f).symm))

variable (X : RingedSite.{c, u, u}) [EssentiallySmall.{u} X.C]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify X.J AddCommGrpCat.{max c u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max c u}]
  {I' I L' L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

omit [HasWeakSheafify X.J AddCommGrpCat.{max c u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max c u}] in
/-- Over an object `U` of the site, the morphism of internal Hom complexes induced by `l` and
`i` is pre- and postcomposition with the restrictions `l|_U` and `i|_U`, hence a
quasi-isomorphism. -/
private theorem quasiIso_sections_homMap (i : I' ⟶ I) [QuasiIso i] [I'.IsKInjective]
    [I.IsKInjective] (l : L' ⟶ L) [QuasiIso l] (U : X.C) :
    QuasiIso (((sheafToPresheaf X.J AddCommGrpCat ⋙
      (evaluation X.Cᵒᵖ AddCommGrpCat).obj (op U)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
          (((SheafOfModules.toSheaf
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
              (ComplexShape.up ℤ)).map (homMap X l i))) := by
  have hPH : (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).PreservesHomology :=
    Stacks.SheafOfModules.preservesHomology_overFunctor U
  have hq : ∀ {A B : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ} (f : A ⟶ B) [QuasiIso f],
      QuasiIso (restrictComplexMap X U f) := fun f _ ↦
    HomologicalComplex.quasiIso_map_of_preservesHomology f (SheafOfModules.overFunctor _ U)
  have hk : ∀ (K : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) [K.IsKInjective],
      (restrictComplex X K U).IsKInjective := fun K _ ↦
    Stacks.Cohomology.Localization.isKInjective_over_of_essentiallySmall X.J
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U K
  have := hq i
  have := hq l
  have := hk I'
  have := hk I
  let α := (sheafHomComplex X L I').sectionsIso U
  let β := (sheafHomComplex X L' I).sectionsIso U
  refine (quasiIso_iff_comp_right _ β.hom).1 ?_
  let lU := restrictComplexMap X U l
  let iU := restrictComplexMap X U i
  have : QuasiIso (homComplexMap lU iU) := homComplexMap_quasiIso lU iU
  have : QuasiIso (α.hom ≫ homComplexMap lU iU) := inferInstance
  convert this using 1
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  ext s
  refine Cochain.ext _ _ fun p q hpq ↦ ?_
  simp only [HomologicalComplex.comp_f, AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply]
  change ((AddCommGrpCat.Hom.hom (β.hom.f n))
    (((homMap X l i).f n).val.app (op U) s)).v p q hpq = _
  rw [sectionsIso_homMap_v X l i U n p q hpq s]
  exact (cochainMap_v lU iU n p q hpq _).symm

/-- **Stacks 0A95.** A quasi-isomorphism `l : L' ⟶ L` and a quasi-isomorphism `i : I' ⟶ I`
between K-injective complexes of `O`-modules induce a quasi-isomorphism
`SheafHom(L, I') ⟶ SheafHom(L', I)` of internal Hom complexes.

This is what makes the derived internal Hom well defined. The objects of the site need not lie
in the universe of its morphisms; at `c = u` the extra size conditions above the tag's are
automatic, which
is `AlgebraicGeometry.RingedSite.homMap_quasiIso_of_collapsed`. -/
@[stacks 0A95]
theorem homMap_quasiIso (i : I' ⟶ I) [QuasiIso i] [I'.IsKInjective] [I.IsKInjective]
    (l : L' ⟶ L) [QuasiIso l] : QuasiIso (homMap X l i) := by
  refine quasiIso_of_sheafification_quasiIso (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    (homMap X l i) ?_
  refine (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
    (PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).1 ?_
  rw [HomologicalComplex.quasiIso_iff_evaluation]
  exact fun U ↦ quasiIso_sections_homMap X i l U.unop

/-- **Stacks 0A95 over a ringed site whose three universes coincide.** The statement of the tag
with no hypotheses beyond it: on a `AlgebraicGeometry.RingedSite.{u, u, u}` every hypothesis
`AlgebraicGeometry.RingedSite.homMap_quasiIso` adds in freeing the universe of the objects is
automatic, the underlying category being `u`-small on the nose. So nothing has been weakened in
freeing them. -/
theorem homMap_quasiIso_of_collapsed (Y : RingedSite.{u, u, u})
    {I₀ I₁ L₀ L₁ :
      CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (i : I₀ ⟶ I₁) [QuasiIso i] [I₀.IsKInjective] [I₁.IsKInjective]
    (l : L₀ ⟶ L₁) [QuasiIso l] : QuasiIso (homMap Y l i) :=
  homMap_quasiIso Y i l

end AlgebraicGeometry.RingedSite

end
