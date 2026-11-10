module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOnARingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.BoundedAboveFlatComplexes
public import StacksFrontier.CategoryTheory.Sites.Modules.Gate18b.FlatRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFinite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
import StacksCore.Tactic.StacksAttribute

/-!
# Restriction to a slice site carries K-flat resolutions to K-flat resolutions

Let `(C, O)` be a ringed site and `U` an object of `C`.  Restriction of sheaves of modules to
the localized site `C/U` is exact, so it preserves quasi-isomorphisms; this file shows that it
also preserves the two properties that make the resolution of Stacks 06YS usable for the
derived pullback, namely K-flatness and flatness of the terms.

K-flatness itself is **not** a property that transports along a functor: it quantifies over all
acyclic complexes of modules on the site, and the acyclic complexes on `C/U` are not the
restrictions of the acyclic complexes on `C`.  What transports is the *presentation* of the
resolution produced by Stacks 06YS, recorded in
`Stacks.SheafOfModules.KFlatResolution.exists_resolution_colimit`: a sequential colimit of
bounded above complexes of flat modules.  Restriction preserves each clause of that
presentation — it is a left adjoint, so it commutes with the colimit; it is additive, so it
preserves the bound; and it preserves flatness by Stacks 0E8J — and a sequential colimit of
bounded above complexes of flat modules is K-flat by Stacks 06YQ.  This is the same argument
by which the *pullback* of the resolution of 06YS is K-flat, Stacks 0G7E.

What this buys downstream is a single resolution good on both sides of a localization: for a
complex `G` of `O`-modules, a K-flat resolution with flat terms whose restriction to `C/U` is
again K-flat with flat terms, which is
`Stacks.SheafOfModules.KFlatRestriction.exists_kFlatResolution_restriction` below.  That is
what makes the canonical comparison `L f^* ⟶ f^*` of Stacks 06YY invertible simultaneously on
`C` and on `C/U`, hence what lets the derived pullback be computed after restricting to a
slice.

## Main results

* `Stacks.SheafOfModules.KFlatRestriction.isFlat_restriction`: **Stacks 0E8J**, restated at the
  spelling of the tensor product so that it can feed the K-flatness criteria.
* `Stacks.SheafOfModules.KFlatRestriction.kFlat_restriction_of_isColimit`: the restriction of a
  sequential colimit of bounded above complexes of flat modules is K-flat.
* `Stacks.SheafOfModules.KFlatRestriction.exists_kFlatResolution_restriction`: **the usable
  form.** Every complex of `O`-modules receives a termwise surjective quasi-isomorphism from a
  K-flat complex with flat terms whose restriction to `C/U` is again K-flat with flat terms; no
  binary products are assumed on the site.
* `Stacks.SheafOfModules.KFlatRestriction.preservesColimitsOfShape_restriction_of_cocontinuous`
  and `Stacks.SheafOfModules.KFlatRestriction.kFlat_restriction_of_isColimit_of_cocontinuous`:
  the same engine **without binary products on the site**. The class was needed only to know
  that restriction preserves sequential colimits, through the instance making it a left adjoint;
  restriction is also the pushforward along `Over.forget U`, which is continuous and
  cocontinuous, and colimit preservation for such a pushforward needs no products.
* `Stacks.SheafOfModules.KFlatRestriction.exists_kFlatResolution_restriction_forall`: **one
  resolution whose restriction to every slice is K-flat.** The colimit presentation does not
  mention the object localized at, so a single resolution serves every object at once; this is
  the form a statement checked on a covering family needs, and it carries no binary products.

## Implementation notes

The two ring sheaves that have to agree for the statements to elaborate — the sheaf of rings
`(Stacks.SheafOfModules.Tensor.ringSheaf O).over U` over which the restricted modules live, and
the sheaf of rings `Stacks.SheafOfModules.Tensor.ringSheaf (O.over U)` over which the tensor
product of the localized site is taken — are equal by `rfl`: restricting along
`(Over.forget U)ᵒᵖ` and forgetting commutativity are both precomposition-type operations and
commute on the nose.  So no comparison isomorphism appears anywhere below, and `restriction` is
named without a type ascription, so that every instance registered for
`SheafOfModules.overFunctor` is found for it: retyping it at the second spelling would hide
those instances from synthesis, which does not unfold a declared type.

Colimit preservation is needed for sequential, not finite, colimits, so it cannot come from
exactness. `preservesColimitsOfShape_restriction` takes it from the adjunction
`j_U^{-1} ⊣ j_{U,*}`, i.e. from the `Functor.IsLeftAdjoint` instance on
`SheafOfModules.overFunctor`, which is where `CategoryTheory.Limits.HasBinaryProducts` on the
site comes from (`j_{U,*}` is built out of the products with `U`).
`preservesColimitsOfShape_restriction_of_cocontinuous` takes it instead from restriction being
the pushforward along the continuous and cocontinuous functor `Over.forget U`, which needs no
products, and the resolutions below are built on that version.

## References

* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 0E8J](https://stacks.math.columbia.edu/tag/0E8J)
* [Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Stacks.SheafOfModules.KFlatRestriction

variable {C : Type u} [SmallCategory.{u} C] [Limits.HasBinaryProducts C]
  {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (R : Sheaf J CommRingCat.{u}) (U : C)
  [HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Restriction of sheaves of `O`-modules to the site localized at `U`.  It is named here
only so that the statements below can be read; its type is the one
`SheafOfModules.overFunctor` declares, so every instance registered for the latter applies to
it. -/
noncomputable abbrev restriction :=
  SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) U

/-- Restriction of complexes of sheaves of `O`-modules to the site localized at `U`, with its
target spelled over `Stacks.SheafOfModules.Tensor.ringSheaf (O|_U)`, the sheaf of rings the
tensor product of the localized site is taken over.  That spelling is equal by `rfl` to the one
`SheafOfModules.overFunctor` declares, but only the former lets the K-flatness criteria find
their instances; see the module docstring. -/
noncomputable abbrev restrictionComplexFunctor :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ ⥤
      CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (R.over U))) ℤ :=
  (restriction R U).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The restriction of a single complex, read at the same spelling. -/
noncomputable abbrev restrictionComplex
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R))
      ℤ) :
    CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (R.over U))) ℤ :=
  (restrictionComplexFunctor R U).obj K

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Restriction to the localized site preserves sequential colimits: it is a left adjoint, the
localization `j_U^{-1}` of a morphism of topoi. -/
theorem preservesColimitsOfShape_restriction :
    PreservesColimitsOfShape ℕ (restriction R U) :=
  have h : PreservesColimitsOfSize.{0, 0} (restriction R U) :=
    (Adjunction.ofIsLeftAdjoint (restriction R U)).leftAdjoint_preservesColimits
  h.preservesColimitsOfShape

omit [Limits.HasBinaryProducts C] in
/-- The restriction of a flat sheaf of `O`-modules to the site localized at `U` is a flat sheaf
of `O|_U`-modules, stated at the ring-sheaf spelling the tensor product uses.

This is a restatement of `Stacks.SheafOfModules.FlatRestriction.isFlat_over`, which carries the
Stacks tag, and it deliberately carries no attribute of its own: that tag makes a single
assertion about restriction to an object of a ringed site, the assertion is already covered,
and a second carrier of one assertion is a duplicate rather than part of a covering set. Only
the spelling differs. -/
theorem isFlat_restriction
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R))
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) F) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R.over U)
      ((restriction R U).obj F) :=
  Stacks.SheafOfModules.FlatRestriction.isFlat_over { C := C, J := J, O := R } U F hF

omit [Limits.HasBinaryProducts C] [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Restriction to the localized site preserves the bound of a strictly bounded above complex:
it is additive, so it carries a zero object to a zero object. -/
theorem isStrictlyLE_restriction
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R))
      ℤ) (b : ℤ) [K.IsStrictlyLE b] :
    CochainComplex.IsStrictlyLE (restrictionComplex R U K) b := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact (restriction R U).map_isZero (K.isZero_of_isStrictlyLE b i hi)

omit [Limits.HasBinaryProducts C] in
/-- **The restriction of a bounded above complex of flat modules is K-flat**, by Stacks 06YQ on
the localized site: restriction preserves the bound and, by Stacks 0E8J, the flatness of the
terms. -/
theorem kFlat_restriction_of_isStrictlyLE
    (L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R))
      ℤ) (b : ℤ) [L.IsStrictlyLE b]
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) (L.X i)) :
    CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (R.over U))
      (restrictionComplex R U L) := by
  have := isStrictlyLE_restriction R U L b
  refine CochainComplex.KFlatBifunctor.kFlat_of_isStrictlyLE _ _ b
    (Stacks.SheafOfModules.KFlatResolution.hF_sheafTensor (R.over U))
    (Stacks.SheafOfModules.KFlatResolution.hexact_sheafOfModules (R.over U)) fun q ↦ ?_
  exact Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat (R.over U) _
    (isFlat_restriction R U _ (hflat q)) q

/-- **The engine.** The restriction of a sequential colimit of bounded above complexes of flat
`O`-modules is K-flat: restriction commutes with the colimit degreewise, and each stage
restricts to a bounded above complex of flat `O|_U`-modules. -/
theorem kFlat_restriction_of_isColimit
    (Dg : ℕ ⥤ CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ)
    (c : Cocone Dg) (hc : IsColimit c)
    (hLE : ∀ n : ℕ, ∃ b : ℤ, (Dg.obj n).IsStrictlyLE b)
    (hflat : ∀ (n : ℕ) (i : ℤ), AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R)
      ((Dg.obj n).X i)) :
    CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (R.over U))
      (restrictionComplex R U c.pt) := by
  have := preservesColimitsOfShape_restriction R U
  have hp := CochainComplex.KFlat.preservesColimit_mapHomologicalComplex Dg (restriction R U)
  refine CochainComplex.KFlatBifunctor.kFlat_of_isColimit
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (R.over U))
    ((restrictionComplexFunctor R U).mapCocone c) (hp.preserves hc).some
    (Stacks.SheafOfModules.KFlatResolution.hF_sheafTensor (R.over U))
    (Stacks.SheafOfModules.KFlatResolution.hexact_sheafOfModules (R.over U)) fun n ↦ ?_
  obtain ⟨b, hb⟩ := hLE n
  have := hb
  exact kFlat_restriction_of_isStrictlyLE R U (Dg.obj n) b (hflat n)

omit [Limits.HasBinaryProducts C] in
/-- **Restriction to the localized site preserves sequential colimits, without assuming binary
products on the site.** `preservesColimitsOfShape_restriction` obtains this from restriction
being a left adjoint, and the instance supplying that is available only on a site with binary
products. Restriction is also the pushforward of sheaves of modules along `Over.forget U`, which
is continuous and cocontinuous, and colimit preservation for such a pushforward —
`Stacks.SheafOfModules.pushforward_preservesColimits` — asks only for the sheafification data of
the two topologies. Nothing else in the K-flatness of a restricted resolution needs the class,
so this is what removes it. -/
theorem preservesColimitsOfShape_restriction_of_cocontinuous :
    PreservesColimitsOfShape ℕ (restriction R U) :=
  have _h : PreservesColimitsOfSize.{u, u} (restriction R U) :=
    Stacks.SheafOfModules.pushforward_preservesColimits (J := J.over U) (K := J)
      (Over.forget U) (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R).over U))
  have h0 : PreservesColimitsOfSize.{0, 0} (restriction R U) :=
    preservesColimitsOfSize_shrink _
  h0.preservesColimitsOfShape

omit [Limits.HasBinaryProducts C] in
/-- **The engine, without binary products on the site.** The restriction of a sequential colimit
of bounded above complexes of flat `O`-modules is K-flat. This is
`kFlat_restriction_of_isColimit` with its one use of binary products replaced by
`preservesColimitsOfShape_restriction_of_cocontinuous`; every other step already carried
`omit [Limits.HasBinaryProducts C]`. -/
theorem kFlat_restriction_of_isColimit_of_cocontinuous
    (Dg : ℕ ⥤ CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ)
    (c : Cocone Dg) (hc : IsColimit c)
    (hLE : ∀ n : ℕ, ∃ b : ℤ, (Dg.obj n).IsStrictlyLE b)
    (hflat : ∀ (n : ℕ) (i : ℤ), AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R)
      ((Dg.obj n).X i)) :
    CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (R.over U))
      (restrictionComplex R U c.pt) := by
  have := preservesColimitsOfShape_restriction_of_cocontinuous R U
  have hp := CochainComplex.KFlat.preservesColimit_mapHomologicalComplex Dg (restriction R U)
  refine CochainComplex.KFlatBifunctor.kFlat_of_isColimit
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (R.over U))
    ((restrictionComplexFunctor R U).mapCocone c) (hp.preserves hc).some
    (Stacks.SheafOfModules.KFlatResolution.hF_sheafTensor (R.over U))
    (Stacks.SheafOfModules.KFlatResolution.hexact_sheafOfModules (R.over U)) fun n ↦ ?_
  obtain ⟨b, hb⟩ := hLE n
  have := hb
  exact kFlat_restriction_of_isStrictlyLE R U (Dg.obj n) b (hflat n)

omit [Limits.HasBinaryProducts C] in
/-- **A K-flat resolution that stays K-flat after restriction to the slice at `U`.** Every
complex of `O`-modules receives a termwise surjective quasi-isomorphism from a complex which is
K-flat with flat terms and whose restriction to `C/U` is again K-flat with flat terms.

This is Stacks 06YS together with the transport of its colimit presentation along restriction:
the resolution is the one of
`Stacks.SheafOfModules.KFlatResolution.exists_resolution_colimit`, and both its own K-flatness
and the K-flatness of its restriction are read off from that one presentation. No binary
products are needed on the site: the K-flatness of the restriction comes from
`kFlat_restriction_of_isColimit_of_cocontinuous`. -/
theorem exists_kFlatResolution_restriction
    (G : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ) :
    ∃ (K : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ)
      (f : K ⟶ G),
      CochainComplex.KFlatBifunctor.KFlat
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R) K ∧
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) (K.X i)) ∧
      QuasiIso f ∧ (∀ i : ℤ, Epi (f.f i)) ∧
      CochainComplex.KFlatBifunctor.KFlat
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (R.over U))
        (restrictionComplex R U K) ∧
      ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R.over U)
        ((restrictionComplex R U K).X i) := by
  obtain ⟨D, f, hLE, hflat, hqis, hepi⟩ :=
    Stacks.SheafOfModules.KFlatResolution.exists_resolution_colimit R G
  refine ⟨colimit D, f,
    Stacks.SheafOfModules.KFlatResolution.kFlat_colimit_of_isStrictlyLE_of_isFlat R D hLE hflat,
    Stacks.SheafOfModules.KFlatResolution.isFlat_colimit_X R D hflat, hqis, hepi,
    kFlat_restriction_of_isColimit_of_cocontinuous R U D (colimit.cocone D) (colimit.isColimit D)
      hLE hflat,
    fun i ↦ isFlat_restriction R U _
      (Stacks.SheafOfModules.KFlatResolution.isFlat_colimit_X R D hflat i)⟩

omit [Limits.HasBinaryProducts C] [HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **One K-flat resolution whose restriction to *every* slice is K-flat.** The colimit
presentation produced by Stacks 06YS does not mention the object the site is localized at, and
the criterion `kFlat_restriction_of_isColimit_of_cocontinuous` reads K-flatness of the
restriction off that one presentation; so a single resolution serves every object at once.

That uniformity is what a statement checked on a covering family needs: it has to restrict one
and the same K-flat model to every member of the family, and
`exists_kFlatResolution_restriction` fixes the object in advance. There are no binary products
here either, for the reason given at
`preservesColimitsOfShape_restriction_of_cocontinuous`. -/
theorem exists_kFlatResolution_restriction_forall
    [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{u}]
    [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ V : C, (J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (G : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ) :
    ∃ (K : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ)
      (f : K ⟶ G),
      CochainComplex.KFlatBifunctor.KFlat
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R) K ∧
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) (K.X i)) ∧
      QuasiIso f ∧ (∀ i : ℤ, Epi (f.f i)) ∧
      ∀ V : C, CochainComplex.KFlatBifunctor.KFlat
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (R.over V))
        (restrictionComplex R V K) := by
  obtain ⟨D, f, hLE, hflat, hqis, hepi⟩ :=
    Stacks.SheafOfModules.KFlatResolution.exists_resolution_colimit R G
  exact ⟨colimit D, f,
    Stacks.SheafOfModules.KFlatResolution.kFlat_colimit_of_isStrictlyLE_of_isFlat R D hLE hflat,
    Stacks.SheafOfModules.KFlatResolution.isFlat_colimit_X R D hflat, hqis, hepi,
    fun V => kFlat_restriction_of_isColimit_of_cocontinuous R V D (colimit.cocone D)
      (colimit.isColimit D) hLE hflat⟩

end Stacks.SheafOfModules.KFlatRestriction

end
