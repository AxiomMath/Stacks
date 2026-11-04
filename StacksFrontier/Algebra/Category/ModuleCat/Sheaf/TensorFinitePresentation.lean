module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.AlgebraicGeometry.TensorFinitePresentation.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorFiniteness

/-!
# Finite presentation of a tensor product of sheaves of modules on a ringed site

Stacks 03L6 asserts that the tensor product of two sheaves of modules on a ringed site inherits
each of the local finiteness properties of Stacks 03DL from its two factors. This file proves
the finite presentation clause, that a tensor product of sheaves of finite presentation is of
finite presentation.

## Main definitions

* `Stacks.SheafOfModules.TensorLocalProperties.tensorOverPresentation`: a presentation of the
  restriction of `F ⊗ G` to the slice site at an object `U`, built from presentations of `F.over U`
  and of `G.over U`.

## Main results

* `Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isFinitePresentation`: the tensor
  product of two sheaves of modules of finite presentation on a ringed site is of finite
  presentation. This is Stacks 03L6 for the finite presentation condition Stacks 03DL(6).

## Implementation notes

The shape of the argument is that of
`Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isFiniteType`: each factor has a
finite presentation over the members of a covering family, the objects admitting arrows into a
member of each family again cover (by `GrothendieckTopology.transitive`), and over such an
object both presentations restrict — by `Stacks.SheafOfModules.LocalKernel.presentationOver`,
which is already site-generic and preserves finiteness — so their tensor presentation presents
the restriction of `F ⊗ G` there.

Nothing of the tensor presentation itself has to be redone:
`Stacks.SheafOfModules.TensorProduct.tensorPresentation` and its finiteness
`tensorPresentation_isFinite` are stated for an arbitrary site, over the
`Stacks.SheafOfModules.TensorSheafification` spelling
`Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪` of the structure sheaf. The
two things supplied here are the slice-site instance of that spelling — `sliceO`,
`isSheaf_sliceO` — and the transport of the resulting presentation across `tensorOverIso`
onto the restriction of the globally formed tensor product.

**Two spellings of the restricted structure sheaf.**
`Stacks.SheafOfModules.TensorSheafification.structureSheaf (sliceO X U) (isSheaf_sliceO X U)`
and `(Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U` are equal by `rfl`, and so are the two
tensor
products formed over them, but they are not interchangeable where the elaborator works at
reducible transparency. The one consequence here is that the `IsIso` argument of
`SheafOfModules.Presentation.ofIsIso`, and the finiteness instance
`SheafOfModules.instIsFiniteOfIsIso`, have to be passed as terms rather than left to instance
search, which is syntactic: `Iso.isIso_hom` is an instance, but the obligation arises at
whichever of the two spellings the surrounding elaboration chose. Passing them as terms needs
only definitional equality. No transparency option is involved, and the file needs no
option overrides.

`UnivLE.{max v u, w}` is the hypothesis under which the structure presheaf of a site can be
recognised as a sheaf after composing with `forget₂ CommRingCat RingCat`; it is the hypothesis
`Stacks.SheafOfModules.TensorProduct.tensorPresentation` is stated under, and the slice site
`Over U` needs no more of it than the site itself, `max v (max u v) = max u v`.

`UnivLE.{max v u, w}` is the only hypothesis here beyond the ones needed to form the tensor
product of sheaves of modules at all. Two further hypotheses that the argument does use are
*not* assumed, being theorems under those: sheafification on each slice site is
`AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective`, attached as a local
instance, and preservation of colimits by restriction along an arrow is
`Stacks.SheafOfModules.overMap_preservesColimits`, introduced inside the proof. Stacks 03L6
assumes neither, so neither may be a hypothesis of its finite presentation clause.

## References

* [Stacks Project, Tag 03L6](https://stacks.math.columbia.edu/tag/03L6)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Limits

universe v u w

namespace Stacks.SheafOfModules.TensorLocalProperties

attribute [local instance] AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective

variable (X : AlgebraicGeometry.RingedSite.{u, v, w}) [UnivLE.{max v u, w}]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The structure presheaf of commutative rings of a ringed site, restricted to the slice site
at an object `U`. -/
noncomputable abbrev sliceO (U : X.C) : (Over U)ᵒᵖ ⥤ CommRingCat.{w} := (X.O.over U).obj

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The restricted structure presheaf is a sheaf of rings on the slice site at `U`. -/
theorem isSheaf_sliceO (U : X.C) : Presheaf.IsSheaf (X.J.over U)
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf (sliceO X U)) :=
  (Presheaf.isSheaf_iff_isSheaf_comp _ (X.O.over U).obj
    (forget₂ CommRingCat.{w} RingCat.{w})).mp (X.O.over U).property

/-- A presentation of the restriction of `F ⊗ G` to the slice site at `U`, built from
presentations of `F.over U` and of `G.over U` by forming their tensor presentation on the slice
site and transporting it along `tensorOverIso`. -/
noncomputable def tensorOverPresentation (U : X.C) (F G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (P : (F.over U).Presentation) (Q : (G.over U).Presentation) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj F).obj G).over U).Presentation :=
  @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _ (tensorOverIso X.O U F G).hom
    (tensorOverIso X.O U F G).isIso_hom
    (Stacks.SheafOfModules.TensorProduct.tensorPresentation (sliceO X U) (isSheaf_sliceO X U)
      P Q)

/-- The tensor product of two finite presentations on the slice at `U` is finite. -/
theorem tensorOverPresentation_isFinite (U : X.C) (F G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (P : (F.over U).Presentation) (Q : (G.over U).Presentation)
    [hP : P.IsFinite] [hQ : Q.IsFinite] :
    (tensorOverPresentation X U F G P Q).IsFinite :=
  @SheafOfModules.instIsFiniteOfIsIso _ _ _ _ _ _ _ _
    (tensorOverIso X.O U F G).hom (tensorOverIso X.O U F G).isIso_hom
    (Stacks.SheafOfModules.TensorProduct.tensorPresentation (sliceO X U) (isSheaf_sliceO X U)
      P Q)
    (Stacks.SheafOfModules.TensorProduct.tensorPresentation_isFinite (sliceO X U)
      (isSheaf_sliceO X U) P Q (hP := hP) (hQ := hQ))

/-- **Stacks Project, Tag 03L6, finite presentation case.** The tensor product of two sheaves of
modules of finite presentation on a ringed site is of finite presentation.

Following the source: `F` has a finite presentation over each member of a covering family and so
does `G`; the objects admitting an arrow into a member of each family again cover, and over such
an object the two restricted presentations are still finite and their tensor presentation
presents the restriction of `F ⊗ G`. -/
@[stacks 03L6 "finite_presentation"]
theorem tensorSheaf_isFinitePresentation
    (F G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [SheafOfModules.IsFinitePresentation F] [SheafOfModules.IsFinitePresentation G] :
    SheafOfModules.IsFinitePresentation
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj F).obj G) := by
  classical
  letI : ∀ (V W : X.C) (f : W ⟶ V),
      PreservesColimitsOfSize.{w, w}
        (SheafOfModules.overMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f) :=
    fun _ _ f => Stacks.SheafOfModules.overMap_preservesColimits
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f
  obtain ⟨qF, hqF⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData F
  obtain ⟨qG, hqG⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData G
  let I := Σ i : qF.I, Σ j : qG.I,
    {V : X.C // Nonempty ((V ⟶ qF.X i) × (V ⟶ qG.X j))}
  let Y (z : I) := z.2.2.1
  let pres (z : I) := tensorOverPresentation X (Y z) F G
    (Stacks.SheafOfModules.LocalKernel.presentationOver
      (Classical.choice z.2.2.2).1 (qF.presentation z.1))
    (Stacks.SheafOfModules.LocalKernel.presentationOver
      (Classical.choice z.2.2.2).2 (qG.presentation z.2.1))
  refine ⟨⟨{ I := I, X := Y, coversTop := ?_, presentation := pres }, ⟨fun z => ?_⟩⟩⟩
  · intro W
    exact X.J.transitive (qF.coversTop W) (Sieve.ofObjects Y W) (by
      intro V f hf
      refine X.J.superset_covering ?_ (qG.coversTop V)
      intro Z g hg
      obtain ⟨i, ⟨b⟩⟩ := (Sieve.mem_ofObjects_iff qF.X f).mp hf
      obtain ⟨j, ⟨c⟩⟩ := (Sieve.mem_ofObjects_iff qG.X g).mp hg
      exact (Sieve.mem_ofObjects_iff Y (g ≫ f)).2 ⟨⟨i, j, Z, ⟨(g ≫ b, c)⟩⟩, ⟨𝟙 Z⟩⟩)
  · have h1 : (qF.presentation z.1).IsFinite := hqF.isFinite_presentation z.1
    have h2 : (qG.presentation z.2.1).IsFinite := hqG.isFinite_presentation z.2.1
    exact tensorOverPresentation_isFinite X (Y z) F G _ _

end Stacks.SheafOfModules.TensorLocalProperties

end
