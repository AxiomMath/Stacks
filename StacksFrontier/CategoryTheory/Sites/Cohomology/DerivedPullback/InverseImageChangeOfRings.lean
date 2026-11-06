module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.TwoOutOfThreeShortExact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.ChangeOfRingsReduction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.KFlatPullbackCyclesInput

/-!
# The change-of-rings half of Stacks 0G6R

Stacks 0G6R says that the pullback `f^*` of sheaves of modules along a morphism of ringed topoi
keeps a short exact sequence short exact when its third term is flat.  The source deduces it
from Stacks 05VD and Stacks 03EX, applied along the factorization

`X --h--> X' --g--> Y`,  `X' = (X.C, X.J, f⁻¹O_Y)`

of `StacksPullbackFactorization`: `g^*` is the inverse image with no
change of rings, so it is exact (Stacks 04JC); `g^*T.X₃` is flat over `f⁻¹O_Y` by Stacks 05VD
applied at `X'`; and `h^*` is extension of scalars, so Stacks 03EX applies to it.

**This file is the `h^*` step, and the assembly.**  The `h^*` step is discharged
unconditionally; the `g^*` step is not, and is isolated below as a named predicate.

## Main results

* `Stacks.Sheaves.InverseImageExactness.changeOfRings_comp_toSheaf`: **the whole content of the
  `h^*` step, and it
  holds by `rfl`.**  Extension of scalars along `α : O₁ ⟶ O₂`, read on underlying sheaves of
  abelian groups, *is* the tensor product `O₂ ⊗_{O₁} ·` of Tag 06YM with `O₂` as its left
  factor.
* `Stacks.Sheaves.InverseImageExactness.shortExact_map_extendScalars`: **Stacks 03EX for change of
  rings.**  If a
  short exact sequence of sheaves of `O₁`-modules has flat third term, its extension of
  scalars along any `α : O₁ ⟶ O₂` is short exact.  Unconditional.
* `Stacks.Sheaves.InverseImageExactness.shortExact_map_pullbackTopos_auxHomH`: the same for the
  ring-theoretic half
  `h^*` of the factorization.
* `Stacks.Sheaves.InverseImageExactness.InverseImagePreservesShortExact`: the one remaining input,
  Stacks 04JC for
  sheaves of *modules* at the geometric half `g` — see the implementation notes.
* `Stacks.Sheaves.InverseImageExactness.pullbackPreservesShortExact_of_auxHomG` and
  `pullbackPreservesShortExact_of_univ`: **the reduction.**  Stacks 0G6R for `f` follows from
  Stacks 05VD (at `X'`, equivalently universally quantified) together with
  `InverseImagePreservesShortExact f`.
* `Stacks.Sheaves.InverseImageExactness.kFlat_pullbackComplex_of_univ`: what the reduction buys at
  the consumer —
  the K-flatness assertion of Tag 0G7E on universally quantified Stacks 05VD and
  `InverseImagePreservesShortExact`, i.e. with Stacks 0G6R traded for Stacks 04JC.  The count
  of open inputs is still two; see its docstring.

## Implementation notes

**The `h^*` step costs nothing.**  Three
identifications are in play and all three are `rfl`:

* `Stacks.Sheaves.ChangeOfRings.changeOfRings J α` is the sheafification of the sectionwise
  `O₂(U) ⊗_{O₁(U)} G(U)` (Tag 03CU), while `Stacks.SheafOfModules.Tensor.sheafTensor O₁` is the
    sheafification
  of the sectionwise monoidal tensor `M(U) ⊗_{O₁(U)} G(U)` of `PresheafOfModules`.  Taking `M`
  to be `O₂` restricted along `α` makes the two underlying abelian presheaves **the same term**:
  the tensor factors are already in the same order, so no commutativity comparison is needed.
  This is what makes `changeOfRings_comp_toSheaf` a `rfl`, and it is why this file routes
  through the *left* tensor factor
    (`Stacks.SheafOfModules.KFlatTwoOutOfThree.shortExact_map_sheafTensor_obj`) rather than
  the right one (`Stacks.SheafOfModules.FlatTensorShortExact.sheafTensorRight_shortExact_of_flat`):
    going through the right
  factor would need `TensorProduct.comm` sectionwise, naturally in both variables.
* `PresheafOfModules.sheafification (𝟙 R.obj) ⋙ SheafOfModules.toSheaf R` agrees with
  sheafifying the underlying abelian presheaf, in both of the two ring spellings at once.
* `(auxHomH f).pullbackTopos` is `Stacks.Sheaves.ModuleAdjunction.extendScalars` of
  `(auxHomH f).fSharpRing` (`StacksPullbackFactorization.pullbackTopos_auxHomH`), and
  `(sheafCompose X.J (forget₂ CommRingCat RingCat)).map (auxHomH f).fSharp` is that same
  morphism.

The comparison with the right-hand tensor factor **is** available after sheafification and was
*not* used: `Stacks.SheafOfModules.FlatTensorShortExact.flipIso` would supply it, but
  `Stacks.SheafOfModules.KFlatTwoOutOfThree` has already made that
crossing once and its `shortExact_map_sheafTensor_obj` is the left-factor statement, so the
crossing is paid for exactly once in the tree.

**What is still open, and why it is not the flatness input.**  The remaining statement is
`InverseImagePreservesShortExact f`, i.e. exactness of `(auxHomG f).pullbackTopos` on sheaves
of modules.  It is *not* in either tree, and in particular it is **not** what
`CategoryTheory.Sites.abelianInverseImage_exact` says: that is exactness of the inverse
  image on
ordinary *abelian* sheaves, for a `CategoryTheory.MorphismOfTopoi`, and its hook
`CategoryTheory.Sites.abelianInverseImage_forgetIso` compares it with the inverse image
  of the
underlying sheaves of **sets**.  Deducing the module statement from it needs the missing side
of that square: an isomorphism

`(auxHomG f).pullbackTopos ⋙ SheafOfModules.toSheaf ≅ SheafOfModules.toSheaf ⋙ f⁻¹`

on abelian sheaves.  That is a Beck–Chevalley comparison and it is **not formal here**:
`AlgebraicGeometry.RingedToposSiteHom.pullbackTopos` is Mathlib's `SheafOfModules.pullback`,
defined as an abstract left adjoint (`PresheafOfModules.pullback` is
`(pushforward φ).leftAdjoint`), and `SheafOfModules.toSheaf` is a right adjoint on the relevant
side, so uniqueness of adjoints does not identify the two composites.  Nothing in
the library supplies `PreservesFiniteLimits` for the module pullback —
the Stacks 06YY and Stacks 07A6 developments both
take it as an instance *hypothesis*.

**Universes.**  Everything is at `RingedTopos.{u, u, u}` with the site small in the universe of
the sections.  This narrowing is **inherited, not chosen here**, and it is forced four
independent ways on this chain; the four forcings are recorded in the implementation notes of
the Stacks 05VD reduction.  The change-of-rings section below adds no
forcing of its own beyond the two it inherits from `Stacks.SheafOfModules.Tensor.sheafTensor` and
`Stacks.Sheaves.ChangeOfRings.changeOfRings`, both of which are stated for `{C : Type u}` with
`SmallCategory C` and the ring sections in that same `u`.

**No tag is placed in this file.**  Stacks 0G6R registers its single clause with a
bare attribute carrying no clause string, and nothing here concludes that clause: the main
theorem is conditional on `Stacks.Sheaves.DerivedPullback.KFlatPullback.PullbackPreservesIsFlat`
  and on
`InverseImagePreservesShortExact`, neither of which any declaration in either tree concludes.
Stacks 03EX and Stacks 05V4 are tagged where they are proved, and the change-of-rings
statements below are corollaries of 03EX rather than new assertions of the source, so they take
no tag either.

## References

* [The Stacks Project, Tag 0G6R](https://stacks.math.columbia.edu/tag/0G6R)
* [The Stacks Project, Tag 03EX](https://stacks.math.columbia.edu/tag/03EX)
* [The Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
* [The Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace Stacks.Sheaves.InverseImageExactness

/-! ### Stacks 03EX for change of rings -/

section ChangeOfRings

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Extension of scalars is additive, being a left adjoint of restriction of scalars, which is
additive.  Without this the statements below cannot even be written: `ShortComplex.map` asks
for `PreservesZeroMorphisms` of the functor. -/
instance extendScalars_additive {R₁ R₂ : Sheaf J RingCat.{u}} (α : R₁ ⟶ R₂) :
    (Stacks.Sheaves.ModuleAdjunction.extendScalars.{u} α).Additive :=
  Adjunction.left_adjoint_additive
    (Stacks.Sheaves.ModuleAdjunction.extendRestrictScalarsAdjunction.{u} α)

variable {O₁ O₂ : Sheaf J CommRingCat.{u}}

/-- A morphism of sheaves of commutative rings, read on the sheaves of rings over which the
sheaves of modules are taken. -/
abbrev ringMap (α : O₁ ⟶ O₂) :
    Stacks.SheafOfModules.Tensor.ringSheaf O₁ ⟶ Stacks.SheafOfModules.Tensor.ringSheaf O₂ :=
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map α

/-- `O₂`, read as a sheaf of `O₁`-modules by restriction of scalars along `α`.  This is the
left tensor factor through which extension of scalars along `α` is computed. -/
abbrev restrictUnit (α : O₁ ⟶ O₂) : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₁)
  :=
  (SheafOfModules.restrictScalars (ringMap α)).obj
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O₂))

/-- **The sectionwise extension of scalars is the tensor product with `O₂`, on underlying
abelian sheaves, on the nose.**  Both sides sheafify the presheaf
`U ↦ O₂(U) ⊗_{O₁(U)} G(U)`; the tensor factors are in the same order on the two sides, so this
is `rfl` and no comparison of tensor products intervenes. -/
theorem changeOfRings_comp_toSheaf (α : O₁ ⟶ O₂) :
    Stacks.Sheaves.ChangeOfRings.changeOfRings.{u, u, u} J α ⋙
        SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O₂)
      = (Stacks.SheafOfModules.Tensor.sheafTensor O₁).obj (restrictUnit α) ⋙
        SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O₁) :=
  rfl

/-- The same identification for the abstract extension of scalars, which is isomorphic to the
sectionwise one by
`Stacks.Sheaves.DerivedPullback.FlatExtendScalars.extendScalarsIsoChangeOfRings`.
-/
def extendScalarsCompToSheafIso (α : O₁ ⟶ O₂) :
    Stacks.Sheaves.ModuleAdjunction.extendScalars.{u} (ringMap α) ⋙
        SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O₂)
      ≅ (Stacks.SheafOfModules.Tensor.sheafTensor O₁).obj (restrictUnit α) ⋙
        SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O₁) :=
  Functor.isoWhiskerRight
    (Stacks.Sheaves.DerivedPullback.FlatExtendScalars.extendScalarsIsoChangeOfRings α)
      (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O₂)) ≪≫
    eqToIso (changeOfRings_comp_toSheaf α)

/-- **Stacks 03EX for change of rings.**  Extension of scalars along `α : O₁ ⟶ O₂` carries a
short exact sequence of sheaves of `O₁`-modules whose third term is flat to a short exact
sequence of sheaves of `O₂`-modules.

Short exactness is read on underlying abelian sheaves, where `extendScalarsCompToSheafIso`
turns the statement into Stacks 03EX for the tensor product
(`Stacks.SheafOfModules.KFlatTwoOutOfThree.shortExact_map_sheafTensor_obj`);
  `SheafOfModules.toSheaf` is exact
(Stacks 03DA) and faithful, so it both carries and reflects short exactness. -/
theorem shortExact_map_extendScalars (α : O₁ ⟶ O₂)
    (S : ShortComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₁)))
    (hS : S.ShortExact)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := O₁) S.X₃) :
    (S.map (Stacks.Sheaves.ModuleAdjunction.extendScalars.{u} (ringMap α))).ShortExact := by
  refine ShortExact.reflects_shortExact_of_faithful
    (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O₂)) ?_
  refine ShortComplex.shortExact_of_iso
    (S.mapNatIso (extendScalarsCompToSheafIso α).symm) ?_
  exact (Stacks.SheafOfModules.KFlatTwoOutOfThree.shortExact_map_sheafTensor_obj O₁ S hS hflat
    (restrictUnit α)).map_of_exact (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
      O₁))

end ChangeOfRings

/-! ### The ring-theoretic half of the factorization -/

section Reduction

open StacksPullbackFactorization

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- `h^*` is additive.  `AlgebraicGeometry.RingedToposSiteHom.pullbackTopos_additive`
applies, but instance *search* does not find it at the `auxHomH f` spelling — the side
conditions it carries are stated for the auxiliary ringed topos and have to be seated one at a
time — so it is restated here at that spelling. -/
instance pullbackTopos_auxHomH_additive (f : AlgebraicGeometry.RingedToposSiteHom X Y) :
    (auxHomH f).pullbackTopos.Additive :=
  AlgebraicGeometry.RingedToposSiteHom.pullbackTopos_additive (auxHomH f)

/-- `g^*` is additive, restated at the `auxHomG f` spelling for the same reason as
`pullbackTopos_auxHomH_additive`. -/
instance pullbackTopos_auxHomG_additive (f : AlgebraicGeometry.RingedToposSiteHom X Y) :
    (auxHomG f).pullbackTopos.Additive :=
  AlgebraicGeometry.RingedToposSiteHom.pullbackTopos_additive (auxHomG f)

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Stacks 03EX for the ring-theoretic half `h^*` of the factorization.**  `h^*` is extension
of scalars along `f⁻¹O_Y ⟶ O_X` on the nose
(`StacksPullbackFactorization.pullbackTopos_auxHomH`), so this is
`shortExact_map_extendScalars`.  No hypothesis on `f` is used. -/
theorem shortExact_map_pullbackTopos_auxHomH (f : AlgebraicGeometry.RingedToposSiteHom X Y)
    (S : ShortComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (auxTopos f).O)))
    (hS : S.ShortExact)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := (auxTopos f).O) S.X₃) :
    (S.map (auxHomH f).pullbackTopos).ShortExact :=
  shortExact_map_extendScalars (auxHomH f).fSharp S hS hflat

/-- **Stacks 04JC for sheaves of modules, at the geometric half `g` of the factorization.**
For a morphism of ringed topoi — the underlying continuous functor being a morphism of sites —
the inverse image with no change of rings is exact, so it carries a short exact sequence of
sheaves of `O_Y`-modules to a short exact sequence of sheaves of `f⁻¹O_Y`-modules.

No flatness enters: `g^*` is exact, full stop.  As for
  `Stacks.Sheaves.DerivedPullback.KFlatPullback.PullbackPreservesIsFlat`,
the morphism-of-sites hypothesis is part of the statement and cannot be dropped — for a merely
continuous `f.u` the functor `f⁻¹` need not be left exact.

**No declaration in either tree concludes this**; see the implementation notes for what the
04JC port does and does not give. -/
def InverseImagePreservesShortExact (f : AlgebraicGeometry.RingedToposSiteHom X Y) : Prop :=
  f.u.IsMorphismOfSites Y.J X.J →
    ∀ T : ShortComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)),
      T.ShortExact → (T.map (auxHomG f).pullbackTopos).ShortExact

end Reduction

/- The reduction of 0G6R, in a section without the variables `[Y.J.HasSheafCompose _]` and
`[HasSheafify Y.J _]`: Lean 4.35 lets instance search see a section variable even under `omit`,
so the `HasSheafify Y.J` its statement needs would be the section variable rather than the
global `Stacks.SheafOfModules.coefficientSheafification`. -/
section ReductionOfZeroG6R

open StacksPullbackFactorization

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Stacks 0G6R for `f` follows from Stacks 05VD at `X'` together with exactness of `g^*`.**

The three steps of the source's proof: `g^*T` is short exact because `g^*` is exact (04JC, the
hypothesis `hg`); its third term `g^*T.X₃` is flat over `f⁻¹O_Y` by Stacks 05VD applied at the
auxiliary ringed topos `X'` (the hypothesis `hpf` — and the morphism-of-sites hypothesis is the
same on both sides, since `(auxHomG f).u = f.u` and `(auxTopos f).J = X.J` by `rfl`); and
`h^*` of it is short exact by Stacks 03EX
(`shortExact_map_pullbackTopos_auxHomH`).  The conclusion is transported along
`StacksPullbackFactorization.pullbackFactorIso`, which says `f^* ≅ g^* ⋙ h^*`. -/
theorem pullbackPreservesShortExact_of_auxHomG
    (f : AlgebraicGeometry.RingedToposSiteHom X Y)
    (hpf : Stacks.Sheaves.DerivedPullback.KFlatPullback.PullbackPreservesIsFlat (auxHomG f))
    (hg : InverseImagePreservesShortExact f) :
    Stacks.Sheaves.DerivedPullback.KFlatPullback.PullbackPreservesShortExact f := by
  intro hmos T hT hflat
  change ShortComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) at T
  refine ShortComplex.shortExact_of_iso (T.mapNatIso (pullbackFactorIso f)) ?_
  exact shortExact_map_pullbackTopos_auxHomH f (T.map (auxHomG f).pullbackTopos)
    (hg hmos T hT) (hpf hmos T.X₃ hflat)

end ReductionOfZeroG6R

/-! ### The universally quantified form of Stacks 05VD -/

/-- Stacks 05VD for *every* morphism of ringed topoi at once — the form in which the reduction
of `pullbackPreservesShortExact_of_univ` consumes it, since the source applies 05VD not to `f`
but to the geometric half `g : X' ⟶ Y` of its factorization. -/
def PullbackPreservesIsFlatUniv : Prop :=
  ∀ {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
    [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (f : AlgebraicGeometry.RingedToposSiteHom X Y),
      Stacks.Sheaves.DerivedPullback.KFlatPullback.PullbackPreservesIsFlat f

section Univ

open StacksPullbackFactorization

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Stacks 0G6R from universally quantified Stacks 05VD and exactness of `g^*`.**  This is
`pullbackPreservesShortExact_of_auxHomG` with the flatness input taken at every morphism of
ringed topoi rather than at the auxiliary one; instantiating it at `auxHomG f` needs no
transport, and in particular introduces no new instance burden, because
`(auxTopos f).J = X.J` by `rfl`. -/
theorem pullbackPreservesShortExact_of_univ
    (f : AlgebraicGeometry.RingedToposSiteHom X Y)
    (hpf : PullbackPreservesIsFlatUniv.{u})
    (hg : InverseImagePreservesShortExact f) :
    Stacks.Sheaves.DerivedPullback.KFlatPullback.PullbackPreservesShortExact f :=
  pullbackPreservesShortExact_of_auxHomG f (hpf (auxHomG f)) hg

section Consumer

variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]

/-- **The K-flatness assertion of Tag 0G7E with Stacks 0G6R replaced by Stacks 04JC for
sheaves of modules.**
  `Stacks.Sheaves.DerivedPullback.KFlatPullback.kFlat_pullbackComplex_of_pullbackPreserves` takes
    the two
inputs `PullbackPreservesIsFlat` (Stacks 05VD) and `PullbackPreservesShortExact` (Stacks 0G6R);
here the second is traded for `InverseImagePreservesShortExact` by
`pullbackPreservesShortExact_of_univ`.

This records what the reduction does and does not buy.  The count of open inputs is **still
two**: the flatness input is now consumed universally quantified rather than at `f` alone, and
0G6R has become exactness of the module inverse image.  What it buys is that the second input
is no longer a statement about flatness at all — it is pure 04JC infrastructure, independent of
Stacks 05VD and of the filteredness condition 05VD is blocked on. -/
theorem kFlat_pullbackComplex_of_univ (f : AlgebraicGeometry.RingedToposSiteHom X Y)
    (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (hpf : PullbackPreservesIsFlatUniv.{u})
    (hg : InverseImagePreservesShortExact f)
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Stacks.SheafOfModules.KFlat.KFlat Y.O K)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O)
      (K.X i)) :
    Stacks.SheafOfModules.KFlat.KFlat X.O
      ((Stacks.Sheaves.DerivedPullback.KFlatPullback.pullbackComplex f).obj K) :=
  Stacks.Sheaves.DerivedPullback.KFlatPullback.kFlat_pullbackComplex_of_pullbackPreserves f hmos
    (hpf f)
    (pullbackPreservesShortExact_of_univ f hpf hg) K hK hflatK

end Consumer

end Univ

end Stacks.Sheaves.InverseImageExactness

end

end
