module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatChangeOfRings
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.MixedDerivedTensor.AuxiliaryRingedSite

/-!
# The underived identity `F ⊗_O f^*G = F ⊗_{f⁻¹O'} f⁻¹G`

Let `f : (Sh(C), O) ⟶ (Sh(C'), O')` be a morphism of ringed topoi, let `F` be a sheaf of
`O`-modules and let `G` be a sheaf of `O'`-modules.  Reading `F` as a sheaf of
`f⁻¹O'`-modules by restriction of scalars along `f⁻¹O' ⟶ O`, there is an isomorphism

`F ⊗_{f⁻¹O'} f⁻¹G ≅ F ⊗_O f^*G`

of sheaves of abelian groups, natural in `F`.  This is the underived content of Stacks 08I6,
and it is the identity that the source's proof of that tag passes to the derived category.

The two steps are the two halves of the factorization `X --h--> X' --g--> Y` of
`StacksPullbackFactorization`, with `X' = (C, f⁻¹O')`.  The geometric half gives
`f^*G ≅ h^*(g^*G)`, i.e. `f^*G` is the extension of scalars of `f⁻¹G` along `f⁻¹O' ⟶ O`.  The
ring-theoretic half is the cancellation of a base change,

`H ⊗_{O} (O ⊗_{f⁻¹O'} N) ≅ H|_{f⁻¹O'} ⊗_{f⁻¹O'} N`,

which is `Stacks.FlatChangeOfRings.tensorBaseChangeSheafIso`, sectionwise
`TensorProduct.AlgebraTensorModule.cancelBaseChange`.  The source states that cancellation as
an identity of sheaves of abelian groups, and that is the generality in which it is available
here; see the implementation notes.

## Main definitions

* `Functor.mapIso` on the native flipped tensor bifunctor: an isomorphism of the fixed
  tensor factor induces an isomorphism of the functors of tensoring with it.
* `Stacks.Cohomology.MixedDerivedTensor.tensorBaseChangeIso`: the cancellation of a base
  change, with the abstract extension of scalars in place of the sectionwise one.
* `Stacks.Cohomology.MixedDerivedTensor.SheafifyCommutesRestrictScalars`: the comparison of
  the two sheafifications of one underlying abelian presheaf — over `O₁` after restricting
  scalars, and over `O₂` before restricting them.
* `Stacks.Cohomology.MixedDerivedTensor.tensorBaseChangeModuleIso`: the cancellation of a
  base change as sheaves of `O₁`-modules, granted that comparison.
* `Stacks.Cohomology.MixedDerivedTensor.pullbackIsoExtendInverseImage`: `f^*G` is the
  extension of scalars of `f⁻¹G` along `f⁻¹O' ⟶ O`.
* `Stacks.Cohomology.MixedDerivedTensor.underivedTensorInverseImageIso`: **the underived
  identity of Stacks 08I6**, as sheaves of abelian groups.  Unconditional.
* `Stacks.Cohomology.MixedDerivedTensor.underivedTensorInverseImageModuleIso`: the same
  identity as sheaves of `f⁻¹O'`-modules, granted the comparison of the two sheafifications.

## Main results

* `Stacks.Cohomology.MixedDerivedTensor.extendScalarsIsoPullbackAuxHomH`: the two extensions
  of scalars along `f⁻¹O' ⟶ O` in play — the sectionwise tensor product followed by
  sheafification, and the abstract left adjoint of restriction of scalars that `h^*` is —
  agree.  Both are left adjoints of the same restriction of scalars, so this is uniqueness of
  left adjoints; `h_*` is that restriction of scalars by `rfl`.
* `Stacks.Cohomology.MixedDerivedTensor.restrictScalars_comp_forget`: restriction of scalars
  does not change the underlying presheaf of modules, by `rfl`.

## Implementation notes

**Why the unconditional identity is stated on underlying sheaves of abelian groups, and what
exactly is missing from the `f⁻¹O'`-linear one.**  The cancellation isomorphism of
`Stacks.FlatChangeOfRings` is `f⁻¹O'`-linear already at the level of *presheaves* of modules
(`Stacks.FlatChangeOfRings.baseChangeNatIsoOf`); the step that forgets the module structure is
the passage from the sectionwise extension of scalars to its sheafification,
`Stacks.FlatChangeOfRings.tensorRightExtendScalarsIso`, which is stated after
`Stacks.moduleSheafification` over the *target* ring `O`.  Reinstating the linearity therefore
needs exactly one comparison, of the two sheafifications of one underlying abelian presheaf —
over `f⁻¹O'` after restricting scalars, and over `O` before restricting them.  Of the two
identifications involved, `restrictScalars_comp_forget` holds by `rfl` and this one does not:
the two sheafifications build the scalar action from different rings.  It is isolated as
`SheafifyCommutesRestrictScalars`, and no declaration in either tree supplies it.

This matters beyond bookkeeping.  An isomorphism of underlying abelian sheaves carries no
information about the `f⁻¹O'`-module structure, so it does not descend to the derived category
of `f⁻¹O'`-modules; the conditional `underivedTensorInverseImageModuleIso` is the form of the
identity that a derived statement of Stacks 08I6 would consume.

**The three extensions of scalars.**  `Stacks.FlatChangeOfRings.extendScalars` is the
sectionwise tensor product followed by sheafification,
`Stacks.Sheaves.ModuleAdjunction.extendScalars` is the abstract left adjoint of restriction
of scalars, and `AlgebraicGeometry.RingedToposSiteHom.pullbackTopos` of the ring-theoretic
half of the factorization is the second of these by `rfl`
(`StacksPullbackFactorization.pullbackTopos_auxHomH`).  The first and the second are compared
once, by uniqueness of left adjoints, in `extendScalarsIsoPullbackAuxHomH`; no other crossing
between the two occurs.

**Universes.**  Everything is at `AlgebraicGeometry.RingedTopos.{u, u, u}`.  The module
universe is not independent of the ring universe in this file, and that is inherited from
`Stacks.FlatChangeOfRings.tensorRightExtendScalarsIso`, whose own notes record that
`Stacks.isIso_sheafification_map_tensorMapRight` pins the two together through the extension
theorem for bilinear maps along a local bijection.

**No tag is placed in this file.**  Stacks 08I6 asserts an isomorphism in the derived
category, and nothing here concludes that; the underived identity below is a step of the
source's proof rather than the assertion of the tag, and a tag on it would make the dashboard
read as progress on a statement about derived categories.

## References

* [The Stacks Project, Tag 08I6](https://stacks.math.columbia.edu/tag/08I6)
* [The Stacks Project, Tag 05V4](https://stacks.math.columbia.edu/tag/05V4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace Stacks.Cohomology.MixedDerivedTensor

/-! ### Transporting the fixed tensor factor along an isomorphism -/

section Transport

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Tensoring on the right with the identity is the identity. -/
lemma tensorMapRight_id {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    (M N : PresheafOfModules.{w} (Stacks.ringPresheaf O)) :
    Stacks.tensorMapRight M (𝟙 N) = 𝟙 (Stacks.tensorObj M N) := by
  apply PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext x y
  rfl

/-- An isomorphism of the second tensor factor induces an isomorphism of the functors of
tensoring with it, on presheaves of modules. -/
def tensorRightNatIso {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    {N N' : PresheafOfModules.{w} (Stacks.ringPresheaf O)} (e : N ≅ N') :
    (Stacks.tensorRight N : PresheafOfModules.{w} (Stacks.ringPresheaf O) ⥤ _) ≅
      Stacks.tensorRight N' where
  hom := Stacks.tensorRightNatTrans e.hom
  inv := Stacks.tensorRightNatTrans e.inv
  hom_inv_id := by
    apply NatTrans.ext
    funext M
    simp only [NatTrans.comp_app, Stacks.tensorRightNatTrans_app, NatTrans.id_app]
    rw [Stacks.tensorMapRight_comp, e.hom_inv_id, tensorMapRight_id]
    rfl
  inv_hom_id := by
    apply NatTrans.ext
    funext M
    simp only [NatTrans.comp_app, Stacks.tensorRightNatTrans_app, NatTrans.id_app]
    rw [Stacks.tensorMapRight_comp, e.inv_hom_id, tensorMapRight_id]
    rfl

end Transport

/-! ### Cancellation of a base change -/

section BaseChange

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {O₁ O₂ : Sheaf J CommRingCat.{w}}

/-- **Cancellation of a base change.**  For a morphism `α : O₁ ⟶ O₂` of sheaves of
commutative rings and a sheaf `G` of `O₁`-modules, tensoring an `O₂`-module `H` with the
extension of scalars `O₂ ⊗_{O₁} G` gives the same sheaf of abelian groups as tensoring the
restriction of `H` with `G` over `O₁`, naturally in `H`.

This is `Stacks.FlatChangeOfRings.tensorBaseChangeSheafIso` followed by
`Stacks.FlatChangeOfRings.tensorRightExtendScalarsIso`, which replaces the sectionwise
extension of scalars by its sheafification. -/
def tensorBaseChangeIso (α : O₁ ⟶ O₂)
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₁)) :
    SheafOfModules.restrictScalars.{w} (Stacks.FlatChangeOfRings.ringSheafMap α) ⋙
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O₁).flip.obj G ⋙
          SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O₁)
      ≅ (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O₂).flip.obj
            ((Stacks.FlatChangeOfRings.extendScalars α).obj G) ⋙
          SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O₂) :=
  Stacks.FlatChangeOfRings.tensorBaseChangeSheafIso α G ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O₂))
        (Stacks.FlatChangeOfRings.tensorRightExtendScalarsIso α G))
      (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O₂))

omit [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Restriction of scalars leaves the underlying presheaf of modules alone.  This is one of
the two identifications the `O₁`-linear form of the cancellation needs, and it holds by
`rfl`. -/
lemma restrictScalars_comp_forget (α : O₁ ⟶ O₂) :
    SheafOfModules.restrictScalars.{w} (Stacks.FlatChangeOfRings.ringSheafMap α) ⋙
        SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O₁)
      = SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O₂) ⋙
          PresheafOfModules.restrictScalars (Stacks.FlatChangeOfRings.ringSheafMap α).hom :=
  rfl

/-- **Sheafification of presheaves of modules commutes with restriction of scalars.**  The
two functors `PresheafOfModules(O₂) ⥤ SheafOfModules(O₁)` obtained by restricting scalars and
then sheafifying over `O₁`, and by sheafifying over `O₂` and then restricting scalars, have
one and the same underlying sheaf of abelian groups, namely the sheafification of the
underlying abelian presheaf.

It is **not** a definitional equality — `Stacks.moduleSheafification O₁` and
`Stacks.moduleSheafification O₂` build the scalar action of the sheafification from different
rings.

Two things this docstring used to claim are no longer true.  It is supplied, unconditionally, by
`Stacks.Cohomology.MixedDerivedTensor.sheafifyCommutesRestrictScalars`.  And it is not the only
input missing for the `O₂`-linear cancellation of a base change: that cancellation is now proved,
for presheaves and for sheaves, in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/MixedBaseChangeTensor.lean`
(`Stacks.MixedBaseChange.mixedBaseChange:324`, `mixedSheafBaseChangeNatIso:404`), and it did not
need this input — at presheaf level the identification is `rfl`, provided the mixed tensor product
is built on top of `tensorObj (restrict f H) G` rather than as a fresh presheaf.  What a derived
form of Stacks 08I6 still needs is bifunctoriality in the second variable, the `O₂`-linear form of
`mixedTensorTotalIso`, and the one-sided K-flat re-run. -/
def SheafifyCommutesRestrictScalars (α : O₁ ⟶ O₂) : Type _ :=
  PresheafOfModules.restrictScalars
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf O₁).obj)
      (R' := (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)
      (Stacks.FlatChangeOfRings.ringSheafMap α).hom ⋙ Stacks.moduleSheafification O₁
    ≅ Stacks.moduleSheafification O₂ ⋙
        SheafOfModules.restrictScalars.{w}
          (R := Stacks.SheafOfModules.Tensor.ringSheaf O₁)
          (R' := Stacks.SheafOfModules.Tensor.ringSheaf O₂)
          (Stacks.FlatChangeOfRings.ringSheafMap α)

/-- **Cancellation of a base change, as sheaves of `O₁`-modules**, granted the comparison of
the two sheafifications.

With that comparison in hand the cancellation is `O₁`-linear and not merely an identity of
sheaves of abelian groups: `Stacks.FlatChangeOfRings.baseChangeNatIsoOf` is already an
isomorphism of presheaves of `O₁`-modules, and the only reason
`Stacks.FlatChangeOfRings.tensorBaseChangeSheafIso` forgets the module structure is that it
sheafifies afterwards over `O₂` rather than over `O₁`. -/
def tensorBaseChangeModuleIso (α : O₁ ⟶ O₂) (h : SheafifyCommutesRestrictScalars.{u, v, w} α)
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₁)) :
    SheafOfModules.restrictScalars.{w} (Stacks.FlatChangeOfRings.ringSheafMap α) ⋙
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O₁).flip.obj G
      ≅ (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O₂).flip.obj
            ((Stacks.FlatChangeOfRings.extendScalars α).obj G) ⋙
          SheafOfModules.restrictScalars.{w} (Stacks.FlatChangeOfRings.ringSheafMap α) := by
  refine Iso.trans ?_ (Functor.isoWhiskerLeft
    (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O₂))
    (Functor.isoWhiskerRight (Stacks.FlatChangeOfRings.tensorRightExtendScalarsIso α G)
      (SheafOfModules.restrictScalars.{w} (Stacks.FlatChangeOfRings.ringSheafMap α))))
  refine Iso.trans ?_ (Functor.isoWhiskerLeft
    (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O₂) ⋙
      Stacks.tensorRightOf O₂ ((Stacks.FlatChangeOfRings.presheafExtendScalars α).obj G.val)) h)
  exact (Functor.isoWhiskerLeft
    (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O₂))
    (Functor.isoWhiskerRight (Stacks.FlatChangeOfRings.baseChangeNatIsoOf α G)
      (Stacks.moduleSheafification O₁))).symm

end BaseChange

/-! ### The underived identity of Stacks 08I6 -/

section Tag08I6

open StacksPullbackFactorization

attribute [local instance]
  AlgebraicGeometry.SheafOfModules.isRightAdjoint_sheafPushforwardContinuous_commRingCat

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : AlgebraicGeometry.RingedToposSiteHom X Y)

/-- **The sectionwise extension of scalars along `f⁻¹O' ⟶ O` is `h^*`.**  Both functors are
left adjoints of restriction of scalars along `f⁻¹O' ⟶ O`: the first by
`Stacks.FlatChangeOfRings.extendScalarsAdjunction`, the second because `h_*` *is* that
restriction of scalars (`pushforwardTopos_auxHomH`).  So this is uniqueness of left
adjoints. -/
def extendScalarsIsoPullbackAuxHomH :
    Stacks.FlatChangeOfRings.extendScalars ((auxHomH f).fSharp) ≅ (auxHomH f).pullbackTopos :=
  Adjunction.leftAdjointUniq (Stacks.FlatChangeOfRings.extendScalarsAdjunction _)
    (auxHomH f).pullbackPushforwardAdjunctionTopos

/-- **`f^*G` is the extension of scalars of `f⁻¹G` along `f⁻¹O' ⟶ O`.**  The geometric half
`g` of the factorization carries `G` to `f⁻¹G` with no change of rings, and the
ring-theoretic half `h` extends the scalars; their composite is `f^*`, which is
`StacksPullbackFactorization.pullbackFactorIso`. -/
def pullbackIsoExtendInverseImage
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) :
    (Stacks.FlatChangeOfRings.extendScalars ((auxHomH f).fSharp)).obj
        ((auxHomG f).pullbackTopos.obj G) ≅ f.pullbackTopos.obj G :=
  (extendScalarsIsoPullbackAuxHomH f).app _ ≪≫ (pullbackFactorIso f).app G

/-- **The underived identity of Stacks 08I6.**  For a sheaf `G` of `O'`-modules, the functor
carrying a sheaf `F` of `O`-modules to `F|_{f⁻¹O'} ⊗_{f⁻¹O'} f⁻¹G` and the functor carrying it
to `F ⊗_O f^*G` have the same underlying sheaf of abelian groups, naturally in `F`.

The identity of the source's proof, in the source's own generality: `f^*G` is the extension of
scalars of `f⁻¹G` (`pullbackIsoExtendInverseImage`), and the base change then cancels
(`tensorBaseChangeIso`). -/
def underivedTensorInverseImageIso
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) :
    restrictToInvRing f ⋙
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (invRing f)).flip.obj
            ((auxHomG f).pullbackTopos.obj G) ⋙
          SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (auxTopos f).O)
      ≅ (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).flip.obj
            (f.pullbackTopos.obj G) ⋙
          SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O) :=
  tensorBaseChangeIso ((auxHomH f).fSharp) ((auxHomG f).pullbackTopos.obj G) ≪≫
    Functor.isoWhiskerRight
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).flip.mapIso
        (pullbackIsoExtendInverseImage f G))
      (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))

/-- **The underived identity of Stacks 08I6, as sheaves of `f⁻¹O'`-modules**, granted the
comparison of the two sheafifications.

This is the form the derived statement of the tag needs: an isomorphism of sheaves of abelian
groups carries no information about the `f⁻¹O'`-module structure and so does not descend to
the derived category of `f⁻¹O'`-modules, whereas this one does. -/
def underivedTensorInverseImageModuleIso
    (h : SheafifyCommutesRestrictScalars.{u, u, u} ((auxHomH f).fSharp))
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) :
    restrictToInvRing f ⋙
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (invRing f)).flip.obj
            ((auxHomG f).pullbackTopos.obj G)
      ≅ (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).flip.obj
            (f.pullbackTopos.obj G) ⋙ restrictToInvRing f :=
  tensorBaseChangeModuleIso ((auxHomH f).fSharp) h ((auxHomG f).pullbackTopos.obj G) ≪≫
    Functor.isoWhiskerRight
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).flip.mapIso
        (pullbackIsoExtendInverseImage f G))
      (restrictToInvRing f)

end Tag08I6

end Stacks.Cohomology.MixedDerivedTensor

end
