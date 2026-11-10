module

public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentAffineStalkLegs

/-!
# The stalkwise comparison of Stacks 0D0I

Let `f : X ⟶ Y` be a morphism of schemes, let `U` be an open of `Y` and `V` an open of `X` with
`V ⊆ f^{-1}U`.  The canonical map `(NL_{A/R})~ ⟶ NL_{X/Y}|_V` of
`Stacks.NaiveCotangentAffineMap.comparisonMap` is an isomorphism in `D(𝒪_V)` precisely when all of
its maps of stalk complexes are quasi-isomorphisms
(`AlgebraicGeometry.SheafOfModules.quasiIso_of_forall_stalk_quasiIso`), and
`CochainComplex.quasiIso_of_isZero_X_of_addEquiv` reduces each of those to four additive
identifications of the terms of the two stalk complexes together with four elementary conditions
on the kernel and the cokernel.  This file supplies the identifications and all but one of the
hypotheses.

## Main definitions

* `Stacks.NaiveCotangentAffineStalkComparison.uNegOne` and
  `Stacks.NaiveCotangentAffineStalkComparison.uZero`: the stalk at `x` of the degree `-1`,
  respectively degree `0`, term of `(NL_{A/R})~` is `𝒪_{X,x} ⊗_{Γ(X,V)} NL_{A/R}`, which is the
  corresponding term of `NaiveCotangent.nlExtensionBaseChange`.  These are clause (3) of
  Stacks 01BH, through `Stacks.NaiveCotangentAffineStalkLegs.uLeg`, composed with the
  identification of the term of a two-term complex.
* `Stacks.NaiveCotangentAffineStalkComparison.vNegOne` and
  `Stacks.NaiveCotangentAffineStalkComparison.vZero`: the stalk at `x` of the corresponding term
  of `NL_{X/Y}|_V` is the conormal module, respectively the cotangent space, of the canonical
  presentation of `𝒪_{X,x}` over `(f^{-1}𝒪_Y)_x`, which is the corresponding term of
  `NaiveCotangent.nlOfExtension`.  These compose
  `Stacks.NaiveCotangentAffineStalkLegs.restrictStalkAddEquiv` with Stacks 0D09.

## Main results

* `Stacks.NaiveCotangentAffineStalkComparison.uLeg_map`: **the stalk of the associated sheaf is
  natural in the module.**  The stalk at `x` of the map of associated sheaves induced by an
  `A`-linear `φ` is `φ` base changed to `𝒪_{X,x}`.  This is the degreewise statement that makes
  the differential of `(NL_{A/R})~` the base change of the differential of `NL_{A/R}`.
* `Stacks.NaiveCotangentAffineStalkComparison.isZero_src` and
  `Stacks.NaiveCotangentAffineStalkComparison.isZero_tgt`: both stalk complexes vanish outside
  degrees `-1` and `0`.
* `Stacks.NaiveCotangentAffineStalkComparison.tgt_d`: the identifications of the terms of
  `NL_{X/Y}|_V` carry its differential to the cotangent complex of the stalk extension.
* `Stacks.NaiveCotangentAffineStalkComparison.stalkAlgEquiv_germ`: the identification of
  `𝒪_{V,x}` with `𝒪_{X,x}` carries the germ of a section over `W` to the germ over `V.ι ''ᵁ W`.

## Implementation notes

**Spell every shared parameter the way the consumer spells it.**  The rule that an abstract
statement is cheap to instantiate exactly when the concrete data replaces a *variable* of the
statement has a corollary which is what the work here turns on: the consumer's term is produced
by other lemmas, so the abstract statement has to use the *same spelling* of every parameter
those lemmas use.  Two spellings of one ring sheaf —
`structureSheafRing V.toScheme.toRingedSpace` and
`V.toScheme.ringCatSheaf` — appearing inside a `PresheafOfModules.toPresheaf` and a
`TopCat.Presheaf.stalkFunctor` put the difference inside colimit data whose definition is not
exposed, and the unifier then exceeds 200000 heartbeats rather than reducing;
`Stacks.NaiveCotangentAffineStalkComparison.uLeg_map` is stated in the second spelling for that
reason, because that is the one `Stacks.NaiveCotangentAffineStalkLegs.stalkMap_comp_apply`
produces.

**Why the vanishing statements avoid `mapHomologicalComplex`.**  Written as a statement about
`(F.mapHomologicalComplex c).obj K |>.X i` rather than about `F.obj (K.X i)`, the two results
above drag in synthesis of `F.PreservesZeroMorphisms`, which fails when the point is written in
the `x : V` reading rather than as a point of the site's underlying space.  The two forms are
equal by `rfl`, so the statements given here apply to the complex form without the instance ever
being needed.

## References

* [Stacks Project, Tag 0D0I](https://stacks.math.columbia.edu/tag/0D0I), of whose proof this is a
  step.
* [Stacks Project, Tag 0D09](https://stacks.math.columbia.edu/tag/0D09), the stalk of the naive
  cotangent complex of a morphism of sheaves of rings.
* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH), clause (3): the stalks
  of the sheaf associated to a module.
* [Stacks Project, Tag 08TL](https://stacks.math.columbia.edu/tag/08TL), the stalkwise criterion
  for quasi-isomorphy.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

universe u

noncomputable section

namespace Stacks.NaiveCotangentAffineStalkComparison

open Stacks.NaiveCotangentAffineIso Stacks.NaiveCotangentAffineMap Stacks.AssociatedSheaf
open Stacks.NaiveCotangentAffineStalkLegs Stacks.SheafOfModules

variable {X : Scheme.{u}} (V : X.Opens) (x : V)

/-- The identification `stalkAlgEquiv` of `𝒪_{V,x}` with `𝒪_{X,x}` sends the germ at `x` of a
section `s` over `W` to the germ at `x` of `s` over `V.ι ''ᵁ W`. -/
theorem stalkAlgEquiv_germ (W : V.toScheme.Opens) (hx : x ∈ W)
    (s : V.toScheme.presheaf.obj (op W)) :
    letI := stalkAlgebra V.toScheme.toRingedSpace (alpha (V := V)) x
    stalkAlgEquiv V x ((V.toScheme.presheaf.germ W x hx).hom s) =
      (X.presheaf.germ (V.ι ''ᵁ W) x.1 (show (x : X) ∈ V.ι ''ᵁ W by simpa using hx)).hom s := by
  let := stalkAlgebra V.toScheme.toRingedSpace (alpha (V := V)) x
  exact ConcreteCategory.congr_hom (V.germ_stalkIso_hom (V := W) x hx) s

/-- Under `uLeg`, the map of stalks at `x` induced by the map of associated sheaves of an
`A`-linear map `φ : M ⟶ N` is the base change of `φ` to `𝒪_{X,x}`. -/
theorem uLeg_map (M N : ModuleCat.{u} Γ(X, V)) (φ : M ⟶ N)
    (ζ : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      ((associatedSheafFunctor.{u, u} V.toScheme.toRingedSpace
        (alpha (V := V))).obj M).val.presheaf x)) :
    letI := stalkAlgebra V.toScheme.toRingedSpace (alpha (V := V)) x
    uLeg V x N
        (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          ((PresheafOfModules.toPresheaf V.toScheme.ringCatSheaf.obj).map
            ((associatedSheafFunctor.{u, u} V.toScheme.toRingedSpace
              (alpha (V := V))).map φ).val)).hom ζ) =
      (LinearMap.baseChange (ToType (X.presheaf.stalk x.1)) φ.hom) (uLeg V x M ζ) := by
  let := stalkAlgebra V.toScheme.toRingedSpace (alpha (V := V)) x
  let Psi := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((PresheafOfModules.toPresheaf V.toScheme.ringCatSheaf.obj).map
      ((associatedSheafFunctor.{u, u} V.toScheme.toRingedSpace (alpha (V := V))).map φ).val)
  obtain ⟨w, rfl⟩ :=
    (associatedSheafStalkAddEquiv V.toScheme.toRingedSpace (alpha (V := V)) M x).symm.surjective ζ
  induction w using TensorProduct.inductionOn with
  | add w₁ w₂ h₁ h₂ =>
      refine Eq.trans (congrArg (uLeg V x N)
        (Eq.trans (congrArg Psi.hom (map_add
          (associatedSheafStalkAddEquiv V.toScheme.toRingedSpace (alpha (V := V)) M x).symm
          w₁ w₂)) (map_add Psi.hom _ _))) ?_
      refine Eq.trans (map_add (uLeg V x N) _ _) ?_
      refine Eq.trans (congrArg₂ (fun p q => p + q) h₁ h₂) ?_
      refine Eq.symm (Eq.trans (congrArg
        (LinearMap.baseChange (ToType (X.presheaf.stalk x.1)) φ.hom)
        (Eq.trans (congrArg (uLeg V x M) (map_add
          (associatedSheafStalkAddEquiv V.toScheme.toRingedSpace (alpha (V := V)) M x).symm
          w₁ w₂)) (map_add (uLeg V x M) _ _))) (map_add _ _ _))
  | tmul ξ m =>
      obtain ⟨W, hxW, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq V.toScheme.presheaf ξ
      refine Eq.trans (congrArg (uLeg V x N)
        (stalkMap_associatedSheafFunctor_map_germ_tmul V.toScheme.toRingedSpace
          (alpha (V := V)) M x N φ W hxW s m)) ?_
      refine Eq.trans (uLeg_assoc_symm V x N _) ?_
      refine Eq.trans (TensorProduct.congr_tmul (stalkAlgEquiv V x).toLinearEquiv
        (LinearEquiv.refl Γ(X, V) N) _ _) ?_
      refine Eq.symm (Eq.trans (congrArg
        (LinearMap.baseChange (ToType (X.presheaf.stalk x.1)) φ.hom)
        (Eq.trans (uLeg_assoc_symm V x M _)
          (TensorProduct.congr_tmul (stalkAlgEquiv V x).toLinearEquiv
            (LinearEquiv.refl Γ(X, V) M) _ _))) ?_)
      exact LinearMap.baseChange_tmul _ _ _

/-- The inverse of `stalkAddEquivOfIso z e` is the map of stalks at `z` induced by `e.inv`. -/
theorem stalkAddEquivOfIso_symm_apply {T : TopCat.{u}}
    {O : CategoryTheory.Sheaf (Opens.grothendieckTopology T) RingCat.{u}}
    (z : T) {M N : _root_.SheafOfModules.{u} O} (e : M ≅ N)
    (ν : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.val.presheaf z)) :
    (stalkAddEquivOfIso z e).symm ν =
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map
        ((PresheafOfModules.toPresheaf O.obj).map e.inv.val)).hom ν := rfl

/-- The map of stalks at `z` induced by `e.hom` is a left inverse of the inverse of
`stalkAddEquivOfIso z e`. -/
theorem stalkAddEquivOfIso_apply_symm {T : TopCat.{u}}
    {O : CategoryTheory.Sheaf (Opens.grothendieckTopology T) RingCat.{u}}
    (z : T) {M N : _root_.SheafOfModules.{u} O} (e : M ≅ N)
    (ν : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.val.presheaf z)) :
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map
        ((PresheafOfModules.toPresheaf O.obj).map e.hom.val)).hom
        ((stalkAddEquivOfIso z e).symm ν) = ν :=
  Eq.trans (stalkAddEquivOfIso_apply z e _).symm
    ((stalkAddEquivOfIso z e).apply_symm_apply ν)

/-- `stalkAddEquivOfIso z e` is a left inverse of the map of stalks at `z` induced by `e.inv`. -/
theorem stalkAddEquivOfIso_inv_apply {T : TopCat.{u}}
    {O : CategoryTheory.Sheaf (Opens.grothendieckTopology T) RingCat.{u}}
    (z : T) {M N : _root_.SheafOfModules.{u} O} (e : M ≅ N)
    (ν : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.val.presheaf z)) :
    stalkAddEquivOfIso z e
        (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map
          ((PresheafOfModules.toPresheaf O.obj).map e.inv.val)).hom ν) = ν :=
  Eq.trans (congrArg (stalkAddEquivOfIso z e) (stalkAddEquivOfIso_symm_apply z e ν).symm)
    ((stalkAddEquivOfIso z e).apply_symm_apply ν)

/-! ### The four identifications at a point -/

section Concrete
variable {Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} (hVU : V ≤ f ⁻¹ᵁ U)

/-- The stalk at `x` of the degree `-1` term of `associatedNaiveCotangentComplex f hVU` is
additively isomorphic to `𝒪_{X,x} ⊗_{Γ(X,V)} nlSelfModNegOne f hVU`. -/
def uNegOne :
    letI := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        ((associatedNaiveCotangentComplex f hVU).X (-1)).val.presheaf x) ≃+
      (ToType (X.presheaf.stalk x.1) ⊗[Γ(X, V)] nlSelfModNegOne f hVU) :=
  letI := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
  (stalkAddEquivOfIso x (HomologicalComplex.doubleXIso₀
      ((associatedSheafFunctor.{u, u} V.toScheme.toRingedSpace (alpha (V := V))).map
        (nlSelfModD f hVU))
      (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide))).trans
    (uLeg V x (nlSelfModNegOne f hVU))

/-- The stalk at `x` of the degree `0` term of `associatedNaiveCotangentComplex f hVU` is
additively isomorphic to `𝒪_{X,x} ⊗_{Γ(X,V)} nlSelfModZero f hVU`. -/
def uZero :
    letI := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        ((associatedNaiveCotangentComplex f hVU).X 0).val.presheaf x) ≃+
      (ToType (X.presheaf.stalk x.1) ⊗[Γ(X, V)] nlSelfModZero f hVU) :=
  letI := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
  (stalkAddEquivOfIso x (HomologicalComplex.doubleXIso₁
      ((associatedSheafFunctor.{u, u} V.toScheme.toRingedSpace (alpha (V := V))).map
        (nlSelfModD f hVU))
      (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide))).trans
    (uLeg V x (nlSelfModZero f hVU))

/-- The stalk at `x` of the degree `-1` term of `restrictedNaiveCotangentComplex f` is additively
isomorphic to the conormal module of the canonical presentation of `𝒪_{X,x}` over
`(f^{-1}𝒪_Y)_x`. -/
def vNegOne :
    letI := Stacks.RelativeDifferentialStalk.algebraStalk
      (AlgebraicGeometry.inverseImageStructureMap f).hom x.1
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        ((restrictedNaiveCotangentComplex f (V := V)).X (-1)).val.presheaf x) ≃+
      (Algebra.Generators.self
          (ToType (TopCat.Presheaf.stalk ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj
            Y.sheaf).obj x.1))
          (ToType (TopCat.Presheaf.stalk X.sheaf.obj x.1))).toExtension.Cotangent :=
  letI := Stacks.RelativeDifferentialStalk.algebraStalk
    (AlgebraicGeometry.inverseImageStructureMap f).hom x.1
  (restrictStalkAddEquiv V ((naiveCotangentModules f).X (-1)) x).trans
    (stalkLegNegOne ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf) X.sheaf
      (AlgebraicGeometry.inverseImageStructureMap f) x.1)

/-- The stalk at `x` of the degree `0` term of `restrictedNaiveCotangentComplex f` is additively
isomorphic to the cotangent space of the canonical presentation of `𝒪_{X,x}` over
`(f^{-1}𝒪_Y)_x`. -/
def vZero :
    letI := Stacks.RelativeDifferentialStalk.algebraStalk
      (AlgebraicGeometry.inverseImageStructureMap f).hom x.1
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        ((restrictedNaiveCotangentComplex f (V := V)).X 0).val.presheaf x) ≃+
      (Algebra.Generators.self
          (ToType (TopCat.Presheaf.stalk ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj
            Y.sheaf).obj x.1))
          (ToType (TopCat.Presheaf.stalk X.sheaf.obj x.1))).toExtension.CotangentSpace :=
  letI := Stacks.RelativeDifferentialStalk.algebraStalk
    (AlgebraicGeometry.inverseImageStructureMap f).hom x.1
  (restrictStalkAddEquiv V ((naiveCotangentModules f).X 0) x).trans
    (stalkLegZero ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf) X.sheaf
      (AlgebraicGeometry.inverseImageStructureMap f) x.1)

/-- The stalk at `x` of the term of `associatedNaiveCotangentComplex f hVU` in a degree other than
`-1` and `0` is zero. -/
theorem isZero_src (i : ℤ) (h1 : i ≠ -1) (h2 : i ≠ 0) :
    Limits.IsZero
      ((AlgebraicGeometry.SheafOfModules.stalkFunctor V.toScheme.ringCatSheaf x).obj
        ((associatedNaiveCotangentComplex f hVU).X i)) :=
  AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj V.toScheme.ringCatSheaf x _
    (HomologicalComplex.isZero_double_X
      ((associatedSheafFunctor.{u, u} V.toScheme.toRingedSpace (alpha (V := V))).map
        (nlSelfModD f hVU))
      (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) i h1 h2)

/-- The stalk at `x` of the term of `restrictedNaiveCotangentComplex f` in a degree other than `-1`
and `0` is zero. -/
theorem isZero_tgt (i : ℤ) (h1 : i ≠ -1) (h2 : i ≠ 0) :
    Limits.IsZero
      ((AlgebraicGeometry.SheafOfModules.stalkFunctor V.toScheme.ringCatSheaf x).obj
        ((restrictedNaiveCotangentComplex f (V := V)).X i)) := by
  refine AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj
    V.toScheme.ringCatSheaf x _ ?_
  refine (Limits.IsZero.iff_id_eq_zero _).mpr ?_
  refine Eq.trans
    (CategoryTheory.Functor.map_id (Scheme.Modules.restrictFunctor V.ι) _).symm ?_
  refine Eq.trans (congrArg (Scheme.Modules.restrictFunctor V.ι).map
    ((Limits.IsZero.iff_id_eq_zero _).mp
      (Scheme.naiveCotangentComplex_isZero_X f i h1 h2))) ?_
  exact CategoryTheory.Functor.map_zero _ _ _

/-- The identifications `vNegOne` and `vZero` carry the stalk at `x` of the differential of
`restrictedNaiveCotangentComplex f` to the cotangent complex map of the canonical presentation of
`𝒪_{X,x}` over `(f^{-1}𝒪_Y)_x`. -/
theorem tgt_d
    (w : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      ((restrictedNaiveCotangentComplex f (V := V)).X (-1)).val.presheaf x)) :
    letI := Stacks.RelativeDifferentialStalk.algebraStalk
      (AlgebraicGeometry.inverseImageStructureMap f).hom x.1
    vZero V x f
        (((AlgebraicGeometry.SheafOfModules.stalkFunctor V.toScheme.ringCatSheaf x).map
          ((restrictedNaiveCotangentComplex f (V := V)).d (-1) 0)) w) =
      (Algebra.Generators.self
          (ToType (TopCat.Presheaf.stalk ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj
            Y.sheaf).obj x.1))
          (ToType (TopCat.Presheaf.stalk X.sheaf.obj x.1))).toExtension.cotangentComplex
        (vNegOne V x f w) := by
  let := Stacks.RelativeDifferentialStalk.algebraStalk
    (AlgebraicGeometry.inverseImageStructureMap f).hom x.1
  refine Eq.trans (congrArg (stalkLegZero
      ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf) X.sheaf
      (AlgebraicGeometry.inverseImageStructureMap f) x.1)
    (restrictStalkAddEquiv_naturality V ((naiveCotangentModules f).X (-1)) x
      ((naiveCotangentModules f).d (-1) 0) w)) ?_
  exact stalkLeg_d ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf) X.sheaf
    (AlgebraicGeometry.inverseImageStructureMap f) x.1 _

end Concrete

end Stacks.NaiveCotangentAffineStalkComparison

end

end
