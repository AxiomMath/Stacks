module

public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentAffineStalkComparison

/-!
# Stacks 0D0I: the canonical map is an isomorphism in the derived category

Let `f : X ⟶ Y` be a morphism of schemes and let `Spec R = U ⊆ Y` and `Spec A = V ⊆ X` be affine
opens with `V ⊆ f^{-1}U`.  This file proves Stacks 0D0I: the canonical map

`(NL_{A/R})~ ⟶ NL_{X/Y}|_V`

of `Stacks.NaiveCotangentAffineMap.comparisonMap` is an isomorphism in `D(𝒪_V)`.

The proof is the one of the source.  Quasi-isomorphy is a stalkwise condition
(`AlgebraicGeometry.SheafOfModules.quasiIso_of_forall_stalk_quasiIso`, Stacks 08TL), and at a
point `x` of `V` the two stalk complexes are `NL_{A/R} ⊗_A 𝒪_{X,x}` and
`NL_{𝒪_{X,x}/(f^{-1}𝒪_Y)_x}`: the first by clause (3) of Stacks 01BH, the second by Stacks 0D09,
through the identifications of
`StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentAffineStalkComparison`.  Under those
identifications the stalk of the comparison map is
`NaiveCotangent.nlExtensionBaseChangeMap` of the morphism of extensions
`Stacks.NaiveCotangentAffineComparison.canonicalStalkHom`, which is a quasi-isomorphism by
`Stacks.NaiveCotangentAffineComparison.isQuasiIso_nlExtensionBaseChangeMap_canonicalStalkHom` —
and that is where the affineness of `U` and `V` is used, and the only place it is used.

## Main results

* `Stacks.NaiveCotangentAffineQuasiIso.quasiIso_comparisonMap`: for affine `U` and `V`, the
  canonical map `(NL_{A/R})~ ⟶ NL_{X/Y}|_V` is a quasi-isomorphism.
* `Stacks.NaiveCotangentAffineQuasiIso.hp_tmul` and
  `Stacks.NaiveCotangentAffineQuasiIso.hq_tmul`: under the identifications above, the stalk of
  the canonical map carries `germ_x(s) ⊗ m` to `germ_x(s) • Cotangent.map canonicalStalkHom m`,
  which is the value of `NaiveCotangent.nlExtensionBaseChangeMap`.
* `Stacks.NaiveCotangentAffineQuasiIso.src_d`: the differential of the associated complex, read
  through the same identifications, is the base change of the differential of `NL_{A/R}`.

## Implementation notes

**Supply every argument explicitly; never a placeholder.**  Each of the long germ chains here is
a composition of ten named lemmas, and at every step the elaborator must join a term produced by
one lemma to the argument slot of the next.  Left to infer an argument, the unifier falls into
the colimit data that a stalk carries — whose definition is not exposed, so it cannot reduce —
and spends the whole 200000-heartbeat budget.  Written out, each step costs a few thousand.  In
particular the implicit sheaf of rings of a generic stalk lemma is always given by name here
(`(O := V.toScheme.ringCatSheaf)`): left implicit, the *point* becomes a metavariable and the
same explosion follows.

**The two spellings.**  `Stacks.NaiveCotangentAffineQuasiIso.stalkFunctor_map_apply` and
`Stacks.NaiveCotangentAffineQuasiIso.stalkMap_apply` are the bridges between the three spellings
of the stalk of a morphism of sheaves of modules — `(stalkFunctor O x).map`,
`AlgebraicGeometry.SheafOfModules.stalkMap`, and the stalk of the underlying morphism of
presheaves of abelian groups.  They hold by `rfl` over abstract data, and are inserted explicitly
wherever a chain crosses from one to another rather than left to `isDefEq`, which does not
survive the crossing at the concrete presentation.  For the same reason
`Stacks.NaiveCotangentAffineQuasiIso.quasiIso_comparisonMap` opens with a block of `let`s whose
types are ascribed: `X.presheaf.stalk x` and `TopCat.Presheaf.stalk X.sheaf.obj x` are one type
with two spellings, and an `Algebra` instance found for one is not found for the other.

## References

* [Stacks Project, Tag 0D0I](https://stacks.math.columbia.edu/tag/0D0I)
* [Stacks Project, Tag 0D09](https://stacks.math.columbia.edu/tag/0D09), the stalk of the naive
  cotangent complex of a morphism of sheaves of rings.
* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH), the sheaf associated to
  a module, its mapping property and its stalks.
* [Stacks Project, Tag 08TL](https://stacks.math.columbia.edu/tag/08TL), the stalkwise criterion
  for quasi-isomorphy.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

universe u

noncomputable section

namespace Stacks.NaiveCotangentAffineQuasiIso

open Stacks.NaiveCotangentAffineIso Stacks.NaiveCotangentAffineMap Stacks.AssociatedSheaf
open Stacks.NaiveCotangentAffineStalkLegs Stacks.NaiveCotangentAffineStalkComparison
open Stacks.SheafOfModules

/-- The stalk of a morphism of sheaves of modules under `stalkFunctor` agrees with the stalk of
the underlying morphism of presheaves of abelian groups. -/
theorem stalkFunctor_map_apply {T : TopCat.{u}}
    {O : CategoryTheory.Sheaf (Opens.grothendieckTopology T) RingCat.{u}}
    (z : T) {M N : _root_.SheafOfModules.{u} O} (ψ : M ⟶ N)
    (ω : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf z)) :
    ((AlgebraicGeometry.SheafOfModules.stalkFunctor O z).map ψ) ω =
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map
        ((PresheafOfModules.toPresheaf O.obj).map ψ.val)).hom ω := rfl

variable {X : Scheme.{u}} (V : X.Opens) (x : V) {Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens}
  (hVU : V ≤ f ⁻¹ᵁ U)

/-- `uNegOne` is the identification of the stalk of the degree `-1` term of the double complex
with the stalk of the sheaf associated to `nlSelfModNegOne f hVU`, followed by `uLeg`. -/
theorem uNegOne_apply
    (w : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      ((associatedNaiveCotangentComplex f hVU).X (-1)).val.presheaf x)) :
    letI := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
    uNegOne V x f hVU w =
      uLeg V x (nlSelfModNegOne f hVU)
        (stalkAddEquivOfIso x (HomologicalComplex.doubleXIso₀
          ((associatedSheafFunctor.{u, u} V.toScheme.toRingedSpace (alpha (V := V))).map
            (nlSelfModD f hVU))
          (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)) w) := rfl

/-- `uZero` is the identification of the stalk of the degree `0` term of the double complex
with the stalk of the sheaf associated to `nlSelfModZero f hVU`, followed by `uLeg`. -/
theorem uZero_apply
    (w : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      ((associatedNaiveCotangentComplex f hVU).X 0).val.presheaf x)) :
    letI := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
    uZero V x f hVU w =
      uLeg V x (nlSelfModZero f hVU)
        (stalkAddEquivOfIso x (HomologicalComplex.doubleXIso₁
          ((associatedSheafFunctor.{u, u} V.toScheme.toRingedSpace (alpha (V := V))).map
            (nlSelfModD f hVU))
          (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide)) w) := rfl

/-- Under `uNegOne` and `uZero`, the stalk at `x` of the differential of
`associatedNaiveCotangentComplex f hVU` is the base change to `𝒪_{X,x}` of `nlSelfModD f hVU`. -/
theorem src_d
    (w : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      ((associatedNaiveCotangentComplex f hVU).X (-1)).val.presheaf x)) :
    letI := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
    uZero V x f hVU
        (((AlgebraicGeometry.SheafOfModules.stalkFunctor V.toScheme.ringCatSheaf x).map
          ((associatedNaiveCotangentComplex f hVU).d (-1) 0)) w) =
      (LinearMap.baseChange (ToType (X.presheaf.stalk x.1)) (nlSelfModD f hVU).hom)
        (uNegOne V x f hVU w) := by
  let := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
  have hd := HomologicalComplex.double_d
    ((associatedSheafFunctor.{u, u} V.toScheme.toRingedSpace (alpha (V := V))).map
      (nlSelfModD f hVU))
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide)
  refine Eq.trans (congrArg (uZero V x f hVU)
    (stalkFunctor_map_apply (O := V.toScheme.ringCatSheaf) x
      ((associatedNaiveCotangentComplex f hVU).d (-1) 0) w)) ?_
  refine Eq.trans (congrArg (uZero V x f hVU) (congrArg
    (fun ψ : (associatedNaiveCotangentComplex f hVU).X (-1) ⟶
        (associatedNaiveCotangentComplex f hVU).X 0 =>
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf V.toScheme.ringCatSheaf.obj).map ψ.val)).hom w) hd)) ?_
  refine Eq.trans (congrArg (uZero V x f hVU)
    (stalkMap_comp_apply (O := V.toScheme.ringCatSheaf) x
      (HomologicalComplex.doubleXIso₀
        ((associatedSheafFunctor.{u, u} V.toScheme.toRingedSpace (alpha (V := V))).map
          (nlSelfModD f hVU))
        (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)).hom
      (((associatedSheafFunctor.{u, u} V.toScheme.toRingedSpace (alpha (V := V))).map
          (nlSelfModD f hVU)) ≫
        (HomologicalComplex.doubleXIso₁
          ((associatedSheafFunctor.{u, u} V.toScheme.toRingedSpace (alpha (V := V))).map
            (nlSelfModD f hVU))
          (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide)).inv) w)) ?_
  refine Eq.trans (congrArg (uZero V x f hVU)
    (stalkMap_comp_apply (O := V.toScheme.ringCatSheaf) x
      ((associatedSheafFunctor.{u, u} V.toScheme.toRingedSpace (alpha (V := V))).map
        (nlSelfModD f hVU))
      (HomologicalComplex.doubleXIso₁
        ((associatedSheafFunctor.{u, u} V.toScheme.toRingedSpace (alpha (V := V))).map
          (nlSelfModD f hVU))
        (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide)).inv _)) ?_
  refine Eq.trans (uZero_apply V x f hVU _) ?_
  refine Eq.trans (congrArg (uLeg V x (nlSelfModZero f hVU))
    (stalkAddEquivOfIso_inv_apply (O := V.toScheme.ringCatSheaf) x
      (HomologicalComplex.doubleXIso₁
        ((associatedSheafFunctor.{u, u} V.toScheme.toRingedSpace (alpha (V := V))).map
          (nlSelfModD f hVU))
        (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide))
      (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf V.toScheme.ringCatSheaf.obj).map
        ((associatedSheafFunctor.{u, u} V.toScheme.toRingedSpace (alpha (V := V))).map
          (nlSelfModD f hVU)).val)).hom
      (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf V.toScheme.ringCatSheaf.obj).map
          (HomologicalComplex.doubleXIso₀
            ((associatedSheafFunctor.{u, u} V.toScheme.toRingedSpace (alpha (V := V))).map
              (nlSelfModD f hVU))
            (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)).hom.val)).hom w)))) ?_
  refine Eq.trans (uLeg_map V x (nlSelfModNegOne f hVU) (nlSelfModZero f hVU)
    (nlSelfModD f hVU) (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf V.toScheme.ringCatSheaf.obj).map
        (HomologicalComplex.doubleXIso₀
          ((associatedSheafFunctor.{u, u} V.toScheme.toRingedSpace (alpha (V := V))).map
            (nlSelfModD f hVU))
          (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)).hom.val)).hom w)) ?_
  refine Eq.trans (congrArg
    (LinearMap.baseChange (ToType (X.presheaf.stalk x.1)) (nlSelfModD f hVU).hom)
    (congrArg (uLeg V x (nlSelfModNegOne f hVU))
      (stalkAddEquivOfIso_apply (O := V.toScheme.ringCatSheaf) x
        (HomologicalComplex.doubleXIso₀
          ((associatedSheafFunctor.{u, u} V.toScheme.toRingedSpace (alpha (V := V))).map
            (nlSelfModD f hVU))
          (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)) w).symm)) ?_
  exact congrArg
    (LinearMap.baseChange (ToType (X.presheaf.stalk x.1)) (nlSelfModD f hVU).hom)
    (uNegOne_apply V x f hVU w).symm

/-- `vNegOne` is the restriction of stalks to `V` followed by `stalkLegNegOne`. -/
theorem vNegOne_apply
    (ζ : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      ((restrictedNaiveCotangentComplex f (V := V)).X (-1)).val.presheaf x)) :
    letI := Stacks.RelativeDifferentialStalk.algebraStalk
      (AlgebraicGeometry.inverseImageStructureMap f).hom x.1
    vNegOne V x f ζ =
      stalkLegNegOne ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf) X.sheaf
        (AlgebraicGeometry.inverseImageStructureMap f) x.1
        (restrictStalkAddEquiv V ((naiveCotangentModules f).X (-1)) x ζ) := rfl

/-- `AlgebraicGeometry.SheafOfModules.stalkMap` agrees with the stalk of the underlying morphism
of presheaves of abelian groups. -/
theorem stalkMap_apply {T : TopCat.{u}}
    {O : CategoryTheory.Sheaf (Opens.grothendieckTopology T) RingCat.{u}}
    (z : T) {M N : _root_.SheafOfModules.{u} O} (ψ : M ⟶ N)
    (ω : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf z)) :
    (AlgebraicGeometry.SheafOfModules.stalkMap O z ψ) ω =
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map
        ((PresheafOfModules.toPresheaf O.obj).map ψ.val)).hom ω := rfl

/-- The inverse of `uNegOne` is the inverse of `uLeg` followed by the inverse of the
identification of the degree `-1` term of the double complex. -/
theorem uNegOne_symm_apply
    (ν : letI := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
      ToType (X.presheaf.stalk x.1) ⊗[Γ(X, V)] nlSelfModNegOne f hVU) :
    letI := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
    letI := stalkAlgebra V.toScheme.toRingedSpace (alpha (V := V)) x
    (uNegOne V x f hVU).symm ν =
      (stalkAddEquivOfIso x (HomologicalComplex.doubleXIso₀
          ((associatedSheafFunctor.{u, u} V.toScheme.toRingedSpace (alpha (V := V))).map
            (nlSelfModD f hVU))
          (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide))).symm
        ((uLeg V x (nlSelfModNegOne f hVU)).symm ν) := rfl

/-- The stalk of `e.hom ≫ associatedSheafDesc g` carries the preimage under `uLeg` and `e` of
`germ_x(s) ⊗ m` to `germ_x(s) • germ_x(g m)`. -/
private theorem stalkFunctor_map_hom_desc_symm_tmul {M : ModuleCat.{u} Γ(X, V)}
    {𝒢 : _root_.SheafOfModules.{u} (structureSheafRing V.toScheme.toRingedSpace)}
    {N : _root_.SheafOfModules.{u} V.toScheme.ringCatSheaf}
    (e : N ≅ (associatedSheafFunctor.{u, u} V.toScheme.toRingedSpace (alpha (V := V))).obj M)
    (g : M ⟶ (globalSectionsFunctor.{u, u} V.toScheme.toRingedSpace (alpha (V := V))).obj 𝒢)
    (W : V.toScheme.Opens) (hxW : x ∈ W) (s : V.toScheme.presheaf.obj (op W)) (m : M) :
    letI := stalkAlgebra V.toScheme.toRingedSpace (alpha (V := V)) x
    ((AlgebraicGeometry.SheafOfModules.stalkFunctor V.toScheme.ringCatSheaf x).map
        (e.hom ≫ associatedSheafDesc V.toScheme.toRingedSpace (alpha (V := V)) M 𝒢 g))
      ((stalkAddEquivOfIso x e).symm ((uLeg V x M).symm
        (stalkAlgEquiv V x ((V.toScheme.presheaf.germ W x hxW).hom s) ⊗ₜ[Γ(X, V)] m))) =
      (AlgebraicGeometry.SheafOfModules.stalkMap V.toScheme.ringCatSheaf x
          (associatedSheafDesc V.toScheme.toRingedSpace (alpha (V := V)) M 𝒢 g)).hom
        ((associatedSheafStalkAddEquiv V.toScheme.toRingedSpace (alpha (V := V)) M x).symm
          ((V.toScheme.presheaf.germ W x hxW).hom s ⊗ₜ[Γ(X, V)] m)) := by
  let := stalkAlgebra V.toScheme.toRingedSpace (alpha (V := V)) x
  refine Eq.trans (stalkFunctor_map_apply (O := V.toScheme.ringCatSheaf) x
    (e.hom ≫ associatedSheafDesc V.toScheme.toRingedSpace (alpha (V := V)) M 𝒢 g) _) ?_
  refine Eq.trans (stalkMap_comp_apply (O := V.toScheme.ringCatSheaf) x e.hom
    (associatedSheafDesc V.toScheme.toRingedSpace (alpha (V := V)) M 𝒢 g) _) ?_
  refine Eq.trans (congrArg (fun ν => ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf V.toScheme.ringCatSheaf.obj).map
        (associatedSheafDesc V.toScheme.toRingedSpace (alpha (V := V)) M 𝒢 g).val)).hom ν)
    (Eq.trans (stalkAddEquivOfIso_apply_symm (O := V.toScheme.ringCatSheaf) x e _)
      (uLeg_symm_tmul V x M W hxW s m))) ?_
  exact (stalkMap_apply (O := V.toScheme.ringCatSheaf) x
    (associatedSheafDesc V.toScheme.toRingedSpace (alpha (V := V)) M 𝒢 g) _).symm

/-- If `v (Φ (u.symm ζ)) = Ψ ζ` for all `ζ`, then `Φ z = v.symm (Ψ (u z))`. -/
private theorem apply_eq_symm_of_forall {A B C D : Type*} [Add A] [Add B] [Add C] [Add D]
    (u : A ≃+ C) (v : B ≃+ D) (Φ : A → B) (Ψ : C → D) (h : ∀ ζ, v (Φ (u.symm ζ)) = Ψ ζ) (z : A) :
    Φ z = v.symm (Ψ (u z)) := by
  rw [← h, u.symm_apply_apply, v.symm_apply_apply]

/-- An identity `v (Φ (u.symm ζ)) = F ζ` between additive maps holds on a tensor product as soon
as it holds on pure tensors. -/
private theorem apply_symm_eq_of_forall_tmul {R T M A B D : Type*} [CommSemiring R]
    [AddCommMonoid T] [AddCommMonoid M] [Module R T] [Module R M] [AddCommMonoid A]
    [AddCommMonoid B] [AddCommMonoid D] {G H : Type*} [FunLike G A B] [AddMonoidHomClass G A B]
    [FunLike H (T ⊗[R] M) D] [AddMonoidHomClass H (T ⊗[R] M) D]
    (u : A ≃+ T ⊗[R] M) (Φ : G) (v : B ≃+ D) (F : H)
    (h : ∀ t m, v (Φ (u.symm (t ⊗ₜ[R] m))) = F (t ⊗ₜ[R] m)) (ζ : T ⊗[R] M) :
    v (Φ (u.symm ζ)) = F ζ := by
  induction ζ using TensorProduct.induction_on with
  | zero => simp
  | add ζ₁ ζ₂ h₁ h₂ => simp [h₁, h₂]
  | tmul t m => exact h t m

/-- In degree `-1`, under `uNegOne` and `vNegOne`, the stalk of `comparisonMap f hVU` carries
`germ_x(s) ⊗ m` to `germ_x(s) • Cotangent.map canonicalStalkHom m`. -/
theorem hp_tmul (W : V.toScheme.Opens) (hxW : x ∈ W)
    (s : V.toScheme.presheaf.obj (op W)) (m : nlSelfModNegOne f hVU) :
    letI := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
    letI := stalkAlgebra V.toScheme.toRingedSpace (alpha (V := V)) x
    letI := Stacks.NaiveCotangentAffineStalk.algebraStalkInverseImage f (hVU x.2)
    letI := Stacks.NaiveCotangentAffineStalk.algebraStalkInverseImageStructureMap f (x := x.1)
    letI := Stacks.NaiveCotangentAffineStalk.algebraStalkOfAppLE f hVU x.2
    letI : Algebra (ToType (TopCat.Presheaf.stalk
          ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).obj x.1))
        (ToType (TopCat.Presheaf.stalk X.sheaf.obj x.1)) :=
      Stacks.RelativeDifferentialStalk.algebraStalk
        (AlgebraicGeometry.inverseImageStructureMap f).hom x.1
    haveI : IsScalarTower Γ(Y, U) Γ(X, V) ↑(X.presheaf.stalk x.1) :=
      Stacks.NaiveCotangentAffineStalk.isScalarTower_appLE f hVU x.2
    haveI : IsScalarTower Γ(Y, U)
        ↑(TopCat.Presheaf.stalk ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj
          Y.sheaf).obj x.1) ↑(X.presheaf.stalk x.1) :=
      Stacks.NaiveCotangentAffineStalk.isScalarTower_stalkInverseImage f hVU x.2 (hVU x.2)
    vNegOne V x f
        (((AlgebraicGeometry.SheafOfModules.stalkFunctor V.toScheme.ringCatSheaf x).map
          ((comparisonMap f hVU).f (-1)))
          ((uNegOne V x f hVU).symm
            (stalkAlgEquiv V x ((V.toScheme.presheaf.germ W x hxW).hom s) ⊗ₜ[Γ(X, V)] m))) =
      (show ToType (TopCat.Presheaf.stalk X.sheaf.obj x.1) from
          stalkAlgEquiv V x ((V.toScheme.presheaf.germ W x hxW).hom s)) •
        (show (Algebra.Generators.self
            (ToType (TopCat.Presheaf.stalk ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj
              Y.sheaf).obj x.1))
            (ToType (TopCat.Presheaf.stalk X.sheaf.obj x.1))).toExtension.Cotangent from
          Algebra.Extension.Cotangent.map
            (Stacks.NaiveCotangentAffineComparison.canonicalStalkHom f hVU x.2 (hVU x.2)) m) := by
  let := Stacks.NaiveCotangentAffineComparison.algebraAppLE' f hVU
  let := Stacks.NaiveCotangentAffineComparison.algebraBaseSection f hVU
  let := Stacks.NaiveCotangentAffineSections.algebraSections f V
  have _ := Stacks.NaiveCotangentAffineComparison.isScalarTower_baseSection f hVU
  let := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
  let := stalkAlgebra V.toScheme.toRingedSpace (alpha (V := V)) x
  let := Stacks.NaiveCotangentAffineStalk.algebraStalkInverseImage f (hVU x.2)
  let := Stacks.NaiveCotangentAffineStalk.algebraStalkInverseImageStructureMap f (x := x.1)
  let := Stacks.NaiveCotangentAffineStalk.algebraStalkOfAppLE f hVU x.2
  let _ : Algebra (ToType (TopCat.Presheaf.stalk
        ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).obj x.1))
      (ToType (TopCat.Presheaf.stalk X.sheaf.obj x.1)) :=
    Stacks.RelativeDifferentialStalk.algebraStalk
      (AlgebraicGeometry.inverseImageStructureMap f).hom x.1
  have _ : IsScalarTower Γ(Y, U) Γ(X, V) ↑(X.presheaf.stalk x.1) :=
    Stacks.NaiveCotangentAffineStalk.isScalarTower_appLE f hVU x.2
  have _ : IsScalarTower Γ(Y, U)
      ↑(TopCat.Presheaf.stalk ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj
        Y.sheaf).obj x.1) ↑(X.presheaf.stalk x.1) :=
    Stacks.NaiveCotangentAffineStalk.isScalarTower_stalkInverseImage f hVU x.2 (hVU x.2)
  refine Eq.trans (congrArg (vNegOne V x f) (congrArg
    (fun ψ : (associatedNaiveCotangentComplex f hVU).X (-1) ⟶
        (restrictedNaiveCotangentComplex f (V := V)).X (-1) =>
      ((AlgebraicGeometry.SheafOfModules.stalkFunctor V.toScheme.ringCatSheaf x).map ψ)
        ((uNegOne V x f hVU).symm
          (stalkAlgEquiv V x ((V.toScheme.presheaf.germ W x hxW).hom s) ⊗ₜ[Γ(X, V)] m)))
    (wholeStepMap_f_negOne V (naiveCotangentModules f) (nlSelfModD f hVU)
      (descDatumNegOne f hVU) (descDatumZero f hVU) (descDatum_comm f hVU)
      (Scheme.naiveCotangentComplex_isZero_X f 1 (by decide) (by decide))))) ?_
  refine Eq.trans (congrArg (vNegOne V x f) (Eq.trans
    (stalkFunctor_map_hom_desc_symm_tmul V x
      (HomologicalComplex.doubleXIso₀
        ((associatedSheafFunctor.{u, u} V.toScheme.toRingedSpace (alpha (V := V))).map
          (nlSelfModD f hVU))
        (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide))
      (descDatumNegOne f hVU ≫ restrictTop V ((naiveCotangentModules f).X (-1))) W hxW s m)
    (stalkMap_associatedSheafDesc_germ_tmul V.toScheme.toRingedSpace (alpha (V := V))
      (nlSelfModNegOne f hVU)
      ((Scheme.Modules.restrictFunctor V.ι).obj ((naiveCotangentModules f).X (-1))) x
      (descDatumNegOne f hVU ≫ restrictTop V ((naiveCotangentModules f).X (-1)))
      W hxW s m))) ?_
  refine Eq.trans (vNegOne_apply V x f _) ?_
  refine Eq.trans (congrArg (stalkLegNegOne ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj
      Y.sheaf) X.sheaf
      (AlgebraicGeometry.inverseImageStructureMap f) x.1)
    (restrictTop_germ_smul V ((naiveCotangentModules f).X (-1)) x W hxW s
      (descDatumNegOne f hVU m))) ?_
  refine Eq.trans (stalkLegNegOne_germ_smul ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj
      Y.sheaf) X.sheaf
    (AlgebraicGeometry.inverseImageStructureMap f) x.1 (V.ι ''ᵁ W)
    (show (x : X) ∈ V.ι ''ᵁ W by simpa using hxW) s
    (((Scheme.Modules.restrictFunctor V.ι).obj ((naiveCotangentModules f).X (-1))).val.map
      (homOfLE (le_top (a := W))).op
      (restrictTop V ((naiveCotangentModules f).X (-1)) (descDatumNegOne f hVU m)))) ?_
  refine Eq.trans ?_ (congrArg (fun r : ToType (TopCat.Presheaf.stalk X.sheaf.obj x.1) =>
      r • (show (Algebra.Generators.self
            (ToType (TopCat.Presheaf.stalk ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj
                Y.sheaf).obj x.1))
            (ToType (TopCat.Presheaf.stalk X.sheaf.obj x.1))).toExtension.Cotangent from
        Algebra.Extension.Cotangent.map
          (Stacks.NaiveCotangentAffineComparison.canonicalStalkHom f hVU x.2 (hVU x.2)) m))
    (stalkAlgEquiv_germ V x W hxW s)).symm
  refine congrArg (fun c : (Algebra.Generators.self
            (ToType (TopCat.Presheaf.stalk ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj
                Y.sheaf).obj x.1))
            (ToType (TopCat.Presheaf.stalk X.sheaf.obj x.1))).toExtension.Cotangent =>
    (show ToType (TopCat.Presheaf.stalk X.sheaf.obj x.1) from
      (TopCat.Presheaf.germ X.sheaf.obj (V.ι ''ᵁ W) x.1
        (show (x : X) ∈ V.ι ''ᵁ W by simpa using hxW)).hom s) • c) ?_
  refine Eq.trans (congrArg (stalkLegNegOne ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj
      Y.sheaf) X.sheaf
      (AlgebraicGeometry.inverseImageStructureMap f) x.1)
    (Eq.trans (TopCat.Presheaf.germ_res_apply
        ((naiveCotangentModules f).X (-1)).val.presheaf
        (V.ι.opensFunctor.map (homOfLE (le_top (a := W)))) x.1
        (show (x : X) ∈ V.ι ''ᵁ W by simpa using hxW)
        (restrictTop V ((naiveCotangentModules f).X (-1)) (descDatumNegOne f hVU m)))
      (TopCat.Presheaf.germ_res_apply ((naiveCotangentModules f).X (-1)).val.presheaf
        (eqToHom V.ι_image_top) x.1 (show (x : X) ∈ V.ι ''ᵁ ⊤ by simp)
        (descDatumNegOne f hVU m)))) ?_
  refine Eq.trans (congrArg (fun t : Γ((naiveCotangentModules f).X (-1), V) =>
      stalkLegNegOne ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf) X.sheaf
        (AlgebraicGeometry.inverseImageStructureMap f) x.1
        ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          ((naiveCotangentModules f).X (-1)).val.presheaf V x.1 x.2).hom t))
    (ConcreteCategory.congr_arg (legNegOne (V := V) f) (DFunLike.congr_fun
      (Stacks.NaiveCotangentAffineComparison.sectionsBaseComparison_f₁ f hVU) m))) ?_
  refine Eq.trans (stalkLegNegOne_germ_sectionsConormalComparison ((TopCat.Sheaf.pullback
      CommRingCat.{u} f.base).obj Y.sheaf) X.sheaf
    (AlgebraicGeometry.inverseImageStructureMap f) x.1 V x.2
    (Algebra.Extension.Cotangent.map
      (Stacks.NaiveCotangentAffineComparison.baseChangeSelfHom
        (R := Γ(Y, U)) (R' := ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj
            Y.sheaf).obj.obj (op V)))
        (A := ↑(X.sheaf.obj.obj (op V)))) m)) ?_
  exact Stacks.NaiveCotangentAffineIso.cotangentMap_germSelfHom_eq_canonicalStalkHom
    f hVU x.2 (hVU x.2) m

/-- The inverse of `uZero` is the inverse of `uLeg` followed by the inverse of the
identification of the degree `0` term of the double complex. -/
theorem uZero_symm_apply
    (ν : letI := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
      ToType (X.presheaf.stalk x.1) ⊗[Γ(X, V)] nlSelfModZero f hVU) :
    letI := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
    letI := stalkAlgebra V.toScheme.toRingedSpace (alpha (V := V)) x
    (uZero V x f hVU).symm ν =
      (stalkAddEquivOfIso x (HomologicalComplex.doubleXIso₁
          ((associatedSheafFunctor.{u, u} V.toScheme.toRingedSpace (alpha (V := V))).map
            (nlSelfModD f hVU))
          (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide))).symm
        ((uLeg V x (nlSelfModZero f hVU)).symm ν) := rfl

/-- `vZero` is the restriction of stalks to `V` followed by `stalkLegZero`. -/
theorem vZero_apply
    (ζ : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      ((restrictedNaiveCotangentComplex f (V := V)).X 0).val.presheaf x)) :
    letI := Stacks.RelativeDifferentialStalk.algebraStalk
      (AlgebraicGeometry.inverseImageStructureMap f).hom x.1
    vZero V x f ζ =
      stalkLegZero ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf) X.sheaf
        (AlgebraicGeometry.inverseImageStructureMap f) x.1
        (restrictStalkAddEquiv V ((naiveCotangentModules f).X 0) x ζ) := rfl

/-- In degree `0`, under `uZero` and `vZero`, the stalk of `comparisonMap f hVU` carries
`germ_x(s) ⊗ m` to `germ_x(s) • CotangentSpace.map canonicalStalkHom m`. -/
theorem hq_tmul (W : V.toScheme.Opens) (hxW : x ∈ W)
    (s : V.toScheme.presheaf.obj (op W)) (m : nlSelfModZero f hVU) :
    letI := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
    letI := stalkAlgebra V.toScheme.toRingedSpace (alpha (V := V)) x
    letI : DecidableEq (OrderDual (TopologicalSpace.OpenNhds x.1)) := Classical.decEq _
    letI := Stacks.NaiveCotangentAffineStalk.algebraStalkInverseImage f (hVU x.2)
    letI := Stacks.NaiveCotangentAffineStalk.algebraStalkInverseImageStructureMap f (x := x.1)
    letI := Stacks.NaiveCotangentAffineStalk.algebraStalkOfAppLE f hVU x.2
    letI : Algebra (ToType (TopCat.Presheaf.stalk
          ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).obj x.1))
        (ToType (TopCat.Presheaf.stalk X.sheaf.obj x.1)) :=
      Stacks.RelativeDifferentialStalk.algebraStalk
        (AlgebraicGeometry.inverseImageStructureMap f).hom x.1
    haveI : IsScalarTower Γ(Y, U) Γ(X, V) ↑(X.presheaf.stalk x.1) :=
      Stacks.NaiveCotangentAffineStalk.isScalarTower_appLE f hVU x.2
    haveI : IsScalarTower Γ(Y, U)
        ↑(TopCat.Presheaf.stalk ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj
          Y.sheaf).obj x.1) ↑(X.presheaf.stalk x.1) :=
      Stacks.NaiveCotangentAffineStalk.isScalarTower_stalkInverseImage f hVU x.2 (hVU x.2)
    vZero V x f
        (((AlgebraicGeometry.SheafOfModules.stalkFunctor V.toScheme.ringCatSheaf x).map
          ((comparisonMap f hVU).f 0))
          ((uZero V x f hVU).symm
            (stalkAlgEquiv V x ((V.toScheme.presheaf.germ W x hxW).hom s) ⊗ₜ[Γ(X, V)] m))) =
      (show ToType (TopCat.Presheaf.stalk X.sheaf.obj x.1) from
          stalkAlgEquiv V x ((V.toScheme.presheaf.germ W x hxW).hom s)) •
        (show (Algebra.Generators.self
            (ToType (TopCat.Presheaf.stalk ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj
              Y.sheaf).obj x.1))
            (ToType (TopCat.Presheaf.stalk X.sheaf.obj x.1))).toExtension.CotangentSpace from
          Algebra.Extension.CotangentSpace.map
            (Stacks.NaiveCotangentAffineComparison.canonicalStalkHom f hVU x.2 (hVU x.2)) m) := by
  let := Stacks.NaiveCotangentAffineComparison.algebraAppLE' f hVU
  let := Stacks.NaiveCotangentAffineComparison.algebraBaseSection f hVU
  let := Stacks.NaiveCotangentAffineSections.algebraSections f V
  have _ := Stacks.NaiveCotangentAffineComparison.isScalarTower_baseSection f hVU
  let := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
  let := stalkAlgebra V.toScheme.toRingedSpace (alpha (V := V)) x
  let _ : DecidableEq (OrderDual (TopologicalSpace.OpenNhds x.1)) := Classical.decEq _
  let := Stacks.NaiveCotangentAffineStalk.algebraStalkInverseImage f (hVU x.2)
  let := Stacks.NaiveCotangentAffineStalk.algebraStalkInverseImageStructureMap f (x := x.1)
  let := Stacks.NaiveCotangentAffineStalk.algebraStalkOfAppLE f hVU x.2
  let _ : Algebra (ToType (TopCat.Presheaf.stalk
        ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).obj x.1))
      (ToType (TopCat.Presheaf.stalk X.sheaf.obj x.1)) :=
    Stacks.RelativeDifferentialStalk.algebraStalk
      (AlgebraicGeometry.inverseImageStructureMap f).hom x.1
  have _ : IsScalarTower Γ(Y, U) Γ(X, V) ↑(X.presheaf.stalk x.1) :=
    Stacks.NaiveCotangentAffineStalk.isScalarTower_appLE f hVU x.2
  have _ : IsScalarTower Γ(Y, U)
      ↑(TopCat.Presheaf.stalk ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj
        Y.sheaf).obj x.1) ↑(X.presheaf.stalk x.1) :=
    Stacks.NaiveCotangentAffineStalk.isScalarTower_stalkInverseImage f hVU x.2 (hVU x.2)
  refine Eq.trans (congrArg (vZero V x f) (congrArg
    (fun ψ : (associatedNaiveCotangentComplex f hVU).X 0 ⟶
        (restrictedNaiveCotangentComplex f (V := V)).X 0 =>
      ((AlgebraicGeometry.SheafOfModules.stalkFunctor V.toScheme.ringCatSheaf x).map ψ)
        ((uZero V x f hVU).symm
          (stalkAlgEquiv V x ((V.toScheme.presheaf.germ W x hxW).hom s) ⊗ₜ[Γ(X, V)] m)))
    (wholeStepMap_f_zero V (naiveCotangentModules f) (nlSelfModD f hVU)
      (descDatumNegOne f hVU) (descDatumZero f hVU) (descDatum_comm f hVU)
      (Scheme.naiveCotangentComplex_isZero_X f 1 (by decide) (by decide))))) ?_
  refine Eq.trans (congrArg (vZero V x f) (Eq.trans
    (stalkFunctor_map_hom_desc_symm_tmul V x
      (HomologicalComplex.doubleXIso₁
        ((associatedSheafFunctor.{u, u} V.toScheme.toRingedSpace (alpha (V := V))).map
          (nlSelfModD f hVU))
        (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide))
      (descDatumZero f hVU ≫ restrictTop V ((naiveCotangentModules f).X 0)) W hxW s m)
    (stalkMap_associatedSheafDesc_germ_tmul V.toScheme.toRingedSpace (alpha (V := V))
      (nlSelfModZero f hVU)
      ((Scheme.Modules.restrictFunctor V.ι).obj ((naiveCotangentModules f).X 0)) x
      (descDatumZero f hVU ≫ restrictTop V ((naiveCotangentModules f).X 0))
      W hxW s m))) ?_
  refine Eq.trans (vZero_apply V x f _) ?_
  refine Eq.trans (congrArg (stalkLegZero ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj
      Y.sheaf) X.sheaf
      (AlgebraicGeometry.inverseImageStructureMap f) x.1)
    (restrictTop_germ_smul V ((naiveCotangentModules f).X 0) x W hxW s
      (descDatumZero f hVU m))) ?_
  refine Eq.trans (stalkLegZero_germ_smul ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj
      Y.sheaf) X.sheaf
    (AlgebraicGeometry.inverseImageStructureMap f) x.1 (V.ι ''ᵁ W)
    (show (x : X) ∈ V.ι ''ᵁ W by simpa using hxW) s
    (((Scheme.Modules.restrictFunctor V.ι).obj ((naiveCotangentModules f).X 0)).val.map
      (homOfLE (le_top (a := W))).op
      (restrictTop V ((naiveCotangentModules f).X 0) (descDatumZero f hVU m)))) ?_
  refine Eq.trans ?_ (congrArg (fun r : ToType (TopCat.Presheaf.stalk X.sheaf.obj x.1) =>
      r • (show (Algebra.Generators.self
            (ToType (TopCat.Presheaf.stalk ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj
                Y.sheaf).obj x.1))
            (ToType (TopCat.Presheaf.stalk X.sheaf.obj x.1))).toExtension.CotangentSpace from
        Algebra.Extension.CotangentSpace.map
          (Stacks.NaiveCotangentAffineComparison.canonicalStalkHom f hVU x.2 (hVU x.2)) m))
    (stalkAlgEquiv_germ V x W hxW s)).symm
  refine congrArg (fun c : (Algebra.Generators.self
            (ToType (TopCat.Presheaf.stalk ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj
                Y.sheaf).obj x.1))
            (ToType (TopCat.Presheaf.stalk X.sheaf.obj x.1))).toExtension.CotangentSpace =>
    (show ToType (TopCat.Presheaf.stalk X.sheaf.obj x.1) from
      (TopCat.Presheaf.germ X.sheaf.obj (V.ι ''ᵁ W) x.1
        (show (x : X) ∈ V.ι ''ᵁ W by simpa using hxW)).hom s) • c) ?_
  refine Eq.trans (congrArg (stalkLegZero ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj
      Y.sheaf) X.sheaf
      (AlgebraicGeometry.inverseImageStructureMap f) x.1)
    (Eq.trans (TopCat.Presheaf.germ_res_apply
        ((naiveCotangentModules f).X 0).val.presheaf
        (V.ι.opensFunctor.map (homOfLE (le_top (a := W)))) x.1
        (show (x : X) ∈ V.ι ''ᵁ W by simpa using hxW)
        (restrictTop V ((naiveCotangentModules f).X 0) (descDatumZero f hVU m)))
      (TopCat.Presheaf.germ_res_apply ((naiveCotangentModules f).X 0).val.presheaf
        (eqToHom V.ι_image_top) x.1 (show (x : X) ∈ V.ι ''ᵁ ⊤ by simp)
        (descDatumZero f hVU m)))) ?_
  refine Eq.trans (congrArg (fun t : Γ((naiveCotangentModules f).X 0, V) =>
      stalkLegZero ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf) X.sheaf
        (AlgebraicGeometry.inverseImageStructureMap f) x.1
        ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          ((naiveCotangentModules f).X 0).val.presheaf V x.1 x.2).hom t))
    (ConcreteCategory.congr_arg (legZero (V := V) f) (DFunLike.congr_fun
      (Stacks.NaiveCotangentAffineComparison.sectionsBaseComparison_f₀ f hVU) m))) ?_
  refine Eq.trans (stalkLegZero_germ_sectionsTensorComparison ((TopCat.Sheaf.pullback
      CommRingCat.{u} f.base).obj Y.sheaf) X.sheaf
    (AlgebraicGeometry.inverseImageStructureMap f) x.1 V x.2
    (Algebra.Extension.CotangentSpace.map
      (Stacks.NaiveCotangentAffineComparison.baseChangeSelfHom
        (R := Γ(Y, U)) (R' := ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj
            Y.sheaf).obj.obj (op V)))
        (A := ↑(X.sheaf.obj.obj (op V)))) m)) ?_
  exact Stacks.NaiveCotangentAffineIso.cotangentSpaceMap_germSelfHom_eq_canonicalStalkHom
    f hVU x.2 (hVU x.2) m

/-- In degree `-1`, under `uNegOne` and `vNegOne`, the stalk of `comparisonMap f hVU` is the
degree `-1` component of `NaiveCotangent.nlExtensionBaseChangeMap canonicalStalkHom`. -/
theorem hp_all
    (ζ : letI := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
      ToType (X.presheaf.stalk x.1) ⊗[Γ(X, V)] nlSelfModNegOne f hVU) :
    letI := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
    letI := Stacks.NaiveCotangentAffineStalk.algebraStalkInverseImage f (hVU x.2)
    letI := Stacks.NaiveCotangentAffineStalk.algebraStalkInverseImageStructureMap f (x := x.1)
    letI := Stacks.NaiveCotangentAffineStalk.algebraStalkOfAppLE f hVU x.2
    haveI : IsScalarTower Γ(Y, U) Γ(X, V) ↑(X.presheaf.stalk x.1) :=
      Stacks.NaiveCotangentAffineStalk.isScalarTower_appLE f hVU x.2
    haveI : IsScalarTower Γ(Y, U)
        ↑(TopCat.Presheaf.stalk ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).obj
            x.1) ↑(X.presheaf.stalk x.1) :=
      Stacks.NaiveCotangentAffineStalk.isScalarTower_stalkInverseImage f hVU x.2 (hVU x.2)
    vNegOne V x f
        (((AlgebraicGeometry.SheafOfModules.stalkFunctor V.toScheme.ringCatSheaf x).map
          ((comparisonMap f hVU).f (-1))) ((uNegOne V x f hVU).symm ζ)) =
      (NaiveCotangent.nlExtensionBaseChangeMap
        (Stacks.NaiveCotangentAffineComparison.canonicalStalkHom f hVU x.2
          (hVU x.2))).f₁ ζ := by
  let := Stacks.NaiveCotangentAffineComparison.algebraAppLE' f hVU
  let := Stacks.NaiveCotangentAffineComparison.algebraBaseSection f hVU
  let := Stacks.NaiveCotangentAffineSections.algebraSections f V
  have _ := Stacks.NaiveCotangentAffineComparison.isScalarTower_baseSection f hVU
  let := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
  let := stalkAlgebra V.toScheme.toRingedSpace (alpha (V := V)) x
  let _ : DecidableEq (OrderDual (TopologicalSpace.OpenNhds x.1)) := Classical.decEq _
  let := Stacks.NaiveCotangentAffineStalk.algebraStalkInverseImage f (hVU x.2)
  let := Stacks.NaiveCotangentAffineStalk.algebraStalkInverseImageStructureMap f (x := x.1)
  let := Stacks.NaiveCotangentAffineStalk.algebraStalkOfAppLE f hVU x.2
  let _ : Algebra (ToType (TopCat.Presheaf.stalk ((TopCat.Sheaf.pullback CommRingCat.{u}
      f.base).obj Y.sheaf).obj x.1))
      (ToType (TopCat.Presheaf.stalk X.sheaf.obj x.1)) :=
    Stacks.RelativeDifferentialStalk.algebraStalk
      (AlgebraicGeometry.inverseImageStructureMap f).hom x.1
  have _ : IsScalarTower Γ(Y, U) Γ(X, V) ↑(X.presheaf.stalk x.1) :=
    Stacks.NaiveCotangentAffineStalk.isScalarTower_appLE f hVU x.2
  have _ : IsScalarTower Γ(Y, U)
      ↑(TopCat.Presheaf.stalk ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).obj x.1)
          ↑(X.presheaf.stalk x.1) :=
    Stacks.NaiveCotangentAffineStalk.isScalarTower_stalkInverseImage f hVU x.2 (hVU x.2)
  let Psi := (AlgebraicGeometry.SheafOfModules.stalkFunctor V.toScheme.ringCatSheaf x).map
    ((comparisonMap f hVU).f (-1))
  refine apply_symm_eq_of_forall_tmul (uNegOne V x f hVU) Psi.hom (vNegOne V x f) _ ?_ ζ
  intro t m
  obtain ⟨ξ, rfl⟩ := (stalkAlgEquiv V x).surjective t
  obtain ⟨W, hxW, sec, rfl⟩ := TopCat.Presheaf.exists_germ_eq V.toScheme.presheaf ξ
  exact Eq.trans (hp_tmul V x f hVU W hxW sec m)
    (LinearMap.liftBaseChange_tmul (ToType (X.presheaf.stalk x.1))
      (Algebra.Extension.Cotangent.map
        (Stacks.NaiveCotangentAffineComparison.canonicalStalkHom f hVU x.2
          (hVU x.2))) _ _).symm

/-- In degree `-1`, the stalk of `comparisonMap f hVU` is `vNegOne.symm` composed with the
degree `-1` component of `NaiveCotangent.nlExtensionBaseChangeMap canonicalStalkHom` and
`uNegOne`. -/
theorem hp
    (z : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      ((associatedNaiveCotangentComplex f hVU).X (-1)).val.presheaf x)) :
    letI := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
    letI := Stacks.NaiveCotangentAffineStalk.algebraStalkInverseImage f (hVU x.2)
    letI := Stacks.NaiveCotangentAffineStalk.algebraStalkInverseImageStructureMap f (x := x.1)
    letI := Stacks.NaiveCotangentAffineStalk.algebraStalkOfAppLE f hVU x.2
    haveI : IsScalarTower Γ(Y, U) Γ(X, V) ↑(X.presheaf.stalk x.1) :=
      Stacks.NaiveCotangentAffineStalk.isScalarTower_appLE f hVU x.2
    haveI : IsScalarTower Γ(Y, U)
        ↑(TopCat.Presheaf.stalk ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).obj
            x.1) ↑(X.presheaf.stalk x.1) :=
      Stacks.NaiveCotangentAffineStalk.isScalarTower_stalkInverseImage f hVU x.2 (hVU x.2)
    ((AlgebraicGeometry.SheafOfModules.stalkFunctor V.toScheme.ringCatSheaf x).map
        ((comparisonMap f hVU).f (-1))) z =
      (vNegOne V x f).symm
        ((NaiveCotangent.nlExtensionBaseChangeMap
          (Stacks.NaiveCotangentAffineComparison.canonicalStalkHom f hVU x.2
            (hVU x.2))).f₁ (uNegOne V x f hVU z)) := by
  exact apply_eq_symm_of_forall (uNegOne V x f hVU) (vNegOne V x f) _ _
    (hp_all V x f hVU) z

/-- In degree `0`, under `uZero` and `vZero`, the stalk of `comparisonMap f hVU` is the degree
`0` component of `NaiveCotangent.nlExtensionBaseChangeMap canonicalStalkHom`. -/
theorem hq_all
    (ζ : letI := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
      ToType (X.presheaf.stalk x.1) ⊗[Γ(X, V)] nlSelfModZero f hVU) :
    letI := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
    letI := Stacks.NaiveCotangentAffineStalk.algebraStalkInverseImage f (hVU x.2)
    letI := Stacks.NaiveCotangentAffineStalk.algebraStalkInverseImageStructureMap f (x := x.1)
    letI := Stacks.NaiveCotangentAffineStalk.algebraStalkOfAppLE f hVU x.2
    haveI : IsScalarTower Γ(Y, U) Γ(X, V) ↑(X.presheaf.stalk x.1) :=
      Stacks.NaiveCotangentAffineStalk.isScalarTower_appLE f hVU x.2
    haveI : IsScalarTower Γ(Y, U)
        ↑(TopCat.Presheaf.stalk ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).obj
            x.1) ↑(X.presheaf.stalk x.1) :=
      Stacks.NaiveCotangentAffineStalk.isScalarTower_stalkInverseImage f hVU x.2 (hVU x.2)
    vZero V x f
        (((AlgebraicGeometry.SheafOfModules.stalkFunctor V.toScheme.ringCatSheaf x).map
          ((comparisonMap f hVU).f 0)) ((uZero V x f hVU).symm ζ)) =
      (NaiveCotangent.nlExtensionBaseChangeMap
        (Stacks.NaiveCotangentAffineComparison.canonicalStalkHom f hVU x.2
          (hVU x.2))).f₀ ζ := by
  let := Stacks.NaiveCotangentAffineComparison.algebraAppLE' f hVU
  let := Stacks.NaiveCotangentAffineComparison.algebraBaseSection f hVU
  let := Stacks.NaiveCotangentAffineSections.algebraSections f V
  have _ := Stacks.NaiveCotangentAffineComparison.isScalarTower_baseSection f hVU
  let := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
  let := stalkAlgebra V.toScheme.toRingedSpace (alpha (V := V)) x
  let _ : DecidableEq (OrderDual (TopologicalSpace.OpenNhds x.1)) := Classical.decEq _
  let := Stacks.NaiveCotangentAffineStalk.algebraStalkInverseImage f (hVU x.2)
  let := Stacks.NaiveCotangentAffineStalk.algebraStalkInverseImageStructureMap f (x := x.1)
  let := Stacks.NaiveCotangentAffineStalk.algebraStalkOfAppLE f hVU x.2
  let _ : Algebra (ToType (TopCat.Presheaf.stalk ((TopCat.Sheaf.pullback CommRingCat.{u}
      f.base).obj Y.sheaf).obj x.1))
      (ToType (TopCat.Presheaf.stalk X.sheaf.obj x.1)) :=
    Stacks.RelativeDifferentialStalk.algebraStalk
      (AlgebraicGeometry.inverseImageStructureMap f).hom x.1
  have _ : IsScalarTower Γ(Y, U) Γ(X, V) ↑(X.presheaf.stalk x.1) :=
    Stacks.NaiveCotangentAffineStalk.isScalarTower_appLE f hVU x.2
  have _ : IsScalarTower Γ(Y, U)
      ↑(TopCat.Presheaf.stalk ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).obj x.1)
          ↑(X.presheaf.stalk x.1) :=
    Stacks.NaiveCotangentAffineStalk.isScalarTower_stalkInverseImage f hVU x.2 (hVU x.2)
  let Psi := (AlgebraicGeometry.SheafOfModules.stalkFunctor V.toScheme.ringCatSheaf x).map
    ((comparisonMap f hVU).f 0)
  refine apply_symm_eq_of_forall_tmul (uZero V x f hVU) Psi.hom (vZero V x f) _ ?_ ζ
  intro t m
  obtain ⟨ξ, rfl⟩ := (stalkAlgEquiv V x).surjective t
  obtain ⟨W, hxW, sec, rfl⟩ := TopCat.Presheaf.exists_germ_eq V.toScheme.presheaf ξ
  exact Eq.trans (hq_tmul V x f hVU W hxW sec m)
    (LinearMap.liftBaseChange_tmul (ToType (X.presheaf.stalk x.1))
      (Algebra.Extension.CotangentSpace.map
        (Stacks.NaiveCotangentAffineComparison.canonicalStalkHom f hVU x.2
          (hVU x.2))) _ _).symm

/-- In degree `0`, the stalk of `comparisonMap f hVU` is `vZero.symm` composed with the degree
`0` component of `NaiveCotangent.nlExtensionBaseChangeMap canonicalStalkHom` and `uZero`. -/
theorem hq
    (z : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      ((associatedNaiveCotangentComplex f hVU).X 0).val.presheaf x)) :
    letI := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
    letI := Stacks.NaiveCotangentAffineStalk.algebraStalkInverseImage f (hVU x.2)
    letI := Stacks.NaiveCotangentAffineStalk.algebraStalkInverseImageStructureMap f (x := x.1)
    letI := Stacks.NaiveCotangentAffineStalk.algebraStalkOfAppLE f hVU x.2
    haveI : IsScalarTower Γ(Y, U) Γ(X, V) ↑(X.presheaf.stalk x.1) :=
      Stacks.NaiveCotangentAffineStalk.isScalarTower_appLE f hVU x.2
    haveI : IsScalarTower Γ(Y, U)
        ↑(TopCat.Presheaf.stalk ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).obj
            x.1) ↑(X.presheaf.stalk x.1) :=
      Stacks.NaiveCotangentAffineStalk.isScalarTower_stalkInverseImage f hVU x.2 (hVU x.2)
    ((AlgebraicGeometry.SheafOfModules.stalkFunctor V.toScheme.ringCatSheaf x).map
        ((comparisonMap f hVU).f 0)) z =
      (vZero V x f).symm
        ((NaiveCotangent.nlExtensionBaseChangeMap
          (Stacks.NaiveCotangentAffineComparison.canonicalStalkHom f hVU x.2
            (hVU x.2))).f₀ (uZero V x f hVU z)) := by
  exact apply_eq_symm_of_forall (uZero V x f hVU) (vZero V x f) _ _
    (hq_all V x f hVU) z

/-- If `U` and `V` are affine, the canonical map `comparisonMap f hVU` from the sheaf associated
to `NL_{A/R}` to the restriction of `NL_{X/Y}` to `V` is a quasi-isomorphism. -/
@[stacks 0D0I "the canonical map (NL_{A/R})~ to NL_{X/Y}|_V is an isomorphism in D(O_V)"]
theorem quasiIso_comparisonMap (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    QuasiIso (comparisonMap f hVU) := by
  refine AlgebraicGeometry.SheafOfModules.quasiIso_of_forall_stalk_quasiIso _ _ fun x => ?_
  let := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
  let _ : Algebra Γ(X, V) (ToType (X.presheaf.stalk x.1)) :=
    X.presheaf.algebra_section_stalk (⟨x.1, x.2⟩ : V)
  let := Stacks.NaiveCotangentAffineStalk.algebraStalkInverseImage f (hVU x.2)
  let := Stacks.NaiveCotangentAffineStalk.algebraStalkInverseImageStructureMap f (x := x.1)
  let := Stacks.NaiveCotangentAffineStalk.algebraStalkOfAppLE f hVU x.2
  let _ : Algebra (ToType (TopCat.Presheaf.stalk ((TopCat.Sheaf.pullback CommRingCat.{u}
      f.base).obj Y.sheaf).obj x.1))
      (ToType (TopCat.Presheaf.stalk X.sheaf.obj x.1)) :=
    Stacks.RelativeDifferentialStalk.algebraStalk
      (AlgebraicGeometry.inverseImageStructureMap f).hom x.1
  have _ : IsScalarTower Γ(Y, U) Γ(X, V) ↑(X.presheaf.stalk x.1) :=
    Stacks.NaiveCotangentAffineStalk.isScalarTower_appLE f hVU x.2
  have _ : IsScalarTower Γ(Y, U)
      ↑(TopCat.Presheaf.stalk ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).obj x.1)
          ↑(X.presheaf.stalk x.1) :=
    Stacks.NaiveCotangentAffineStalk.isScalarTower_stalkInverseImage f hVU x.2 (hVU x.2)
  have hqi :=
    Stacks.NaiveCotangentAffineComparison.isQuasiIso_nlExtensionBaseChangeMap_canonicalStalkHom
      f hVU x.2 (hVU x.2) hU hV
  exact CochainComplex.quasiIso_of_isZero_X_of_addEquiv _
    (isZero_src V x f hVU)
    (isZero_tgt V x f)
    (uNegOne V x f hVU) (uZero V x f hVU) (vNegOne V x f) (vZero V x f)
    (LinearMap.baseChange (ToType (X.presheaf.stalk x.1)) (nlSelfModD f hVU).hom)
    (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk ((TopCat.Sheaf.pullback CommRingCat.{u}
        f.base).obj Y.sheaf).obj x.1))
      (ToType (TopCat.Presheaf.stalk X.sheaf.obj x.1))).toExtension.cotangentComplex
    ((NaiveCotangent.nlExtensionBaseChangeMap
      (Stacks.NaiveCotangentAffineComparison.canonicalStalkHom f hVU x.2 (hVU x.2))).f₁)
    ((NaiveCotangent.nlExtensionBaseChangeMap
      (Stacks.NaiveCotangentAffineComparison.canonicalStalkHom f hVU x.2 (hVU x.2))).f₀)
    (fun z => Eq.symm (((uZero V x f hVU).symm_apply_eq).mpr (src_d V x f hVU z).symm))
    (fun z => Eq.symm (((vZero V x f).symm_apply_eq).mpr (tgt_d V x f z).symm))
    (hp V x f hVU) (hq V x f hVU)
    hqi.eq_zero_of_d_eq_zero hqi.exists_of_d_eq_zero hqi.exists_d_eq hqi.exists_add_d_eq

end Stacks.NaiveCotangentAffineQuasiIso

end

end
