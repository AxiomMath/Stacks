module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
public import Mathlib.FieldTheory.IntermediateField.Algebraic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.SeparableClosure
public import StacksCore.CategoryTheory.Pullback
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RepresentablePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldExtensionDescent.AlgebraicClosureSite
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldExtensionDescent.StructureMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.OverFields.AlgClosureFGSubalgebraDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.PurelyInseparableBaseChangeScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeOfIntegralBijection
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoverAffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedDiagonal

/-!
# A scheme after a field extension is a scheme after a finite separable one

Let `k` be a field with algebraic closure `k̄` and let `X` be a quasi-separated algebraic space
over `k` inside a chosen big fppf site, which becomes a scheme after base change along *some*
field extension `K/k`. Then `X_{k̄}` is a scheme, and if `X` is in addition quasi-compact then
`X_{k'}` is a scheme already for a finite separable extension `k'/k`. These are the two parts of
[Stacks, Tag 0B84].

Base change along `K/k` is restriction along the induced morphism `Spec K ⟶ Spec k` of the site,
that is `CategoryTheory.OverShriek.relocalizeRestrict`, and being a scheme is
`CategoryTheory.Functor.IsRepresentable`.

## Main results

* `AlgebraicGeometry.Space.exists_finite_separable_isRepresentable_relocalizeRestrict`:
  **[Stacks, Tag 0B84] part (2)**.
* `AlgebraicGeometry.Space.isRepresentable_relocalizeRestrict_algebraicClosure`:
  **[Stacks, Tag 0B84] part (1)**.
* `AlgebraicGeometry.Space.isRepresentable_of_isRepresentable_extensionBaseChange_of_finite`:
  the case of [Stacks, Tag 0B83] for a *finite* purely inseparable extension, which is the case
  Tag 0B84 consumes.
* `AlgebraicGeometry.Space.relocalizeRestrictCompIso` and
  `AlgebraicGeometry.Space.isRepresentable_relocalizeRestrict_comp`: transitivity of base change.
* `AlgebraicGeometry.Space.isRepresentable_prod_of_isRepresentable_relocalizeRestrict`: the
  representability half of [Stacks, Tag 04SH].

## Implementation notes

The proof of part (2) follows the source. The descent situation of the finitely generated
`k`-subalgebras `A` of `K`, with `X_K` as its limit, is
`AlgebraicGeometry.Space.fgSubalgebraDescentSituation`, and [Stacks, Tag 07SR] produces a stage
`A` with `X_A` a scheme; this is
`AlgebraicGeometry.Space.exists_fgSubalgebra_isRepresentable_relocalizeRestrict`. A residue
field `k₁ = A/𝔪` of `A` at a maximal ideal is a finite extension of `k` by Hilbert's
Nullstellensatz, [Stacks, Tag 00FV], in the form
`AlgebraicGeometry.FieldExtensionDescent.finite_quotient_of_isMaximal`, and `X_{k₁}` is a scheme
because `Spec k₁ ⟶ Spec A` factors the structure morphism of `Spec k₁` over `Spec k`. Finally
`L = separableClosure k k₁` is the subextension of [Stacks, Tag 030K]: it is separable over `k`,
finite because `k₁` is, and `k₁` is purely inseparable over it, so the scheme `X_{k₁}` descends
to `X_L`.

Mathlib has Tag 030K as the pair of instances `separableClosure.isSeparable` and
`separableClosure.isPurelyInseparable`, so no declaration of that content is made here; the
finiteness of `L/k` is `IntermediateField.finiteDimensional_left`.

*The purely inseparable step.* The source cites [Stacks, Tag 0B83] for it. Here the extension
`k₁/L` is finite, and for a finite purely inseparable extension the projection `X_{k₁} ⟶ X_L` is
surjective, finite locally free and universally injective, so each fibre is a single point,
which lies in an affine open of the scheme `X_{k₁}`; [Stacks, Tag 0BA1] then puts every point of
`X_L` in its schematic locus. That is
`AlgebraicGeometry.Space.isRepresentable_of_isRepresentable_extensionBaseChange_of_finite`; it
needs none of the limit theory of [Stacks, Tag 07VT] through which Tag 0B83 is proved for an
arbitrary purely inseparable extension.

Two pieces of plumbing are proved first.
`AlgebraicGeometry.Space.relocalizeRestrictCompIso` identifies restriction along a composite with
the composite of the restrictions, and
`AlgebraicGeometry.Space.isRepresentable_relocalizeRestrict_comp` is the resulting transitivity
of base change: restriction along `g` preserves representability because
`CategoryTheory.Over.map g` is a left adjoint, so a scheme after base change along `f` is a
scheme after base change along `g ≫ f`. This is what moves `X_A` up to `X_{k₁}`, and read
backwards it presents `X_{k₁}` as a base change of `X_L`.
`AlgebraicGeometry.Space.isRepresentable_prod_of_isRepresentable_relocalizeRestrict` converts the
restriction spelling of a base change into the product spelling
`AlgebraicGeometry.Space.extensionBaseChange`; it is the representability half of
[Stacks, Tag 04SH], and is `AlgebraicGeometry.relocalizedYonedaRepresentableBy`
([Stacks, Tag 03I4] part (2)) followed by
`CategoryTheory.OverShriek.relocalizeRestrictIsoProduct`.

Part (1) is deduced from part (2) by the argument the source sketches and whose details it
omits. The space `X` is covered by quasi-compact open subspaces: the affine etale atlas of
[Stacks, Tag 03FY] gives a Zariski covering each of whose members has an affine etale surjective
chart, which is quasi-compactness by [Stacks, Tag 03H6]. Each member is quasi-separated by
[Stacks, Tag 04ZH] part (2), being a monomorphism into `X`, and is a scheme over `K` because
being an open immersion survives base change, so part (2) makes it a scheme over a finite
separable `k'/k`; that `k'` embeds into `k̄` by [Stacks, Tag 09GU], whence the member is a
scheme over `k̄` by transitivity of base change. The ranges of the base-changed members form a
Zariski covering of `X_{k̄}` --- the open-subspace half from [Stacks, Tag 03I5] part (1), the
local-surjectivity half in
`AlgebraicGeometry.Space.isLocallySurjective_sigmaDesc_range_relocalizeRestrict`, which uses
that restriction along a morphism of the base is a precomposition and so commutes with the
coproduct of the covering family --- so [Stacks, Tag 03KE] finishes. The statement is proved for
an arbitrary algebraically closed extension of `k` in the site and then specialized to `k̄`,
whose spectrum lies in the site automatically.

## References

* [Stacks Project, Tag 00FV](https://stacks.math.columbia.edu/tag/00FV)
* [Stacks Project, Tag 030K](https://stacks.math.columbia.edu/tag/030K)
* [Stacks Project, Tag 03FY](https://stacks.math.columbia.edu/tag/03FY)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 03I4](https://stacks.math.columbia.edu/tag/03I4)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 03KE](https://stacks.math.columbia.edu/tag/03KE)
* [Stacks Project, Tag 04SH](https://stacks.math.columbia.edu/tag/04SH)
* [Stacks Project, Tag 04ZH](https://stacks.math.columbia.edu/tag/04ZH)
* [Stacks Project, Tag 04ZI](https://stacks.math.columbia.edu/tag/04ZI)
* [Stacks Project, Tag 09GU](https://stacks.math.columbia.edu/tag/09GU)
* [Stacks Project, Tag 07SR](https://stacks.math.columbia.edu/tag/07SR)
* [Stacks Project, Tag 09RH](https://stacks.math.columbia.edu/tag/09RH)
* [Stacks Project, Tag 0B83](https://stacks.math.columbia.edu/tag/0B83)
* [Stacks Project, Tag 0B84](https://stacks.math.columbia.edu/tag/0B84)
* [Stacks Project, Tag 0BA1](https://stacks.math.columbia.edu/tag/0BA1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

open FieldExtensionDescent

/-! ### Transitivity of base change -/

/-- **Restriction along a composite is the composite of the restrictions.** For `g : W ⟶ V`,
`f : V ⟶ U` and a presheaf `F` on the slice over `U`, restricting `F` to the slice over `V` and
then to the slice over `W` is restricting it along `g ≫ f`. -/
def relocalizeRestrictCompIso {C : Type (u + 1)} [Category.{u} C] {W V U : C} (g : W ⟶ V)
    (f : V ⟶ U) (F : (Over U)ᵒᵖ ⥤ Type u) :
    (OverShriek.relocalizeRestrict g).obj ((OverShriek.relocalizeRestrict f).obj F) ≅
      (OverShriek.relocalizeRestrict (g ≫ f)).obj F :=
  (Functor.associator (Over.map g).op (Over.map f).op F).symm ≪≫
    Functor.isoWhiskerRight
      ((Functor.opComp (Over.map g) (Over.map f)).symm ≪≫ NatIso.op (Over.mapComp g f)) F

/-- **Base change is transitive.** If a presheaf on the slice over `U` becomes representable
after restriction along `f : V ⟶ U`, then it becomes representable after restriction along
`g ≫ f` for any `g : W ⟶ V`.

Restriction along `g ≫ f` is restriction along `g` of restriction along `f` by
`AlgebraicGeometry.Space.relocalizeRestrictCompIso`, and restriction along `g` preserves
representability because `CategoryTheory.Over.map g` is left adjoint to
`CategoryTheory.Over.pullback g`. -/
theorem isRepresentable_relocalizeRestrict_comp
    {C : Type (u + 1)} [Category.{u} C] [HasPullbacks C] {W V U : C} (g : W ⟶ V) (f : V ⟶ U)
    (F : (Over U)ᵒᵖ ⥤ Type u)
    (h : ((OverShriek.relocalizeRestrict f).obj F).IsRepresentable) :
    ((OverShriek.relocalizeRestrict (g ≫ f)).obj F).IsRepresentable := by
  let := h
  let : ((OverShriek.relocalizeRestrict g).obj
      ((OverShriek.relocalizeRestrict f).obj F)).IsRepresentable :=
    Functor.IsRepresentable.mk'
      ((Over.mapPullbackAdj g).compYonedaIso.app
          ((OverShriek.relocalizeRestrict f).obj F).reprX ≪≫
        (OverShriek.relocalizeRestrict g).mapIso
          ((OverShriek.relocalizeRestrict f).obj F).reprW)
  exact isRepresentable_of_natIso ((OverShriek.relocalizeRestrict g).obj
    ((OverShriek.relocalizeRestrict f).obj F)) (relocalizeRestrictCompIso g f F)

/-- **The restriction spelling of a base change implies the product spelling.** If the
restriction of `F` along `f : Spec S ⟶ Spec T` is representable then so is the product of `F`
with the presheaf represented by the object `S →f T` of the site of `T`. This is the
representability half of [Stacks, Tag 04SH].

The relocalization of a representable presheaf is representable by [Stacks, Tag 03I4] part (2),
and relocalizing a restriction is that product by
`CategoryTheory.OverShriek.relocalizeRestrictIsoProduct`. -/
theorem isRepresentable_prod_of_isRepresentable_relocalizeRestrict (B : BigFppfSite.{u})
    (S T : Scheme.{u}) (hS : B.Contains S) (hT : B.Contains T) (f : B.obj hS ⟶ B.obj hT)
    (F : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u)
    (h : ((OverShriek.relocalizeRestrict f).obj F).IsRepresentable) :
    (yoneda.obj (Over.mk f) ⨯ F).IsRepresentable := by
  obtain ⟨U, ⟨r⟩⟩ := h.has_representation
  exact Functor.IsRepresentable.mk'
    ((relocalizedYonedaRepresentableBy B (B.obj hS) (B.obj hT) f U).toIso ≪≫
      (OverShriek.relocalizePresheafFunctor f).mapIso r.toIso ≪≫
      OverShriek.relocalizeRestrictIsoProduct f F)

/-- **Composition of site morphisms between spectra.** If `f ≫ g = h` for ring maps
`f : R ⟶ S`, `g : S ⟶ T` and `h : R ⟶ T`, then `Spec g` followed by `Spec f` is `Spec h` in the
site. -/
private theorem homMk_spec_map_comp (B : BigFppfSite.{u}) {R S T : CommRingCat.{u}}
    (hR : B.Contains (Spec R)) (hS : B.Contains (Spec S)) (hT : B.Contains (Spec T))
    (f : R ⟶ S) (g : S ⟶ T) (h : R ⟶ T) (hfg : f ≫ g = h) :
    (ObjectProperty.homMk (Spec.map g) : B.obj hT ⟶ B.obj hS) ≫
      (ObjectProperty.homMk (Spec.map f) : B.obj hS ⟶ B.obj hR) =
        ObjectProperty.homMk (Spec.map h) := by
  apply ObjectProperty.hom_ext
  change Spec.map g ≫ Spec.map f = Spec.map h
  rw [← Spec.map_comp, hfg]

/-- **Transitivity of base change along spectra of ring maps.** If `X_S` is representable and
`f ≫ g = h` for ring maps `f : R ⟶ S`, `g : S ⟶ T` and `h : R ⟶ T`, then `X_T` is
representable. -/
private theorem isRepresentable_relocalizeRestrict_spec_comp (B : BigFppfSite.{u})
    {R S T : CommRingCat.{u}} (hR : B.Contains (Spec R)) (hS : B.Contains (Spec S))
    (hT : B.Contains (Spec T)) (f : R ⟶ S) (g : S ⟶ T) (h : R ⟶ T) (hfg : f ≫ g = h)
    (X : (BigFppfOver B (Spec R) hR)ᵒᵖ ⥤ Type u)
    (hf : ((OverShriek.relocalizeRestrict
      (ObjectProperty.homMk (Spec.map f) : B.obj hS ⟶ B.obj hR)).obj X).IsRepresentable) :
    ((OverShriek.relocalizeRestrict
      (ObjectProperty.homMk (Spec.map h) : B.obj hT ⟶ B.obj hR)).obj X).IsRepresentable := by
  rw [← homMk_spec_map_comp B hR hS hT f g h hfg]
  exact isRepresentable_relocalizeRestrict_comp _ _ X hf

/-! ### Descending along a finite purely inseparable extension -/

section FinitePurelyInseparable

variable (k k' : Type u) [Field k] [Field k'] [Algebra k k'] (B : BigFppfSite.{u})
  (hk : B.Contains (Spec (.of k))) (hk' : B.Contains (Spec (.of k')))

/-- **The projection `X_{k'} ⟶ X` has every base-change stable property of `Spec k' ⟶ Spec k`.**
The projection is the base change of the structure morphism of `Spec k'` along the structure
morphism of `X`, by `AlgebraicGeometry.Space.isPullback_extensionBaseChangeProj`. -/
private theorem presheaf_extensionBaseChangeProj (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hP : P (Spec.map (CommRingCat.ofHom (algebraMap k k')))) :
    (P.inverseImage (BigFppfOver.toScheme B (Spec (.of k)) hk)).presheaf
      (extensionBaseChangeProj k k' B hk hk' X) := by
  have hg := (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B (Spec (.of k)) hk P
    (specExtensionToBase k k' B hk hk')).2 hP
  let Q := P.inverseImage (BigFppfOver.toScheme B (Spec (.of k)) hk)
  let : Q.presheaf.IsStableUnderBaseChange := MorphismProperty.relative_isStableUnderBaseChange Q
  exact MorphismProperty.of_isPullback (isPullback_extensionBaseChangeProj k k' B hk hk' X) hg

/-- **An algebraic space over `k` which becomes a scheme after a finite purely inseparable
extension `k'/k` is a scheme.** This is the case of [Stacks, Tag 0B83] that [Stacks, Tag 0B84]
consumes.

The projection `f : X_{k'} ⟶ X` is a base change of `Spec k' ⟶ Spec k`, so it is surjective and
finite locally free, `k'` being a finite free `k`-module, and it is universally injective, `k'/k`
being purely inseparable, hence injective on points. The fibre of `f` over a point `y` of `X`
is therefore a single point, which lies in an affine open of the scheme `X_{k'}`; by
[Stacks, Tag 0BA1] the point `y` lies in the schematic locus of `X`. So the schematic locus
carries every point and `X` is a scheme. -/
theorem isRepresentable_of_isRepresentable_extensionBaseChange_of_finite
    [IsPurelyInseparable k k'] [FiniteDimensional k k']
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (hXk' : (extensionBaseChange k k' B hk hk' X).IsRepresentable) :
    X.IsRepresentable := by
  classical
  let Xk' : AlgebraicSpaces B (Spec (.of k)) hk :=
    ⟨_, isAlgebraicSpace_extensionBaseChange k k' B hk hk' X hX⟩
  let Y : AlgebraicSpaces B (Spec (.of k)) hk := ⟨X, hX⟩
  let f : Xk' ⟶ Y := ObjectProperty.homMk (extensionBaseChangeProj k k' B hk hk' X)
  have hsurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (.of k)) hk)).presheaf f.hom :=
    presheaf_extensionBaseChangeProj k k' B hk hk' (@Surjective.{u}) X
      ⟨fun _ => ⟨IsLocalRing.closedPoint k', Subsingleton.elim _ _⟩⟩
  have hflf : (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (.of k)) hk)).presheaf f.hom := by
    have := Stacks.Morphisms.isFiniteLocallyFree_isStableUnderBaseChange
    exact presheaf_extensionBaseChangeProj k k' B hk hk' _ X
      ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
        _).mpr ⟨(IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance),
          inferInstance,
          (LocallyOfFinitePresentation.SpecMap_iff _).mpr
            (RingHom.finitePresentation_algebraMap.mpr
              (Algebra.FinitePresentation.of_finiteType.mp inferInstance))⟩)
  have hinj : Function.Injective (pointsMap B (Spec (.of k)) hk _ f.hom) :=
    injective_pointsMap_of_universallyInjective B (Spec (.of k)) hk hX
      (universallyInjective_extensionBaseChangeProj k k' B hk hk' hX)
  obtain ⟨W, ⟨r⟩⟩ := hXk'.has_representation
  refine isRepresentable_of_surjective_pointsMap_schematicLocus B (Spec (.of k)) hk hX
    fun y => ?_
  obtain ⟨x, hx⟩ := isSurjective_extensionBaseChangeProj k k' B hk hk' X y
  -- an affine open of the scheme `X_{k'}` through the unique point over `y`
  obtain ⟨p, rfl⟩ := Quot.exists_rep x
  obtain ⟨i, q, hq⟩ := exists_affineChart_pointsMap_eq B (Spec (.of k)) hk W r.toIso p
  have hα : IsOpenImmersion B (Spec (.of k)) hk
      (yoneda.map (affineChartι B (Spec (.of k)) hk W i) ≫ r.toIso.hom) :=
    MorphismProperty.RespectsIso.postcomp _ r.toIso.hom _
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B (Spec (.of k)) hk
        (@AlgebraicGeometry.IsOpenImmersion.{u}) _).2
        (isOpenImmersion_toScheme_map_affineChartι B (Spec (.of k)) hk W i))
  exact mem_range_pointsMap_schematicLocus_of_exists_isAffine B (Spec (.of k)) hk f hsurj hflf
    y (affineChart B (Spec (.of k)) hk W i) _ (isAffine_affineChart B (Spec (.of k)) hk W i) hα
    fun x' hx' => (hinj (hx'.trans hx.symm)) ▸ ⟨_, hq⟩

end FinitePurelyInseparable

/-! ### Descending from a finite extension to a finite separable one -/

/-- **The separable step of [Stacks, Tag 0B84] part (2).** If an algebraic space `X` over a
field `k` becomes a scheme after base change along a *finite* extension `k₁/k`, then it becomes
a scheme after base change along a finite *separable* extension of `k`.

The intermediate field `L = separableClosure k k₁` is the subextension of [Stacks, Tag 030K]: it
is separable over `k` by `separableClosure.isSeparable`, finite over `k` because `k₁` is, and
`k₁` is purely inseparable over it by `separableClosure.isPurelyInseparable`. The base change
`X_{k₁}` is the base change of `X_L` along the finite purely inseparable extension `k₁/L`, so
`AlgebraicGeometry.Space.isRepresentable_of_isRepresentable_extensionBaseChange_of_finite`
applies over `L`. -/
private theorem exists_separable_isRepresentable_relocalizeRestrict (k k₁ : Type u) [Field k]
    [Field k₁] [Algebra k k₁] [Module.Finite k k₁] (B : BigFppfSite.{u})
    (hk : B.Contains (Spec (.of k))) (hk₁ : B.Contains (Spec (.of k₁)))
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (hXk₁ : ((OverShriek.relocalizeRestrict (specExtensionHom k k₁ B hk hk₁)).obj
      X).IsRepresentable) :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k') (_ : Module.Finite k k')
      (_ : Algebra.IsSeparable k k') (hk' : B.Contains (Spec (.of k'))),
      ((OverShriek.relocalizeRestrict (specExtensionHom k k' B hk hk')).obj
        X).IsRepresentable := by
  have : Module.Finite k ↥(separableClosure k k₁) := IntermediateField.finiteDimensional_left _
  have : FiniteDimensional ↥(separableClosure k k₁) k₁ :=
    Module.Finite.of_restrictScalars_finite k _ k₁
  have hL : B.Contains (Spec (.of ↥(separableClosure k k₁))) :=
    contains_spec_of_isAlgebraic B k ↥(separableClosure k k₁) hk
  have hc : B.Contains (Spec (.of k₁)) :=
    contains_spec_of_isAlgebraic B ↥(separableClosure k k₁) k₁ hL
  have htower : specExtensionHom ↥(separableClosure k k₁) k₁ B hL hc ≫
      specExtensionHom k ↥(separableClosure k k₁) B hk hL =
        specExtensionHom k k₁ B hk hk₁ :=
    homMk_spec_map_comp B hk hL hc _ _ _ (by
      ext x
      exact (IsScalarTower.algebraMap_apply k ↥(separableClosure k k₁) k₁ x).symm)
  let hcomposite : ((OverShriek.relocalizeRestrict
      (specExtensionHom ↥(separableClosure k k₁) k₁ B hL hc ≫
        specExtensionHom k ↥(separableClosure k k₁) B hk hL)).obj X).IsRepresentable := by
    rw [htower]
    exact hXk₁
  have hLk₁ : ((OverShriek.relocalizeRestrict
      (specExtensionHom ↥(separableClosure k k₁) k₁ B hL hc)).obj
      ((OverShriek.relocalizeRestrict
        (specExtensionHom k ↥(separableClosure k k₁) B hk hL)).obj X)).IsRepresentable :=
    isRepresentable_of_natIso _ (relocalizeRestrictCompIso
      (specExtensionHom ↥(separableClosure k k₁) k₁ B hL hc)
      (specExtensionHom k ↥(separableClosure k k₁) B hk hL) X).symm
  exact ⟨↥(separableClosure k k₁), inferInstance, inferInstance, inferInstance, inferInstance,
    hL, isRepresentable_of_isRepresentable_extensionBaseChange_of_finite
      ↥(separableClosure k k₁) k₁ B hL hc
      ((OverShriek.relocalizeRestrict
        (specExtensionHom k ↥(separableClosure k k₁) B hk hL)).obj X)
      (isAlgebraicSpace_relocalizeRestrict B (Spec (.of ↥(separableClosure k k₁))) (Spec (.of k))
        hL hk (specExtensionHom k ↥(separableClosure k k₁) B hk hL) X hX)
      (isRepresentable_prod_of_isRepresentable_relocalizeRestrict B (Spec (.of k₁))
        (Spec (.of ↥(separableClosure k k₁))) hc hL
        (specExtensionHom ↥(separableClosure k k₁) k₁ B hL hc) _ hLk₁)⟩

/-! ### From a finitely generated stage to a finite separable extension -/

/-- **The second half of [Stacks, Tag 0B84] part (2).** If `X_A` is a scheme for a finitely
generated `k`-subalgebra `A` of a field extension `K/k`, then `X_{k'}` is a scheme for a finite
separable extension `k'/k`.

A residue field `k₁ = A/𝔪` of `A` at a maximal ideal is a finite extension of `k` by Hilbert's
Nullstellensatz, [Stacks, Tag 00FV], in the form
`AlgebraicGeometry.FieldExtensionDescent.finite_quotient_of_isMaximal`, and `X_{k₁}` is a scheme
because `Spec k₁ ⟶ Spec A` factors the structure morphism of `Spec k₁` over `Spec k`; the
separable step `exists_separable_isRepresentable_relocalizeRestrict` finishes. -/
private theorem exists_finite_separable_of_fgSubalgebra (k K : Type u) [Field k] [Field K]
    [Algebra k K] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (hK : B.Contains (Spec (.of K))) (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X) (A : FGSubalgebra k K)
    (hAX : ((OverShriek.relocalizeRestrict (fgSubalgebraSiteHom k K B hk hK A)).obj
      X).IsRepresentable) :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k') (_ : Module.Finite k k')
      (_ : Algebra.IsSeparable k k') (hk' : B.Contains (Spec (.of k'))),
      ((OverShriek.relocalizeRestrict (specExtensionHom k k' B hk hk')).obj
        X).IsRepresentable := by
  classical
  -- The residue field of that stage at a maximal ideal is a finite extension of `k`.
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (A : Subalgebra k K)
  let := hm
  let : Field ((A : Subalgebra k K) ⧸ m) := Ideal.Quotient.field m
  have : Module.Finite k ((A : Subalgebra k K) ⧸ m) := finite_quotient_of_isMaximal k K A m
  have h1 : B.Contains (Spec (.of ((A : Subalgebra k K) ⧸ m))) :=
    contains_spec_of_isAlgebraic B k ((A : Subalgebra k K) ⧸ m) hk
  -- `X` becomes a scheme over it, because `Spec (A/𝔪) ⟶ Spec A ⟶ Spec k`.
  have h1X : ((OverShriek.relocalizeRestrict
      (specExtensionHom k ((A : Subalgebra k K) ⧸ m) B hk h1)).obj X).IsRepresentable :=
    isRepresentable_relocalizeRestrict_spec_comp B hk
      (contains_spec_subalgebra k K B hK (A : Subalgebra k K)) h1 _
      (CommRingCat.ofHom (Ideal.Quotient.mkₐ k m).toRingHom) _
      (by
        ext x
        exact (Ideal.Quotient.mkₐ k m).commutes x) X hAX
  -- The separable closure of `k` in that residue field is the extension we are after.
  exact exists_separable_isRepresentable_relocalizeRestrict k ((A : Subalgebra k K) ⧸ m) B hk h1
    X hX h1X

/-! ### Stacks 0B84, part (2) -/

/-- **[Stacks, Tag 0B84] part (2).** Let `k` be a field and let `X` be a quasi-compact and
quasi-separated algebraic space over `k`. If there is a field extension `K/k` such that the base
change `X_K` is a scheme, then there is a *finite separable* extension `k'/k` such that `X_{k'}`
is a scheme.

The proof is the source's. `K` is the filtered union of its finitely generated `k`-subalgebras
`A`, and [Stacks, Tag 07SR] makes one of the base changes `X_A` a scheme; this is
`AlgebraicGeometry.Space.exists_fgSubalgebra_isRepresentable_relocalizeRestrict`. A residue
field `k₁` of `A` at a maximal ideal is finite over `k` by the Nullstellensatz, `X_{k₁}` is a
scheme, and the separable closure `k'` of `k` in `k₁` is finite separable over `k` with `k₁/k'`
purely inseparable, so `X_{k'}` is a scheme by the finite case of [Stacks, Tag 0B83],
`AlgebraicGeometry.Space.isRepresentable_of_isRepresentable_extensionBaseChange_of_finite`. -/
@[stacks 0B84 "part (2)"]
theorem exists_finite_separable_isRepresentable_relocalizeRestrict (k K : Type u) [Field k]
    [Field K] [Algebra k K] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (hK : B.Contains (Spec (.of K))) (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (hXqc : IsQuasiCompactSpace B (Spec (.of k)) hk X)
    (hXqs : IsAbsolutelyQuasiSeparated B (Spec (.of k)) hk B.contains_terminal X)
    (hXK : ((OverShriek.relocalizeRestrict (specExtensionHom k K B hk hK)).obj
      X).IsRepresentable) :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k') (_ : Module.Finite k k')
      (_ : Algebra.IsSeparable k k') (hk' : B.Contains (Spec (.of k'))),
      ((OverShriek.relocalizeRestrict (specExtensionHom k k' B hk hk')).obj
        X).IsRepresentable := by
  obtain ⟨A, hAX⟩ :=
    exists_fgSubalgebra_isRepresentable_relocalizeRestrict k K B hk hK X hX hXqc hXqs hXK
  exact exists_finite_separable_of_fgSubalgebra k K B hk hK X hX A hAX

/-! ### Restricting a Zariski covering to a smaller base -/

/-- **The local surjectivity half of restricting a Zariski covering to a smaller base.** The
ranges of the restrictions along `g : S ⟶ S'` of the members of a locally surjective family of
subfunctors again form a locally surjective family.

Restriction along `g` is precomposition with `CategoryTheory.Over.map g`, which preserves the
coproduct of the family because colimits of presheaves are computed pointwise; the coproduct of
the ranges therefore receives the restricted coproduct, and local surjectivity passes along that
factorization. -/
private theorem isLocallySurjective_sigmaDesc_range_relocalizeRestrict (B : BigFppfSite.{u})
    (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS') {F : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u} (I : Type u)
    (U : I → Subfunctor F)
    (hU : Presheaf.IsLocallySurjective (BigFppfOver.topology B S' hS')
      (Sigma.desc fun i => (U i).ι)) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (Sigma.desc fun i =>
        (Subfunctor.range ((OverShriek.relocalizeRestrict g).map (U i).ι)).ι) := by
  let R := OverShriek.relocalizeRestrict g
  let G := (Over.map g).op
  let Ui : I → ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := fun i => G ⋙ (U i).toFunctor
  let Wi : I → Subfunctor (R.obj F) := fun i => Subfunctor.range (R.map (U i).ι)
  let e : R.obj (∐ fun i => (U i).toFunctor) ≅ ∐ Ui := by
    show G ⋙ colimit (Discrete.functor fun i => (U i).toFunctor) ≅
      colimit (Discrete.functor Ui)
    exact (colimitCompWhiskeringLeftIsoCompColimit
        (Discrete.functor fun i => (U i).toFunctor) G).symm ≪≫
      HasColimit.isoOfNatIso (Discrete.compNatIsoDiscrete
        (fun i => (U i).toFunctor) ((Functor.whiskeringLeft _ _ _).obj G))
  let t : (∐ Ui) ⟶ ∐ fun i => (Wi i).toFunctor :=
    Limits.Sigma.map fun i => Subfunctor.toRange (R.map (U i).ι)
  let q : (∐ fun i => (Wi i).toFunctor) ⟶ R.obj F := Sigma.desc fun i => (Wi i).ι
  have hι (i : I) : Sigma.ι Ui i ≫ e.inv =
      Functor.whiskerLeft G (Sigma.ι (fun i => (U i).toFunctor) i) := by
    simp [e, Ui, G]
  have hfactor : t ≫ q = e.inv ≫ R.map (Sigma.desc fun i => (U i).ι) := by
    apply Sigma.hom_ext
    intro i
    calc
      Sigma.ι Ui i ≫ t ≫ q = Subfunctor.toRange (R.map (U i).ι) ≫ (Wi i).ι := by
        simp [t, q]
      _ = R.map (U i).ι := by simp [Wi]
      _ = Sigma.ι Ui i ≫ e.inv ≫ R.map (Sigma.desc fun i => (U i).ι) := by
        rw [← Category.assoc, hι]
        show Functor.whiskerLeft G (U i).ι =
          Functor.whiskerLeft G (Sigma.ι (fun i => (U i).toFunctor) i) ≫
            Functor.whiskerLeft G (Sigma.desc fun i => (U i).ι)
        rw [← Functor.whiskerLeft_comp]
        simp
  let : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (R.map (Sigma.desc fun i => (U i).ι)) :=
    isLocallySurjective_relocalizeRestrict_map B S hS S' hS' g
      (Sigma.desc fun i => (U i).ι) hU
  let : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) ((e.hom ≫ t) ≫ q) := by
    rw [Category.assoc, hfactor, ← Category.assoc, e.hom_inv_id, Category.id_comp]
    infer_instance
  exact Presheaf.isLocallySurjective_of_isLocallySurjective
    (BigFppfOver.topology B S hS) (e.hom ≫ t) q

/-! ### Stacks 0B84, part (1) -/

/-- **[Stacks, Tag 0B84] part (1) for an arbitrary algebraically closed extension in the
site.** Let `X` be a quasi-separated — but not necessarily quasi-compact — algebraic space over
a field `k`. If `X` becomes a scheme after base change along some field extension `K/k`, then it
becomes a scheme after base change along any algebraically closed extension `Ω/k` whose spectrum
lies in the site.

This is the reduction of part (1) to part (2) that the source leaves to the reader. The space
`X` is covered by quasi-compact open subspaces `U i` ([Stacks, Tag 03FY] together with
[Stacks, Tag 03H6]), each of which is quasi-separated by [Stacks, Tag 04ZH] part (2) and becomes
a scheme over `K` because being an open immersion is stable under base change. Part (2) gives a
finite separable `k'/k` over which `U i` is a scheme; `k'` embeds in `Ω` because `Ω` is
algebraically closed and `k'/k` is algebraic ([Stacks, Tag 09GU]), so `U i` is a scheme over `Ω`
by transitivity of base change. The restricted family is a Zariski covering of `X_Ω`, so
[Stacks, Tag 03KE] applies. -/
private theorem isRepresentable_relocalizeRestrict_of_isAlgClosed (k K Ω : Type u) [Field k]
    [Field K] [Field Ω] [Algebra k K] [Algebra k Ω] [IsAlgClosed Ω] (B : BigFppfSite.{u})
    (hk : B.Contains (Spec (.of k))) (hK : B.Contains (Spec (.of K)))
    (hΩ : B.Contains (Spec (.of Ω))) (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (hXqs : IsAbsolutelyQuasiSeparated B (Spec (.of k)) hk B.contains_terminal X)
    (hXK : ((OverShriek.relocalizeRestrict (specExtensionHom k K B hk hK)).obj
      X).IsRepresentable) :
    ((OverShriek.relocalizeRestrict (specExtensionHom k Ω B hk hΩ)).obj
      X).IsRepresentable := by
  classical
  -- `X` is covered by quasi-compact open subspaces.
  obtain ⟨I, U, hcover, hatlas⟩ :=
    exists_zariski_cover_affine_etale_atlas B (Spec (.of k)) hk X hX
  have hUqc : ∀ i, IsQuasiCompactSpace B (Spec (.of k)) hk (U i).toFunctor := by
    intro i
    obtain ⟨V, f, W, hV, hsurj, hetale, -, -⟩ := hatlas i
    exact (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B (Spec (.of k)) hk
      (U i).toFunctor (hcover.1 i).1).2
      ⟨V, f, hV, hsurj, isEtale_of_presheaf_etale B (Spec (.of k)) hk hetale⟩
  -- Each member is an open subspace of `X_Ω` after base change.
  have hopenΩ : ∀ i, IsOpenImmersion B (Spec (.of Ω)) hΩ
      ((OverShriek.relocalizeRestrict (specExtensionHom k Ω B hk hΩ)).map (U i).ι) := fun i =>
    presheaf_inverseImage_relocalizeRestrict_map B (Spec (.of Ω)) (Spec (.of k)) hΩ hk
      (specExtensionHom k Ω B hk hΩ) _ inferInstance (hcover.1 i).2
  have hcoverΩ : IsZariskiCover B (Spec (.of Ω)) hΩ I
      (fun i => Subfunctor.range
        ((OverShriek.relocalizeRestrict (specExtensionHom k Ω B hk hΩ)).map (U i).ι)) :=
    ⟨fun i => isOpenSubspace_range_of_isAlgebraicSpace B (Spec (.of Ω)) hΩ
      (isAlgebraicSpace_relocalizeRestrict B (Spec (.of Ω)) (Spec (.of k)) hΩ hk
        (specExtensionHom k Ω B hk hΩ) (U i).toFunctor (hcover.1 i).1) _ (hopenΩ i),
      isLocallySurjective_sigmaDesc_range_relocalizeRestrict B (Spec (.of Ω)) (Spec (.of k))
        hΩ hk (specExtensionHom k Ω B hk hΩ) I U hcover.2⟩
  -- Each member is a scheme after base change to `Ω`.
  have hrepΩ : ∀ i, (Subfunctor.range
      ((OverShriek.relocalizeRestrict (specExtensionHom k Ω B hk hΩ)).map
        (U i).ι)).toFunctor.IsRepresentable := by
    intro i
    have hUiK : ((OverShriek.relocalizeRestrict (specExtensionHom k K B hk hK)).obj
        (U i).toFunctor).IsRepresentable :=
      isRepresentable_of_relativelyRepresentable_of_target B (Spec (.of K)) hK
        ((OverShriek.relocalizeRestrict (specExtensionHom k K B hk hK)).map (U i).ι)
        (presheaf_inverseImage_relocalizeRestrict_map B (Spec (.of K)) (Spec (.of k)) hK hk
          (specExtensionHom k K B hk hK) _ inferInstance (hcover.1 i).2).1 hXK
    have hUiqs : IsAbsolutelyQuasiSeparated B (Spec (.of k)) hk B.contains_terminal
        (U i).toFunctor :=
      isAbsolutelyQuasiSeparated_of_isQuasiSeparated B (Spec (.of k)) hk B.contains_terminal
        (hcover.1 i).1 hXqs
        (isQuasiSeparated_of_mono B (Spec (.of k)) hk (U i).ι inferInstance)
    obtain ⟨k', hk'field, hk'algebra, hk'finite, hk'separable, hk', hUk'⟩ :=
      exists_finite_separable_isRepresentable_relocalizeRestrict k K B hk hK (U i).toFunctor
        (hcover.1 i).1 (hUqc i) hUiqs hUiK
    let := hk'field
    let := hk'algebra
    let := hk'finite
    let := hk'separable
    -- `k'` is algebraic over `k`, so it embeds into the algebraically closed field `Ω`.
    let j : k' →ₐ[k] Ω := IsAlgClosed.lift
    have hUiΩ : ((OverShriek.relocalizeRestrict (specExtensionHom k Ω B hk hΩ)).obj
        (U i).toFunctor).IsRepresentable :=
      isRepresentable_relocalizeRestrict_spec_comp B hk hk' hΩ _
        (CommRingCat.ofHom j.toRingHom) _
        (by
          ext x
          exact j.commutes x) (U i).toFunctor hUk'
    have : Mono ((OverShriek.relocalizeRestrict (specExtensionHom k Ω B hk hΩ)).map (U i).ι) :=
      mono_of_presheaf_isOpenImmersion (hopenΩ i)
    let := hUiΩ
    exact Functor.IsRepresentable.mk'
      (((OverShriek.relocalizeRestrict (specExtensionHom k Ω B hk hΩ)).obj
        (U i).toFunctor).reprW ≪≫
        asIso (Subfunctor.toRange
          ((OverShriek.relocalizeRestrict (specExtensionHom k Ω B hk hΩ)).map (U i).ι)))
  exact isRepresentable_of_isZariskiCover B (Spec (.of Ω)) hΩ
    ((OverShriek.relocalizeRestrict (specExtensionHom k Ω B hk hΩ)).obj X)
    (isAlgebraicSpace_relocalizeRestrict B (Spec (.of Ω)) (Spec (.of k)) hΩ hk
      (specExtensionHom k Ω B hk hΩ) X hX) I _ hcoverΩ hrepΩ

/-- **[Stacks, Tag 0B84] part (1).** Let `k` be a field with algebraic closure `k̄` and let `X`
be a quasi-separated algebraic space over `k`. If there is a field extension `K/k` such that the
base change `X_K` is a scheme, then `X_{k̄}` is a scheme.

The source reduces this to part (2) by covering `X` with quasi-compact open subspaces and omits
the details; they are supplied in
`AlgebraicGeometry.Space.isRepresentable_relocalizeRestrict_of_isAlgClosed`. The spectrum of the
algebraic closure lies in the site automatically. -/
@[stacks 0B84 "part (1)"]
theorem isRepresentable_relocalizeRestrict_algebraicClosure (k K : Type u) [Field k] [Field K]
    [Algebra k K] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (hK : B.Contains (Spec (.of K))) (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (hXqs : IsAbsolutelyQuasiSeparated B (Spec (.of k)) hk B.contains_terminal X)
    (hXK : ((OverShriek.relocalizeRestrict (specExtensionHom k K B hk hK)).obj
      X).IsRepresentable) :
    ((OverShriek.relocalizeRestrict (specExtensionHom k (AlgebraicClosure k) B hk
      (contains_spec_of_isAlgebraic B k (AlgebraicClosure k) hk))).obj X).IsRepresentable :=
  isRepresentable_relocalizeRestrict_of_isAlgClosed k K (AlgebraicClosure k) B hk hK
    (contains_spec_of_isAlgebraic B k (AlgebraicClosure k) hk) X hX hXqs hXK

end AlgebraicGeometry.Space

end
