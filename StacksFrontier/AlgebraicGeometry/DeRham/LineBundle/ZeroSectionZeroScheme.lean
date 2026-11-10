module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineSpaceBundleSmooth
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.AdjointVanishing
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Factorization
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.UnitSectionVanishing
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.FibreCoordinateZeroScheme
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceHomEquivId
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.ZeroSectionFactor
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeRegular
public import StacksFrontier.AlgebraicGeometry.PullbackTensorIso.TensorRightVanishing
public import StacksCore.Tactic.StacksAttribute

/-!
# The image of the zero section is the zero scheme of the tautological section

Let `D` be a line-bundle situation: a scheme `X` carrying an invertible module `L`. Let
`p : Tot(L) ⟶ X` be the total space of `L` and `o : X ⟶ Tot(L)` its zero section. This file
proves **clause (1) of [Stacks, Tag 0F96]**: the closed subscheme `o(X)` of `Tot(L)` is the zero
scheme of the tautological global section of `p^*(L^{⊗ -1})`,

`Z(tautologicalSectionBase) = o(X)`.

## Main results

* `Stacks.LineBundle.Situation.pullbackGlobalSections_tautologicalSection_eq_zero_iff`: **the
  tautological section pulls back to zero along `f : Y ⟶ Tot(L)` exactly when the module
  component of `f` under the functor of points vanishes.**
* `Stacks.LineBundle.Situation.zeroScheme_tautologicalSectionBase_eq_ker_zeroSection`:
  **clause (1) of [Stacks, Tag 0F96]** — the zero scheme of the tautological section is the
  image of the zero section.
* `Stacks.LineBundle.Situation.isRegularSection_tautologicalSection`: **the other half of
  clause (1)** — that section is regular. With the previous result and
  `Stacks.LineBundle.Situation.isRelativeEffectiveCartierDivisor_ker_zeroSection` this is the
  source's statement that `o(X)` is the zero scheme of a *regular* global section of
  `p^*(L^{⊗ -1})`.
* `Situation.isRelativeEffectiveCartierDivisor_zeroScheme_tautologicalSectionBase`, in the
  namespace `Stacks.LineBundle`: that zero scheme is a relative effective Cartier divisor on
  `Tot(L)/X`.

## The argument

Both sides are closed subschemes of `Tot(L)`, so the equality is two inclusions, and each
inclusion is one application of the factorization clause of [Stacks, Tag 02OR]
(`Stacks.Divisors.pullbackSection_eq_zero_iff_factorsThrough_zeroScheme`): a morphism factors
through `Z(s)` exactly when it kills `s`. What makes the two meet is that killing the
tautological section is the same condition as factoring through the zero section, and that is
the identity proved here. It is the composite of four steps, each already isolated:

1. `AlgebraicGeometry.pullbackGlobalSections_app_top_one_eq_zero_iff`: the pulled-back section
   vanishes exactly when the pulled-back morphism `𝒪 ⟶ (p^*L)^{⊗ -1}` does.
2. the tautological section is the tautological functional `p^*L ⟶ 𝒪` read through the duality
   `p^*L ⊗ (p^*L)^{⊗ -1} ≅ 𝒪`, and
   `AlgebraicGeometry.pullback_map_tensorRight_map_eq_zero_iff` removes the tensor factor while
   the two trivializations, being isomorphisms, cannot change whether a composite is zero.
3. `AlgebraicGeometry.pullback_map_homEquiv_symm_eq_zero_iff`: the pullback of the functional
   vanishes exactly when the degree-one inclusion `L ⟶ p_* 𝒪` restricted along `f` does, the
   functional being the adjoint of that inclusion.
4. `Stacks.LineBundle.Situation.totalSpaceHomEquiv_snd` identifies that restriction with the
   module component of `f`, and
   `Stacks.LineBundle.Situation.factorsThrough_zeroSection_iff` says its vanishing is
   factorization through the zero section.

No clause of Tag 0F96 is used, and nothing is assumed about the base scheme of the chow
situation: clause (1) is a statement about the line bundle alone.

## Implementation notes

The statement is in the `basePullbackInverse`/`tautologicalSectionBase` spelling of the ambient
module and its section, which is `p^*(L^{⊗ -1})` with no dualization isomorphism in it;
`Stacks.LineBundle.zeroScheme_tautologicalSectionBase` moves between that spelling and the
`pullbackInverse`/`tautologicalSection` one, in which the chain above is carried out.

The comparison `p_* 𝒪_{Tot(L)} ⟶ (f ≫ p)_* 𝒪_Y` appears in two guises — as the pushforward of
`SheafOfModules.unitToPushforwardObjUnit` followed by `Scheme.Modules.pushforwardComp`, which is
what the adjunction produces, and as the underlying module map of
`Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMapAux`, which is what the functor of points
produces. They agree on sections by `rfl`, which is `comparison_eq` below.

## References

* [Stacks Project, Tag 0F96](https://stacks.math.columbia.edu/tag/0F96)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.LineBundle

variable (D : Situation.{u})

/-- A composite with a split epimorphism in front and a split monomorphism behind vanishes
exactly when the middle factor does. The two one-sided inverses are given explicitly rather than
as `IsIso` instances: the sheafified tensor product of a scheme is typed over a spelling of the
site at which instance search does not find them. -/
private theorem comp_comp_eq_zero_iff {C : Type*} [Category C]
    [CategoryTheory.Limits.HasZeroMorphisms C] {A B B' A' : C}
    {e : A ⟶ B} {ei : B ⟶ A} (hei : ei ≫ e = 𝟙 B)
    (m : B ⟶ B') {e' : B' ⟶ A'} {ei' : A' ⟶ B'} (hei' : e' ≫ ei' = 𝟙 B') :
    e ≫ m ≫ e' = 0 ↔ m = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hm : m = ei ≫ (e ≫ m ≫ e') ≫ ei' := by
      simp only [Category.assoc, hei', Category.comp_id, reassoc_of% hei]
    rw [hm, h, Limits.zero_comp, Limits.comp_zero]
  · rw [h, Limits.zero_comp, Limits.comp_zero]

/-- The two guises of the comparison `p_* 𝒪_{Tot(L)} ⟶ (f ≫ p)_* 𝒪_Y` agree: the one the
pullback–pushforward adjunction produces and the one the functor of points produces. -/
private theorem comparison_eq {Y : Scheme.{u}} (f : Y ⟶ D.totalSpace) :
    (Scheme.Modules.pushforward D.totalSpaceToBase).map
          (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
        (Scheme.Modules.pushforwardComp f D.totalSpaceToBase).hom.app
          (SheafOfModules.unit Y.ringCatSheaf) =
      AlgebraSheaf.underlyingModuleMap (pushforwardAlgebraMapAux D.totalSpaceToBase f) :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun _ =>
    ModuleCat.hom_ext (LinearMap.ext fun _ => rfl))

/-- **The tautological section pulls back to zero along a morphism into the total space exactly
when the module component of that morphism under the functor of points vanishes.** -/
theorem Situation.pullbackGlobalSections_tautologicalSection_eq_zero_iff {Y : Scheme.{u}}
    (f : Y ⟶ D.totalSpace) :
    pullbackGlobalSections f D.pullbackInverse D.tautologicalSection = 0 ↔
      (D.totalSpaceHomEquiv Y f).2 = 0 := by
  have hei : (Scheme.Modules.pullback f).map D.pullbackDuality.hom ≫
      (Scheme.Modules.pullback f).map D.pullbackDuality.inv = 𝟙 _ :=
    Iso.hom_inv_id_map _ _
  have hei' : (Scheme.Modules.pullback f).map
        (Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor D.totalSpace.sheaf.obj
          D.totalSpace.ringCatSheaf.property D.pullbackInverse).hom ≫
      (Scheme.Modules.pullback f).map
        (Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor D.totalSpace.sheaf.obj
          D.totalSpace.ringCatSheaf.property D.pullbackInverse).inv = 𝟙 _ :=
    Iso.hom_inv_id_map _ _
  have hdual : (Scheme.Modules.pullback f).map D.tautologicalSectionHom = 0 ↔
      (Scheme.Modules.pullback f).map D.tautologicalFunctional = 0 := by
    refine Iff.trans ?_ (pullback_map_tensorRight_map_eq_zero_iff f D.pullbackInverse
      D.tautologicalFunctional)
    refine Iff.trans (iff_of_eq (congrArg (fun z => z = 0) ?_))
      (comp_comp_eq_zero_iff hei
        ((Scheme.Modules.pullback f).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨D.totalSpace.sheaf.obj,
            Presheaf.isSheaf_of_isSheaf_comp _ (D.totalSpace.sheaf.obj)
              (forget₂ CommRingCat RingCat) (D.totalSpace.ringCatSheaf.property)⟩).flip.obj
            D.pullbackInverse).map D.tautologicalFunctional))
        hei')
    exact (Functor.map_comp _ _ _).trans
      (congrArg (fun z => (Scheme.Modules.pullback f).map D.pullbackDuality.inv ≫ z)
        (Functor.map_comp _ _ _))
  have hfun : (Scheme.Modules.pullback f).map D.tautologicalFunctional = 0 ↔
      (D.totalSpaceHomEquiv Y f).2 = 0 := by
    refine Iff.trans (pullback_map_homEquiv_symm_eq_zero_iff D.totalSpaceToBase f D.L
      D.genToPushforward) (iff_of_eq (congrArg (fun z => z = 0) ?_))
    exact (congrArg (fun m => D.genToPushforward ≫ m) (comparison_eq D f)).trans
      (D.totalSpaceHomEquiv_snd f).symm
  exact (pullbackGlobalSections_app_top_one_eq_zero_iff f D.pullbackInverse
    D.tautologicalSectionHom).trans (hdual.trans hfun)

/-- **A morphism into the total space factors through the zero scheme of the tautological
section exactly when it factors through the zero section.** This is the junction of the two
universal properties: the factorization clause of [Stacks, Tag 02OR] for the zero scheme, and
the functor of points of the total space for the zero section. -/
theorem Situation.factorsThrough_zeroScheme_tautologicalSection_iff {Y : Scheme.{u}}
    (f : Y ⟶ D.totalSpace) :
    (∃ g : Y ⟶ (Stacks.Divisors.zeroScheme D.totalSpace D.pullbackInverse
        D.tautologicalSection).subscheme,
      g ≫ (Stacks.Divisors.zeroScheme D.totalSpace D.pullbackInverse
        D.tautologicalSection).subschemeι = f) ↔
      ∃ g : Y ⟶ D.X, g ≫ D.zeroSection = f :=
  (Stacks.Divisors.pullbackSection_eq_zero_iff_factorsThrough_zeroScheme D.totalSpace
      D.pullbackInverse D.tautologicalSection f).symm.trans
    ((D.pullbackGlobalSections_tautologicalSection_eq_zero_iff f).trans
      (D.factorsThrough_zeroSection_iff f).symm)

/-- **Clause (1) of [Stacks, Tag 0F96], the zero scheme.** Let `L` be an invertible module on a
scheme `X`, let `p : Tot(L) ⟶ X` be the associated line bundle and let `o : X ⟶ Tot(L)` be its
zero section. Then the closed subscheme `o(X)` of `Tot(L)` is the zero scheme of the tautological
global section of `p^*(L^{⊗ -1})`.

The hypotheses of [Stacks, Tag 0B74] that `X` be locally of finite type over a base scheme with
a dimension function are not needed and are omitted: clause (1) is a statement about the line
bundle alone. -/
@[stacks 0F96 "part (1), the zero scheme"]
theorem Situation.zeroScheme_tautologicalSectionBase_eq_ker_zeroSection :
    Stacks.Divisors.zeroScheme D.totalSpace D.basePullbackInverse D.tautologicalSectionBase =
      D.zeroSection.ker := by
  have hbase : Stacks.Divisors.zeroScheme D.totalSpace D.basePullbackInverse
      D.tautologicalSectionBase =
      Stacks.Divisors.zeroScheme D.totalSpace D.pullbackInverse D.tautologicalSection :=
    (zeroScheme_tautologicalSectionBase D).symm
  rw [hbase]
  rw [← Scheme.IdealSheafData.ker_subschemeι (Stacks.Divisors.zeroScheme D.totalSpace
    D.pullbackInverse D.tautologicalSection)]
  refine le_antisymm ?_ ?_
  · obtain ⟨g, hg⟩ := (D.factorsThrough_zeroScheme_tautologicalSection_iff D.zeroSection).mpr
      ⟨𝟙 D.X, Category.id_comp _⟩
    exact hg ▸ g.le_ker_comp _
  · obtain ⟨g, hg⟩ := (D.factorsThrough_zeroScheme_tautologicalSection_iff
      (Stacks.Divisors.zeroScheme D.totalSpace D.pullbackInverse
        D.tautologicalSection).subschemeι).mp ⟨𝟙 _, Category.id_comp _⟩
    exact hg ▸ g.le_ker_comp _

/-- **Clause (1) of [Stacks, Tag 0F96], regularity of the section.** The tautological global
section of `p^*(L^{⊗ -1})` is a regular section, that is, multiplication by it is injective:
its zero scheme is the image of the zero section, which is an effective Cartier divisor on the
total space by [Stacks, Tag 0B9D]. -/
@[stacks 0F96 "part (1), the section is regular"]
theorem Situation.isRegularSection_tautologicalSection :
    AlgebraicGeometry.IsRegularSection D.totalSpace.sheaf.obj
      D.totalSpace.ringCatSheaf.property
      (SheafOfModules.unitHomEquiv D.pullbackInverse D.tautologicalSectionHom) := by
  have hZ : AlgebraicGeometry.zeroScheme D.totalSpace D.pullbackInverse
      ((SheafOfModules.unitHomEquiv D.pullbackInverse D.tautologicalSectionHom).eval (op ⊤)) =
      D.zeroSection.ker :=
    (zeroScheme_tautologicalSectionBase D).trans
      D.zeroScheme_tautologicalSectionBase_eq_ker_zeroSection
  refine (AlgebraicGeometry.isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection
    D.totalSpace D.pullbackInverse _).mp ?_
  rw [hZ]
  exact D.isRelativeEffectiveCartierDivisor_ker_zeroSection.1

/-- **Clause (1) of [Stacks, Tag 0F96], as a statement about the zero scheme itself**: the zero
scheme of the tautological section is a relative effective Cartier divisor on `Tot(L)/X`. -/
theorem Situation.isRelativeEffectiveCartierDivisor_zeroScheme_tautologicalSectionBase :
    Stacks.Divisors.IsRelativeEffectiveCartierDivisor D.totalSpaceToBase
      (Stacks.Divisors.zeroScheme D.totalSpace D.basePullbackInverse
        D.tautologicalSectionBase) := by
  rw [D.zeroScheme_tautologicalSectionBase_eq_ker_zeroSection]
  exact D.isRelativeEffectiveCartierDivisor_ker_zeroSection

end Stacks.LineBundle

end
