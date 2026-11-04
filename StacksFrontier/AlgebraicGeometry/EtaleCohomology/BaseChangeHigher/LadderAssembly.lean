module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.ConnectingMapCompatibility
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.InjectiveModuleSheafAcyclicity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules

/-!
# The comparison ladder of [Stacks, Tag 0F03]

Let `h ≫ f' = e ≫ g` be a commutative square of schemes as in [Stacks, Tag 0F02] and let
`0 ⟶ F ⟶ I ⟶ Q ⟶ 0` be a short exact sequence of abelian sheaves on the small étale site of `T`.
The proof of [Stacks, Tag 0F03] runs a diagram chase on

```
(f')⁻¹R^q g_* I ──→ (f')⁻¹R^q g_* Q ──δsource──→ (f')⁻¹R^{q+1} g_* F
      |                   |                            |
R^q h_* e⁻¹I  ──→  R^q h_* e⁻¹Q  ──δtarget──→ R^{q+1}h_* e⁻¹F ──→ R^{q+1}h_* e⁻¹I
```

whose data is bundled by `Stacks.EtaleCohomology.HigherBaseChangeLadder`. This file builds such a
ladder, so that the three chases of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/BaseChangeHigher/PositiveDegreeInjectivity.lean`
no longer have it as a hypothesis.

Both rows are the long exact homology sequences of the bounded below derived category attached to
the image of the triangle `F[0] ⟶ I[0] ⟶ Q[0] ⟶ F[0]⟦1⟧` under the derived composites
`R(f')⁻¹ Rg_*` and `Rh_* Re⁻¹`. Both composites are exact functors of triangulated categories, so
the two triangles are distinguished and Mathlib's `homologySequence_exact₁` and
`homologySequence_exact₃` for the homological functor `H⁰` give the exactness. The connecting
morphisms `Stacks.EtaleCohomology.higherBaseChangeδSource` and
`Stacks.EtaleCohomology.higherBaseChangeδTarget` are by construction the ones that homology
sequence attaches to those triangles, read through the identifications
`Stacks.EtaleCohomology.baseChangeSourceIso` and `Stacks.EtaleCohomology.baseChangeTargetIso` of
`(f')⁻¹R^q g_*` and `R^q h_* e⁻¹` with cohomology of the derived composites; so each row of the
ladder is the corresponding homology sequence conjugated by those identifications, and
`Stacks.Cohomology.BaseChange.exact_of_iso_row` carries the exactness across.

The surjectivity of `δsource` is the vanishing of `(f')⁻¹R^{q+1} g_* I`. It is left as a
hypothesis of `Stacks.EtaleCohomology.higherBaseChangeLadder` and discharged separately by
`Stacks.EtaleCohomology.isZero_higherBaseChangeSource_toSheaf_succ` when `I` is the underlying
abelian sheaf of an injective sheaf of modules over a sheaf of rings on the small étale site of
`T`: such a sheaf need not be an injective abelian sheaf, but it is acyclic for the direct image,
which is [Stacks, Tag 03FD]. This is the form in which [Stacks, Tag 0F03] uses the injectivity of
`I` as a sheaf of `ℤ/nℤ`-modules.

Commutativity of the right-hand square is
`Stacks.EtaleCohomology.higherBaseChangeMapAb_comm'`, and the commutativity of the left square is
not part of the data: it is the naturality of the base change map of [Stacks, Tag 0F02].

## Main results

* `Stacks.Cohomology.BaseChange.comp_eq_zero_of_iso` and
  `Stacks.Cohomology.BaseChange.exact_of_iso_row` — a three-term complex and its exactness
  transported along isomorphisms of the three terms.
* `Stacks.EtaleCohomology.higherBaseChangeδSource_comp_baseChangeSourceIso` and
  `Stacks.EtaleCohomology.higherBaseChangeδTarget_comp_baseChangeTargetIso` — the two connecting
  morphisms are the connecting morphisms of the homology sequences of the two derived triangles,
  read through the identifications of the two sides with cohomology of the derived composites.
* `Stacks.EtaleCohomology.epi_higherBaseChangeδSource` — the upper connecting morphism is
  surjective as soon as `(f')⁻¹R^{q+1} g_* I` vanishes.
* `Stacks.EtaleCohomology.exact_higherBaseChangeTarget_map_g_δTarget` and
  `Stacks.EtaleCohomology.exact_higherBaseChangeδTarget_map_f` — the lower row is exact at
  `R^q h_* e⁻¹Q` and at `R^{q+1}h_* e⁻¹F`.
* `Stacks.EtaleCohomology.isZero_higherBaseChangeSource_toSheaf_succ` — `(f')⁻¹R^{q+1} g_*`
  vanishes on the underlying abelian sheaf of an injective sheaf of modules.
* `Stacks.EtaleCohomology.higherBaseChangeLadder` — **the comparison ladder of
  [Stacks, Tag 0F03]**, built from a short exact sequence whose middle term has vanishing
  `(f')⁻¹R^{q+1} g_*`.
* `Stacks.EtaleCohomology.mono_higherBaseChangeMapAb_app_of_shortExact`,
  `Stacks.EtaleCohomology.mono_cokernelDesc_higherBaseChangeMapAb_app_of_shortExact` and
  `Stacks.EtaleCohomology.mono_cokernelMap_higherBaseChangeMapAb_app_of_shortExact` — the three
  assertions of [Stacks, Tag 0F03] with the comparison ladder of their proofs replaced by the
  short exact sequence it is built from.

## Implementation notes

The vanishing hypothesis of `higherBaseChangeLadder` is stated for the functor
`Stacks.EtaleCohomology.higherBaseChangeSource`, not for `R^{q+1} g_*` itself, so that no
property of the inverse image is needed to use it; the two are equivalent because the inverse
image is additive, which is how
`Stacks.EtaleCohomology.isZero_higherBaseChangeSource_toSheaf_succ` proves it.

The instance `CategoryTheory.Abelian.HasExt` needed by the acyclicity of an injective sheaf of
modules has a universe that its type does not determine, so it is introduced by an explicit
`have` rather than left to instance search; the two instances on sheaves of modules over the
small étale site are likewise introduced locally, their module universe being a `max` which does
not unify with a concrete universe by unification alone.

## What is missing

The short exact sequence `0 → F → I → Q → 0` remains an input, so **no declaration here carries
the tag 0F03**: the source constructs the sequence from `F` alone. What a construction needs,
for `F` an abelian sheaf on the small étale site of `T` annihilated by `n`, is the identification
of the abelian sheaves annihilated by `n` with the sheaves of `ℤ/nℤ`-modules, enough injectives
there, and the annihilation by `n` of the quotient. For sheaves of modules over a *sheaf of
rings* this library has enough injectives,
`Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives`, and
`isZero_higherBaseChangeSource_toSheaf_succ` above; what it does not have is either the
constant sheaf of rings `ℤ/nℤ` on the small étale site together with the `ℤ/nℤ`-module structure
on an `n`-torsion abelian sheaf, or — for the alternative category
`Sheaf (smallEtaleTopology T) (ModuleCat (ZMod n))`, where the module structure is sectionwise
and so immediate — the acyclicity of an injective object of that category as an abelian sheaf,
`Stacks.Cohomology.ObjectSections.ext_eq_zero_of_isTorsionFree` being stated for sheaves of
modules over a sheaf of rings only, and `IsGrothendieckAbelian` for it at module universe
`u + 1`, which Mathlib's `ModuleCat.isGrothendieckAbelian` does not give because there the ring
and the modules share a universe.

That gap is closed by
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/BaseChangeHigher/TorsionSheafEmbedding.lean`,
along the first of those two routes: it builds the constant sheaf of rings `ℤ/nℤ` on the small
étale site, reads an abelian sheaf annihilated by `n` as a sheaf of modules over it, and embeds
it in an injective such sheaf as
`Stacks.EtaleCohomology.torsionEtaleInjectiveEmbedding`. The three assertions below are
therefore instantiated there at a constructed sequence, and it is the instantiations, not these
statements, that carry the tag 0F03.

## References

* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
* [Stacks Project, Tag 0F03](https://stacks.math.columbia.edu/tag/0F03)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 01DU](https://stacks.math.columbia.edu/tag/01DU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.Cohomology.BaseChange

/-! ### Transporting a three-term complex along isomorphisms -/

section Conjugation

variable {A : Type*} [Category* A] {A₂ A₃ B₂ B₃ : A} {b : A₂ ⟶ A₃} {b' : B₂ ⟶ B₃}

/-- **A morphism conjugated by two isomorphisms corresponds to the original one.** This is the
form in which a map defined as `u₂.hom ≫ m ≫ u₃.inv` is recognised by `comp_eq_zero_of_iso` and
`exact_of_iso_row`. -/
public theorem conj_comp_hom (u₂ : A₂ ≅ B₂) (u₃ : A₃ ≅ B₃) (m : B₂ ⟶ B₃) :
    (u₂.hom ≫ m ≫ u₃.inv) ≫ u₃.hom = u₂.hom ≫ m := by
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **A morphism corresponding to an epimorphism under isomorphisms of its source and target is
an epimorphism.** -/
public theorem epi_of_iso_comm (u₂ : A₂ ≅ B₂) (u₃ : A₃ ≅ B₃)
    (h₂ : b ≫ u₃.hom = u₂.hom ≫ b') (hb' : Epi b') : Epi b := by
  have hb : Epi (b ≫ u₃.hom) := by rw [h₂]; exact epi_comp _ _
  have : Epi ((b ≫ u₃.hom) ≫ u₃.inv) := epi_comp _ _
  simpa using this

end Conjugation

section TransportRow

variable {A : Type*} [Category* A] [Abelian A] {A₁ A₂ A₃ B₁ B₂ B₃ : A}
  {a : A₁ ⟶ A₂} {b : A₂ ⟶ A₃} {a' : B₁ ⟶ B₂} {b' : B₂ ⟶ B₃}

/-- **A three-term complex transported along isomorphisms of its three terms.** If `a, b`
corresponds to `a', b'` under isomorphisms of the three terms and `a' ≫ b' = 0`, then
`a ≫ b = 0`. -/
public theorem comp_eq_zero_of_iso (u₁ : A₁ ≅ B₁) (u₂ : A₂ ≅ B₂) (u₃ : A₃ ≅ B₃)
    (h₁ : a ≫ u₂.hom = u₁.hom ≫ a') (h₂ : b ≫ u₃.hom = u₂.hom ≫ b') (hz : a' ≫ b' = 0) :
    a ≫ b = 0 := by
  rw [← cancel_mono u₃.hom, Category.assoc, h₂, ← Category.assoc, h₁, Category.assoc, hz,
    comp_zero, zero_comp]

/-- **Exactness of a three-term complex transported along isomorphisms of its three terms.** -/
public theorem exact_of_iso_row (u₁ : A₁ ≅ B₁) (u₂ : A₂ ≅ B₂) (u₃ : A₃ ≅ B₃)
    (h₁ : a ≫ u₂.hom = u₁.hom ≫ a') (h₂ : b ≫ u₃.hom = u₂.hom ≫ b') (hz : a' ≫ b' = 0)
    (hex : (ShortComplex.mk a' b' hz).Exact) :
    (ShortComplex.mk a b (comp_eq_zero_of_iso u₁ u₂ u₃ h₁ h₂ hz)).Exact :=
  ShortComplex.exact_of_iso (ShortComplex.isoMk u₁ u₂ u₃ h₁.symm h₂.symm).symm hex

end TransportRow

end Stacks.Cohomology.BaseChange

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
attribute [local instance] Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus

section LadderRows

variable {X' Y S' T : Scheme.{u}} (f' : X' ⟶ S') (g : T ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T)
  (q : ℕ) {S : ShortComplex (Sheaf (smallEtaleTopology T) Ab.{u + 1})}

/-- The image under `R(f')⁻¹ Rg_*` of the triangle of a short exact sequence is distinguished,
that composite being an exact functor of triangulated categories. -/
public theorem mapTriangle_derivedBaseChangeSource_distinguished (hS : S.ShortExact) :
    (derivedBaseChangeSource f' g).mapTriangle.obj
        (Stacks.Cohomology.BaseChange.singleTrianglePlus hS) ∈
      distTriang (DerivedCategory.Plus (Sheaf (smallEtaleTopology X') Ab.{u + 1})) :=
  (derivedBaseChangeSource f' g).map_distinguished _
    (Stacks.DerivedIndexing.singleTrianglePlus_distinguished hS)

/-- The image under `Rh_* Re⁻¹` of the triangle of a short exact sequence is distinguished, that
composite being an exact functor of triangulated categories. -/
public theorem mapTriangle_derivedBaseChangeTarget_distinguished (hS : S.ShortExact) :
    (derivedBaseChangeTarget h e).mapTriangle.obj
        (Stacks.Cohomology.BaseChange.singleTrianglePlus hS) ∈
      distTriang (DerivedCategory.Plus (Sheaf (smallEtaleTopology X') Ab.{u + 1})) :=
  (derivedBaseChangeTarget h e).map_distinguished _
    (Stacks.DerivedIndexing.singleTrianglePlus_distinguished hS)

/-- **The defining property of the upper connecting morphism.** Read through the identification
`baseChangeSourceIso` of `(f')⁻¹R^q g_*` with cohomology of `R(f')⁻¹ Rg_*`, the connecting
morphism `higherBaseChangeδSource` is the connecting morphism of the long exact homology sequence
of the derived triangle. -/
public theorem higherBaseChangeδSource_comp_baseChangeSourceIso (hS : S.ShortExact) :
    higherBaseChangeδSource f' g q hS ≫ (baseChangeSourceIso f' g (q + 1)).hom.app S.X₁ =
      (baseChangeSourceIso f' g q).hom.app S.X₃ ≫
        (DerivedCategory.Plus.homologyFunctor
            (Sheaf (smallEtaleTopology X') Ab.{u + 1}) 0).homologySequenceδ
          ((derivedBaseChangeSource f' g).mapTriangle.obj
            (Stacks.Cohomology.BaseChange.singleTrianglePlus hS))
          (q : ℤ) ((q + 1 : ℕ) : ℤ) rfl :=
  Stacks.Cohomology.BaseChange.conj_comp_hom ((baseChangeSourceIso f' g q).app S.X₃)
    ((baseChangeSourceIso f' g (q + 1)).app S.X₁) _

/-- **The defining property of the lower connecting morphism.** Read through the identification
`baseChangeTargetIso` of `R^q h_* e⁻¹` with cohomology of `Rh_* Re⁻¹`, the connecting morphism
`higherBaseChangeδTarget` is the connecting morphism of the long exact homology sequence of the
derived triangle. -/
public theorem higherBaseChangeδTarget_comp_baseChangeTargetIso (hS : S.ShortExact) :
    higherBaseChangeδTarget h e q hS ≫ (baseChangeTargetIso h e (q + 1)).hom.app S.X₁ =
      (baseChangeTargetIso h e q).hom.app S.X₃ ≫
        (DerivedCategory.Plus.homologyFunctor
            (Sheaf (smallEtaleTopology X') Ab.{u + 1}) 0).homologySequenceδ
          ((derivedBaseChangeTarget h e).mapTriangle.obj
            (Stacks.Cohomology.BaseChange.singleTrianglePlus hS))
          (q : ℤ) ((q + 1 : ℕ) : ℤ) rfl :=
  Stacks.Cohomology.BaseChange.conj_comp_hom ((baseChangeTargetIso h e q).app S.X₃)
    ((baseChangeTargetIso h e (q + 1)).app S.X₁) _

/-- **The upper row is a complex at `(f')⁻¹R^q g_* Q`.** -/
public theorem higherBaseChangeSource_map_g_comp_δSource (hS : S.ShortExact) :
    (higherBaseChangeSource f' g q).map S.g ≫ higherBaseChangeδSource f' g q hS = 0 :=
  Stacks.Cohomology.BaseChange.comp_eq_zero_of_iso
    ((baseChangeSourceIso f' g q).app S.X₂) ((baseChangeSourceIso f' g q).app S.X₃)
    ((baseChangeSourceIso f' g (q + 1)).app S.X₁)
    ((baseChangeSourceIso f' g q).hom.naturality S.g)
    (higherBaseChangeδSource_comp_baseChangeSourceIso f' g q hS)
    ((DerivedCategory.Plus.homologyFunctor
      (Sheaf (smallEtaleTopology X') Ab.{u + 1}) 0).comp_homologySequenceδ _
      (mapTriangle_derivedBaseChangeSource_distinguished f' g hS) _ _ rfl)

/-- **The lower row is a complex at `R^q h_* e⁻¹Q`.** -/
public theorem higherBaseChangeTarget_map_g_comp_δTarget (hS : S.ShortExact) :
    (higherBaseChangeTarget h e q).map S.g ≫ higherBaseChangeδTarget h e q hS = 0 :=
  Stacks.Cohomology.BaseChange.comp_eq_zero_of_iso
    ((baseChangeTargetIso h e q).app S.X₂) ((baseChangeTargetIso h e q).app S.X₃)
    ((baseChangeTargetIso h e (q + 1)).app S.X₁)
    ((baseChangeTargetIso h e q).hom.naturality S.g)
    (higherBaseChangeδTarget_comp_baseChangeTargetIso h e q hS)
    ((DerivedCategory.Plus.homologyFunctor
      (Sheaf (smallEtaleTopology X') Ab.{u + 1}) 0).comp_homologySequenceδ _
      (mapTriangle_derivedBaseChangeTarget_distinguished h e hS) _ _ rfl)

/-- **The lower row is a complex at `R^{q+1}h_* e⁻¹F`.** -/
public theorem higherBaseChangeδTarget_comp_map_f (hS : S.ShortExact) :
    higherBaseChangeδTarget h e q hS ≫ (higherBaseChangeTarget h e (q + 1)).map S.f = 0 :=
  Stacks.Cohomology.BaseChange.comp_eq_zero_of_iso
    ((baseChangeTargetIso h e q).app S.X₃) ((baseChangeTargetIso h e (q + 1)).app S.X₁)
    ((baseChangeTargetIso h e (q + 1)).app S.X₂)
    (higherBaseChangeδTarget_comp_baseChangeTargetIso h e q hS)
    ((baseChangeTargetIso h e (q + 1)).hom.naturality S.f)
    ((DerivedCategory.Plus.homologyFunctor
      (Sheaf (smallEtaleTopology X') Ab.{u + 1}) 0).homologySequenceδ_comp _
      (mapTriangle_derivedBaseChangeTarget_distinguished h e hS) _ _ rfl)

/-- **The lower row is exact at `R^q h_* e⁻¹Q`.** -/
public theorem exact_higherBaseChangeTarget_map_g_δTarget (hS : S.ShortExact) :
    (ShortComplex.mk ((higherBaseChangeTarget h e q).map S.g) (higherBaseChangeδTarget h e q hS)
      (higherBaseChangeTarget_map_g_comp_δTarget h e q hS)).Exact :=
  Stacks.Cohomology.BaseChange.exact_of_iso_row
    ((baseChangeTargetIso h e q).app S.X₂) ((baseChangeTargetIso h e q).app S.X₃)
    ((baseChangeTargetIso h e (q + 1)).app S.X₁)
    ((baseChangeTargetIso h e q).hom.naturality S.g)
    (higherBaseChangeδTarget_comp_baseChangeTargetIso h e q hS) _
    ((DerivedCategory.Plus.homologyFunctor
      (Sheaf (smallEtaleTopology X') Ab.{u + 1}) 0).homologySequence_exact₃ _
      (mapTriangle_derivedBaseChangeTarget_distinguished h e hS) _ _ rfl)

/-- **The lower row is exact at `R^{q+1}h_* e⁻¹F`.** -/
public theorem exact_higherBaseChangeδTarget_map_f (hS : S.ShortExact) :
    (ShortComplex.mk (higherBaseChangeδTarget h e q hS)
      ((higherBaseChangeTarget h e (q + 1)).map S.f)
      (higherBaseChangeδTarget_comp_map_f h e q hS)).Exact :=
  Stacks.Cohomology.BaseChange.exact_of_iso_row
    ((baseChangeTargetIso h e q).app S.X₃) ((baseChangeTargetIso h e (q + 1)).app S.X₁)
    ((baseChangeTargetIso h e (q + 1)).app S.X₂)
    (higherBaseChangeδTarget_comp_baseChangeTargetIso h e q hS)
    ((baseChangeTargetIso h e (q + 1)).hom.naturality S.f) _
    ((DerivedCategory.Plus.homologyFunctor
      (Sheaf (smallEtaleTopology X') Ab.{u + 1}) 0).homologySequence_exact₁ _
      (mapTriangle_derivedBaseChangeTarget_distinguished h e hS) _ _ rfl)

/-- **The upper connecting morphism is surjective when `(f')⁻¹R^{q+1} g_* I` vanishes.** The
upper row is exact at `(f')⁻¹R^{q+1} g_* F`, and the term to its right is
`(f')⁻¹R^{q+1} g_* I`. -/
public theorem epi_higherBaseChangeδSource (hS : S.ShortExact)
    (hI : IsZero ((higherBaseChangeSource f' g (q + 1)).obj S.X₂)) :
    Epi (higherBaseChangeδSource f' g q hS) := by
  have hex := (DerivedCategory.Plus.homologyFunctor
    (Sheaf (smallEtaleTopology X') Ab.{u + 1}) 0).homologySequence_exact₁ _
    (mapTriangle_derivedBaseChangeSource_distinguished f' g hS) (q : ℤ) ((q + 1 : ℕ) : ℤ) rfl
  have hzero : IsZero (((DerivedCategory.Plus.homologyFunctor
      (Sheaf (smallEtaleTopology X') Ab.{u + 1}) 0).shift ((q + 1 : ℕ) : ℤ)).obj
      ((derivedBaseChangeSource f' g).obj
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf (smallEtaleTopology T) Ab.{u + 1}) 0).obj S.X₂))) :=
    IsZero.of_iso hI ((baseChangeSourceIso f' g (q + 1)).app S.X₂).symm
  have hepi : Epi ((DerivedCategory.Plus.homologyFunctor
      (Sheaf (smallEtaleTopology X') Ab.{u + 1}) 0).homologySequenceδ
      ((derivedBaseChangeSource f' g).mapTriangle.obj
        (Stacks.Cohomology.BaseChange.singleTrianglePlus hS))
      (q : ℤ) ((q + 1 : ℕ) : ℤ) rfl) :=
    hex.epi_f_iff.2 (hzero.eq_of_tgt _ 0)
  exact Stacks.Cohomology.BaseChange.epi_of_iso_comm
    ((baseChangeSourceIso f' g q).app S.X₃) ((baseChangeSourceIso f' g (q + 1)).app S.X₁)
    (higherBaseChangeδSource_comp_baseChangeSourceIso f' g q hS) hepi

end LadderRows

/-! ### The vanishing of the higher direct images of an injective sheaf of modules -/

section Vanishing

variable {X' S' T : Scheme.{u}} (f' : X' ⟶ S') (g : T ⟶ S')
  (R : Sheaf (smallEtaleTopology T) RingCat.{u + 1}) (I : SheafOfModules.{u + 1} R)
  [Injective I] (q : ℕ)

/-- **`(f')⁻¹R^{q+1} g_*` vanishes on the underlying abelian sheaf of an injective sheaf of
modules.** The underlying abelian sheaf of an injective sheaf of `R`-modules need not be an
injective abelian sheaf, but it is acyclic for the direct image, which is [Stacks, Tag 03FD]; the
inverse image is additive, so it preserves the vanishing. -/
public theorem isZero_higherBaseChangeSource_toSheaf_succ :
    IsZero ((higherBaseChangeSource f' g (q + 1)).obj ((SheafOfModules.toSheaf R).obj I)) := by
  have : CategoryTheory.HasExt.{u + 1} (Sheaf (smallEtaleTopology T) Ab.{u + 1}) :=
    Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{u + 1, u, u}
  exact Functor.map_isZero (smallEtalePullbackAb f')
    (Stacks.Cohomology.InjectiveModuleSheafAcyclicity.isZero_higherDirectImage_toSheaf_succ.{u}
      (smallEtaleTopology S') (smallEtaleTopology T) (smallEtaleBaseChange g) R I q)

end Vanishing

/-! ### The ladder -/

section Ladder

variable {X' Y S' T : Scheme.{u}} (f' : X' ⟶ S') (g : T ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T)
  (w : h ≫ f' = e ≫ g) (q : ℕ)

/-- **The comparison ladder of [Stacks, Tag 0F03]**, attached to a short exact sequence
`0 ⟶ F ⟶ I ⟶ Q ⟶ 0` of abelian sheaves on the small étale site of `T` whose middle term has
vanishing `(f')⁻¹R^{q+1} g_*`.

The two rows are the long exact homology sequences of the images of the triangle of the sequence
under the derived composites `R(f')⁻¹ Rg_*` and `Rh_* Re⁻¹`, read through the identifications of
`(f')⁻¹R^q g_*` and `R^q h_* e⁻¹` with cohomology of those composites; the surjectivity of the
upper connecting morphism is the vanishing hypothesis, and the commutativity of the right-hand
square is `higherBaseChangeMapAb_comm'`. -/
public def higherBaseChangeLadder
    {S : ShortComplex (Sheaf (smallEtaleTopology T) Ab.{u + 1})} (hS : S.ShortExact)
    (hI : IsZero ((higherBaseChangeSource f' g (q + 1)).obj S.X₂)) :
    HigherBaseChangeLadder f' g h e w q S.f S.g where
  δsource := higherBaseChangeδSource f' g q hS
  δtarget := higherBaseChangeδTarget h e q hS
  zero_source := higherBaseChangeSource_map_g_comp_δSource f' g q hS
  zero_target := higherBaseChangeTarget_map_g_comp_δTarget h e q hS
  zero_target_comp := higherBaseChangeδTarget_comp_map_f h e q hS
  exact_target := exact_higherBaseChangeTarget_map_g_δTarget h e q hS
  exact_target_comp := exact_higherBaseChangeδTarget_map_f h e q hS
  epi_δsource := epi_higherBaseChangeδSource f' g q hS hI
  comm := higherBaseChangeMapAb_comm' f' g h e w q hS

end Ladder

/-! ### The three assertions of [Stacks, Tag 0F03] given a short exact sequence -/

section Assertions

variable {X S S' X' T Y : Scheme.{u}} (f : X ⟶ S) (n : ℤ) (q : ℕ)
  (s : S' ⟶ S) (p : X' ⟶ X) (f' : X' ⟶ S') (g : T ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T)

/-- **Part (1) of [Stacks, Tag 0F03] given a short exact sequence `0 → F → I → Q → 0`.** With
`f : X ⟶ S` and `n` as in [Stacks, Tag 0F02], assume `BC(f, n, q)`, let

```
X  ←--  X'  ←-h-  Y
|f      |f'       |e
S  ←--  S'  ←-g-  T
```

be a commutative diagram with `X' = X ×_S S'` and `Y = X' ×_{S'} T` and `g` quasi-compact and
quasi-separated, and let `0 → F → I → Q → 0` be a short exact sequence of abelian sheaves on the
small étale site of `T` whose three terms are annihilated by `n` and whose middle term has
vanishing `(f')⁻¹R^{q+1} g_*`. Then the base change map
`(f')⁻¹R^{q+1} g_* F ⟶ R^{q+1} h_* e⁻¹F` is injective.

This is `mono_higherBaseChangeMapAb_app` with its comparison ladder supplied by
`higherBaseChangeLadder`. -/
public theorem mono_higherBaseChangeMapAb_app_of_shortExact (hbc : BaseChangeHolds f n (q : ℤ))
    (sq₁ : IsPullback p f' f s) (sq : IsPullback h e f' g)
    [QuasiCompact g] [QuasiSeparated g]
    {Z : ShortComplex (Sheaf (smallEtaleTopology T) Ab.{u + 1})} (hZ : Z.ShortExact)
    (hvanish : IsZero ((higherBaseChangeSource f' g (q + 1)).obj Z.X₂))
    (hF : ∀ (U : T.Etale) (x : Z.X₁.obj.obj (Opposite.op U)), n • x = 0)
    (hI : ∀ (U : T.Etale) (x : Z.X₂.obj.obj (Opposite.op U)), n • x = 0)
    (hQ : ∀ (U : T.Etale) (x : Z.X₃.obj.obj (Opposite.op U)), n • x = 0) :
    Mono ((higherBaseChangeMapAb f' g h e sq.w (q + 1)).app Z.X₁) :=
  mono_higherBaseChangeMapAb_app f n q s p f' g h e hbc sq₁ sq Z.f Z.g hF hI hQ
    (higherBaseChangeLadder f' g h e sq.w q hZ hvanish)

/-- **Part (3) of [Stacks, Tag 0F03] given a short exact sequence `0 → F → I → Q → 0`.** In the
situation of `mono_higherBaseChangeMapAb_app_of_shortExact`,

`Coker((f')⁻¹R^{q+1} g_* F ⟶ R^{q+1} h_* e⁻¹F) ⊂ R^{q+1} h_* e⁻¹I`,

the inclusion being the canonical map induced by `R^{q+1}h_* e⁻¹(F ⟶ I)`. This is
`mono_cokernelDesc_higherBaseChangeMapAb_app` with its comparison ladder supplied by
`higherBaseChangeLadder`. -/
public theorem mono_cokernelDesc_higherBaseChangeMapAb_app_of_shortExact
    (hbc : BaseChangeHolds f n (q : ℤ))
    (sq₁ : IsPullback p f' f s) (sq : IsPullback h e f' g)
    [QuasiCompact g] [QuasiSeparated g]
    {Z : ShortComplex (Sheaf (smallEtaleTopology T) Ab.{u + 1})} (hZ : Z.ShortExact)
    (hvanish : IsZero ((higherBaseChangeSource f' g (q + 1)).obj Z.X₂))
    (hF : ∀ (U : T.Etale) (x : Z.X₁.obj.obj (Opposite.op U)), n • x = 0)
    (hI : ∀ (U : T.Etale) (x : Z.X₂.obj.obj (Opposite.op U)), n • x = 0)
    (hQ : ∀ (U : T.Etale) (x : Z.X₃.obj.obj (Opposite.op U)), n • x = 0) :
    Mono (cokernel.desc ((higherBaseChangeMapAb f' g h e sq.w (q + 1)).app Z.X₁)
      ((higherBaseChangeTarget h e (q + 1)).map Z.f)
      (higherBaseChangeMapAb_app_comp_map_eq_zero q f' g h e sq Z.f Z.g
        (higherBaseChangeLadder f' g h e sq.w q hZ hvanish))) :=
  mono_cokernelDesc_higherBaseChangeMapAb_app f n q s p f' g h e hbc sq₁ sq Z.f Z.g hF hI hQ
    (higherBaseChangeLadder f' g h e sq.w q hZ hvanish)

/-- **Part (2) of [Stacks, Tag 0F03] given two short exact sequences with the same middle
term.** In the situation of `mono_higherBaseChangeMapAb_app_of_shortExact`, if `F ⊂ G` with `G`
annihilated by `n`, then

`Coker((f')⁻¹R^{q+1}g_* F → R^{q+1}h_* e⁻¹F) ⊂ Coker((f')⁻¹R^{q+1}g_* G → R^{q+1}h_* e⁻¹G)`,

the inclusion being the map induced on cokernels by the naturality square of the base change
map. As in the source, the hypotheses transcribe the choice `F ⊂ G ⊂ I`: the two short exact
sequences are `0 → F → I → Q_F → 0` and `0 → G → I → Q_G → 0`, with the same middle term `I`.
This is `mono_cokernelMap_higherBaseChangeMapAb_app` with its two comparison ladders supplied by
`higherBaseChangeLadder`. -/
public theorem mono_cokernelMap_higherBaseChangeMapAb_app_of_shortExact
    (hbc : BaseChangeHolds f n (q : ℤ))
    (sq₁ : IsPullback p f' f s) (sq : IsPullback h e f' g)
    [QuasiCompact g] [QuasiSeparated g]
    {F G I QF QG : Sheaf (smallEtaleTopology T) Ab.{u + 1}} (i : F ⟶ G) (k : G ⟶ I)
    (γF : I ⟶ QF) (γG : I ⟶ QG) (hi : Mono i)
    {hzF : (i ≫ k) ≫ γF = 0} {hzG : k ≫ γG = 0}
    (hZF : (ShortComplex.mk (i ≫ k) γF hzF).ShortExact)
    (hZG : (ShortComplex.mk k γG hzG).ShortExact)
    (hvanish : IsZero ((higherBaseChangeSource f' g (q + 1)).obj I))
    (hF : ∀ (U : T.Etale) (x : F.obj.obj (Opposite.op U)), n • x = 0)
    (hG : ∀ (U : T.Etale) (x : G.obj.obj (Opposite.op U)), n • x = 0)
    (hI : ∀ (U : T.Etale) (x : I.obj.obj (Opposite.op U)), n • x = 0)
    (hQF : ∀ (U : T.Etale) (x : QF.obj.obj (Opposite.op U)), n • x = 0)
    (hQG : ∀ (U : T.Etale) (x : QG.obj.obj (Opposite.op U)), n • x = 0) :
    Mono (cokernel.map ((higherBaseChangeMapAb f' g h e sq.w (q + 1)).app F)
      ((higherBaseChangeMapAb f' g h e sq.w (q + 1)).app G)
      ((higherBaseChangeSource f' g (q + 1)).map i)
      ((higherBaseChangeTarget h e (q + 1)).map i)
      ((higherBaseChangeMapAb f' g h e sq.w (q + 1)).naturality i).symm) :=
  mono_cokernelMap_higherBaseChangeMapAb_app f n q s p f' g h e hbc sq₁ sq i k γF γG hi
    hF hG hI hQF hQG (higherBaseChangeLadder f' g h e sq.w q hZF hvanish)
    (higherBaseChangeLadder f' g h e sq.w q hZG hvanish)

end Assertions

end Stacks.EtaleCohomology

end
