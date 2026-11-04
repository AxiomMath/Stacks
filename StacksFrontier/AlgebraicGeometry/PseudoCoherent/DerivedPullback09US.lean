module

public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentPullbackPushforward
public import StacksFrontier.AlgebraicGeometry.Modules.SpecFieldDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Morphisms.PseudoCoherentFrom
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffinePairLocality
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedRelative09UU
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedTensorProjection
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeAbsolute
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeComp09UT
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeDevissage
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeTorIndependentBaseChange
import StacksFrontier.AlgebraicGeometry.ClosedImmersion.TopoiBridge.ClosedImmersion
import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.ClosedImmersionPushforward
import StacksFrontier.AlgebraicGeometry.Perfect.TorIndependence
import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineOpenSideCondition
import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPushforwardRelative
import StacksFrontier.Homology.PseudoCoherent.Relative.Finite
import StacksFrontier.RingTheory.PseudoCoherentMap.Absolute
import StacksFrontier.RingTheory.PseudoCoherentMap.Flat
import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles
import StacksFrontier.Topology.Sheaves.Functors.Module.FlatPullback
import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackComp
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Derived pullback of a relatively pseudo-coherent complex

Let `f : X ⟶ Y` be a pseudo-coherent morphism of schemes, let `g : Y ⟶ S` be locally of finite
type and let `E` be an object of `D(𝒪_Y)` which is `m`-pseudo-coherent relative to `S`. Then the
derived pullback `Lf^*E` is `m`-pseudo-coherent relative to `S`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.IsPseudoCoherentFrom.exists_isLE`: a relatively
  `m`-pseudo-coherent object on an affine scheme over an affine base is bounded above.
* `AlgebraicGeometry.Scheme.Hom.isModulePseudoCoherentFrom_sections_of_isClosedImmersion`: for a
  closed immersion `i : U ⟶ Z` of affine schemes with pseudo-coherent map on global sections,
  `Γ(U, ⊤)` is an `m`-pseudo-coherent `Γ(Z, ⊤)`-module for every `m`.
* `AlgebraicGeometry.kernelAnnihilatesPullbackPushforward_of_isPullback`,
  `AlgebraicGeometry.baseChangeIsoOfKernelAnnihilates` and
  `AlgebraicGeometry.derivedBaseChangeIsoOfIso`: the flat case of Stacks 0E23.
* `AlgebraicGeometry.nonempty_derivedPullbackPushforwardIso`: that case in the shape
  Stacks 09UR consumes, and
  `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_derivedPullback_of_flat`: Stacks 09UR with
  flatness in place of Tor independence.
* `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_comp_derivedPullback`: **Stacks 09US.**

## Implementation notes

The proof is affine-local and runs, on a chain `U ⟶ V ⟶ W` of affine charts, over the
factorization of `U ⟶ V` through a closed immersion into an affine space `𝔸ⁿ_V`, which is the base
change of `𝔸ⁿ_W` along `V ⟶ W`. Stacks 09UR carries the hypothesis on `E` to that base change,
Stacks 09UT crosses the flat projection `𝔸ⁿ_V ⟶ V`, and Stacks 09UU replaces the conclusion on
`U` by one on `𝔸ⁿ_V` for the derived pushforward along the closed immersion `i`. What is left is
the one step of the source that is not formal: the projection formula identifies `Ri_*Li^*G` with
`Ri_*𝒪_U ⊗^𝐋 G`, the sheaf `Ri_*𝒪_U` is the sheafification of the pseudo-coherent
`Γ(Z, ⊤)`-module `Γ(U, ⊤)`, and the dévissage of
`AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_map_of_modulePseudoCoherent` over a
bounded-above finite free resolution of that module reduces the claim to `𝒪_Z ⊗^𝐋 G = G`.

The boundedness input of the dévissage is unconditional: the derived tensor product of a scheme
adds cohomological bounds with no flatness hypothesis
(`AlgebraicGeometry.Scheme.Modules.isLE_derivedTensorProduct`), so the auxiliary property that
the dévissage carries on the terms of the resolution may be taken to be trivial.

**The flat case of Stacks 0E23, proved here.** The one step of the source that is not internal
to relative pseudo-coherence is the base change of Stacks 09UR, and the only thing Stacks 09UR
needs beyond its own covers is Stacks 0E23 at the chart square. Every square at which that
happens in this proof has its horizontal morphism FLAT: it is
`AlgebraicGeometry.AffineSpace.map` of a restriction of the flat projection `𝔸ᵈ_W ⟶ W`. For a
flat square the Tor independence of 0E23 is automatic and the derived statement collapses onto an
underived one, because all four functors are then derived functors of exact functors — `Ri_*`
and `Ri'_*` by Stacks 08KS, `Lf^*` and `Lg^*` by Stacks 02N4. The section "Flat base change
along a closed immersion" below carries this out in four steps:

* `AlgebraicGeometry.kernelAnnihilatesPullbackPushforward_of_isPullback`: the kernel of the
  comorphism of the base-changed immersion `i'` annihilates `f^*(i_*M)` section by section —
  geometrically, the base-changed closed subscheme is cut out by the pulled-back ideal. A section
  is zero iff all its germs are; `Stacks.ModuleSkyscraper.pullbackStalkIso` presents the stalk of
  `f^*(i_*M)` at `x'` as `𝒪_{X',x'} ⊗_{𝒪_{X,f x'}} (i_*M)_{f x'}`; off the image of `i'` the
  second factor vanishes because `Set.range i' = f⁻¹(Set.range i)`; on the image, at `x' = i' w`,
  the germ lies in `ker(𝒪_{X',i'w} ⟶ 𝒪_{Z',w})`, which
  `Stacks.Flatness.ker_stalkMap_of_isPullback` identifies with the ideal generated by the image
  of `ker(𝒪_{X,i(gw)} ⟶ 𝒪_{Z,gw})`, and a generator `φ c` moves across a decomposable element as
  `φ c • (s ⊗ₜ p) = s ⊗ₜ (c • p)`, with `c • p = 0` by
  `AlgebraicGeometry.smul_stalk_pushforward_eq_zero` — the kernel of a germ map of a closed
  immersion kills the stalk of a pushforward, by
  `Stacks.Flatness.ker_stalkMap_eq_map_germ` and Stacks 08KS.
* `AlgebraicGeometry.baseChangeIsoOfKernelAnnihilates`: the underived isomorphism
  `i_* ⋙ f^* ≅ g^* ⋙ i'_*`, from that annihilation through the unit and counit of Stacks 08KS.
* `AlgebraicGeometry.derivedBaseChangeIsoOfIso`: the derived isomorphism
  `Ri_* ⋙ Lf^* ≅ Lg^* ⋙ Ri'_*` obtained from it, since `Functor.mapDerivedCategory` is a functor
  of the exact functor.
* `AlgebraicGeometry.nonempty_derivedPullbackPushforwardIso`: the conclusion in the shape
  Stacks 09UR consumes. The conclusion is an isomorphism rather than invertibility of the
  canonical base change map of Stacks 08HY, because
  `AlgebraicGeometry.isPseudoCoherentFromAfterPushforward_baseChange_of_iso` uses that map only
  through `CategoryTheory.asIso`.

`AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_derivedPullback_of_flat` is then Stacks 09UR
with its Tor independence hypothesis replaced by flatness of the base change morphism, and
Stacks 09US below needs no hypothesis beyond those of the source.

Only the flat case of Stacks 0E23 is treated: the hypothesis of Stacks 0E23 is Tor independence
of `Z` and `X'` over `X`, not flatness of `f`.

**Boundedness above is reflected, not constructed.** Relative pseudo-coherence bounds the
cohomology of an object only after pushforward along a closed immersion into an affine space,
where `AlgebraicGeometry.exists_isLE_of_isPseudoCoherentFrom` applies; the bound comes back
because that pushforward is faithful and exact.

The derived categories are the ones provided by `CategoryTheory.HasDerivedCategory.standard`,
which is made a local instance; there is no global instance, so a user of these results makes the
same declaration.

## References

* [The Stacks Project, Lemma 37.59.16 (09US)](https://stacks.math.columbia.edu/tag/09US)
* [The Stacks Project, Lemma 37.59.15 (09UR)](https://stacks.math.columbia.edu/tag/09UR)
* [The Stacks Project, Lemma 37.59.11 (09UT)](https://stacks.math.columbia.edu/tag/09UT)
* [The Stacks Project, Lemma 37.59.12 (09UU)](https://stacks.math.columbia.edu/tag/09UU)
* [The Stacks Project, Lemma 36.22.9 (0E23)](https://stacks.math.columbia.edu/tag/0E23)
* [The Stacks Project, Lemma 20.47.6 (0B55)](https://stacks.math.columbia.edu/tag/0B55)
* [The Stacks Project, Lemma 26.4.1 (01QO)](https://stacks.math.columbia.edu/tag/01QO)
* [The Stacks Project, Lemma 29.2.1 (08KS)](https://stacks.math.columbia.edu/tag/08KS)
* [The Stacks Project, Lemma 26.21.1 (02N4)](https://stacks.math.columbia.edu/tag/02N4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.AffineTilde (tildeOf)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward derivedPullback)
open Stacks.DerivedTensor.RingedSite (canonicalDerivedTensorProduct)

namespace AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ### Reflecting boundedness above through a faithful exact functor -/

/-- Boundedness above only depends on the isomorphism class of a derived object. -/
private theorem isLE_of_iso {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {A B : DerivedCategory C} (e : A ≅ B) (n : ℤ) (hA : A.IsLE n) : B.IsLE n := by
  have := hA
  rw [DerivedCategory.isLE_iff]
  intro i hi
  exact (DerivedCategory.isZero_of_isLE A n i hi).of_iso
    ((DerivedCategory.homologyFunctor C i).mapIso e.symm)

/-- An exact additive functor commutes with the cohomology of a cochain complex. -/
private def mapHomologicalComplexCompHomologyFunctorIso {C : Type*} [Category C] [Abelian C]
    {D : Type*} [Category D] [Abelian D] (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (n : ℤ) :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) n ≅
      HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n ⋙ F :=
  NatIso.ofComponents (fun L ↦ (L.sc n).mapHomologyIso F) (fun φ ↦
    ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) n).map φ) F)

/-- An exact additive functor commutes with the cohomology of derived objects. -/
private def mapDerivedCategoryCompHomologyFunctorIso {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] {D : Type*} [Category D] [Abelian D] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] (n : ℤ) :
    F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor D n ≅
      DerivedCategory.homologyFunctor C n ⋙ F :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ (F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor D n))
    (DerivedCategory.Q ⋙ (DerivedCategory.homologyFunctor C n ⋙ F)) _ _
    (Functor.isoWhiskerRight F.mapDerivedCategoryFactors (DerivedCategory.homologyFunctor D n) ≪≫
      Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
        (DerivedCategory.homologyFunctorFactors D n) ≪≫
      mapHomologicalComplexCompHomologyFunctorIso F n ≪≫
      Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors C n).symm F)

/-- A faithful additive functor reflects zero objects. -/
private theorem isZero_of_isZero_map {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] (F : C ⥤ D) [F.Additive] [F.Faithful] {A : C} (h : IsZero (F.obj A)) :
    IsZero A :=
  (IsZero.iff_id_eq_zero A).mpr <| F.map_injective <| by
    rw [F.map_id, F.map_zero]
    exact (IsZero.iff_id_eq_zero _).mp h

/-- A faithful exact additive functor reflects boundedness above: it commutes with cohomology and
reflects the vanishing of the cohomology objects. -/
private theorem isLE_of_isLE_mapDerivedCategory {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] {D : Type*} [Category D] [Abelian D] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.Faithful]
    (K : DerivedCategory C) (n : ℤ) (hK : (F.mapDerivedCategory.obj K).IsLE n) : K.IsLE n := by
  have := hK
  rw [DerivedCategory.isLE_iff]
  intro i hi
  refine isZero_of_isZero_map F ?_
  exact (DerivedCategory.isZero_of_isLE (F.mapDerivedCategory.obj K) n i hi).of_iso
    ((mapDerivedCategoryCompHomologyFunctorIso F i).app K).symm

/-! ### Relative pseudo-coherence at an affine-space chart -/

/-- Relative `m`-pseudo-coherence depends on the morphism only through its value, so it may be
transported along an equality of morphisms. This cannot be a `rw` lemma: the two morphisms carry
separate local finite-type instances, which the substitution has to eliminate. -/
public theorem Scheme.Hom.isPseudoCoherentFrom_congr_hom {X S : Scheme.{u}} {q q' : X ⟶ S}
    (h : q = q') [LocallyOfFiniteType q] [LocallyOfFiniteType q']
    (E : DerivedCategory X.Modules) (m : ℤ) :
    q.IsPseudoCoherentFrom E m ↔ q'.IsPseudoCoherentFrom E m := by
  subst h
  exact Iff.rfl

/-- The local condition of Stacks 09UI at a closed immersion, read as absolute
`m`-pseudo-coherence of the unbounded derived pushforward. -/
private theorem isPseudoCoherentFromAfterPushforward_iff_derivedPushforward {X Y : Scheme.{u}}
    (i : X ⟶ Y) [IsClosedImmersion i] (E : DerivedCategory X.Modules) (m : ℤ) :
    Scheme.Modules.IsPseudoCoherentFromAfterPushforward i E m ↔
      RingedSpace.IsPseudoCoherentFrom (X := Y.toRingedSpace)
        ((derivedPushforward i.toLRSHom.toShHom).obj E) m := by
  rw [Scheme.Modules.isPseudoCoherentFromAfterPushforward_iff i E m]
  exact ⟨fun h => h.of_iso
      ((Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategoryOfSchemes i).app E).symm,
    fun h => h.of_iso
      ((Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategoryOfSchemes i).app E)⟩

/-- **The chart bridge of Stacks 09UU.** For a closed immersion `e : U ⟶ 𝔸ⁿ_W` factoring
`q : U ⟶ W`, the local condition of Stacks 09UI at `e` is relative `m`-pseudo-coherence for `q`:
affine `n`-space is flat and locally of finite presentation over its base. -/
private theorem isPseudoCoherentFromAfterPushforward_iff_isPseudoCoherentFrom {U W : Scheme.{u}}
    (q : U ⟶ W) [LocallyOfFiniteType q] (n : ℕ) (e : U ⟶ 𝔸(ULift.{u} (Fin n); W))
    [IsClosedImmersion e] (he : e ≫ 𝔸(ULift.{u} (Fin n); W) ↘ W = q)
    (G : DerivedCategory U.Modules) (m : ℤ) :
    Scheme.Modules.IsPseudoCoherentFromAfterPushforward e G m ↔ q.IsPseudoCoherentFrom G m :=
  let : Flat (𝔸(ULift.{u} (Fin n); W) ↘ W) := flat_affineSpace (ULift.{u} (Fin n)) W
  (isPseudoCoherentFromAfterPushforward_iff_derivedPushforward e G m).trans
    ((Scheme.Hom.derivedPushforwardRelative_iff_pseudoCoherentFrom e
        (𝔸(ULift.{u} (Fin n); W) ↘ W) G m).symm.trans
      ((Scheme.Hom.isPseudoCoherentFrom_iff_derivedPushforwardRelative e
          (𝔸(ULift.{u} (Fin n); W) ↘ W) G m).symm.trans
        (Scheme.Hom.isPseudoCoherentFrom_congr_hom he G m)))

/-- The pair condition of Stacks 09UJ at a compatible pair of affine opens follows from relative
`m`-pseudo-coherence of the restriction for the restricted morphism: a closed immersion into an
affine space exists over the pair, and the chart bridge identifies the two conditions along it. -/
private theorem isPseudoCoherentFromOnAffinePair_of_isPseudoCoherentFrom_resLE {X S : Scheme.{u}}
    (q : X ⟶ S) [LocallyOfFiniteType q] (F : DerivedCategory X.Modules) (m : ℤ)
    (U : X.affineOpens) (V : S.affineOpens) (hUV : U.1 ≤ q ⁻¹ᵁ V.1)
    (h : (q.resLE V.1 U.1 hUV).IsPseudoCoherentFrom
      ((Scheme.Modules.restrictFunctor U.1.ι).mapDerivedCategory.obj F) m) :
    q.IsPseudoCoherentFromOnAffinePair F m U V hUV := by
  have : IsAffine (U.1 : Scheme.{u}) := U.2
  have : IsAffine (V.1 : Scheme.{u}) := V.2
  have := locallyOfFiniteType_resLE q V.1 U.1 hUV
  obtain ⟨n, e, hclosed, hbase⟩ := exists_isClosedImmersion_affineSpace_resLE q V U hUV
  have := hclosed
  exact ⟨n, e, hclosed, hbase,
    (isPseudoCoherentFromAfterPushforward_iff_isPseudoCoherentFrom _ n e hbase _ m).mpr h⟩

/-! ### Boundedness above of a relatively pseudo-coherent object -/

/-- **A relatively `m`-pseudo-coherent object on an affine scheme over an affine base is bounded
above.** A closed immersion of `Z` into an affine space over the base makes the object absolutely
`m`-pseudo-coherent after pushforward, and affine space over an affine scheme is quasi-compact, so
`AlgebraicGeometry.exists_isLE_of_isPseudoCoherentFrom` gives a bound there; the pushforward is
faithful and exact, so the bound comes back. -/
public theorem Scheme.Hom.IsPseudoCoherentFrom.exists_isLE {Z W : Scheme.{u}} [IsAffine Z]
    [IsAffine W] (q : Z ⟶ W) [LocallyOfFiniteType q] (G : DerivedCategory Z.Modules) (m : ℤ)
    (hG : q.IsPseudoCoherentFrom G m) : ∃ a : ℤ, G.IsLE a := by
  obtain ⟨n, e, hclosed, hbase⟩ := exists_isClosedImmersion_affineSpace q
  have := hclosed
  have habs := (isPseudoCoherentFromAfterPushforward_iff_derivedPushforward e G m).mp
    ((isPseudoCoherentFromAfterPushforward_iff_isPseudoCoherentFrom q n e hbase G m).mpr hG)
  obtain ⟨b, hb⟩ := AlgebraicGeometry.exists_isLE_of_isPseudoCoherentFrom _ m habs
  refine ⟨b, isLE_of_isLE_mapDerivedCategory (Scheme.Modules.pushforward e) G b ?_⟩
  exact isLE_of_iso
    ((Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategoryOfSchemes e).app G) b hb

/-! ### The global sections of a closed subscheme as a module -/

/-- **Cancelling a flat, finitely presented chart.** If `i ≫ p` is pseudo-coherent for `p` flat
and locally of finite presentation between affine schemes, then the map on global sections induced
by `i` is a pseudo-coherent ring map, by Stacks 0683. -/
private theorem pseudoCoherent_appTop_of_comp {U Z V : Scheme.{u}} [IsAffine U] [IsAffine Z]
    [IsAffine V] (i : U ⟶ Z) (p : Z ⟶ V) [Flat p] [LocallyOfFinitePresentation p]
    (h : PseudoCoherent (i ≫ p)) : (i.appTop).hom.PseudoCoherent := by
  algebraize [(p.appTop).hom, (i.appTop).hom, ((i ≫ p).appTop).hom]
  let : IsScalarTower Γ(V, ⊤) Γ(Z, ⊤) Γ(U, ⊤) := IsScalarTower.of_algebraMap_eq' rfl
  have hpZ : p.appLE (⊤ : V.Opens) (⊤ : Z.Opens) le_top = p.appTop :=
    Scheme.Hom.appLE_eq_app p
  have hpU : (i ≫ p).appLE (⊤ : V.Opens) (⊤ : U.Opens) le_top = (i ≫ p).appTop :=
    Scheme.Hom.appLE_eq_app (i ≫ p)
  have hVZ : (p.appTop).hom.PseudoCoherent := by
    rw [← hpZ]
    exact PseudoCoherent.pseudoCoherent_appLE p (isAffineOpen_top V) (isAffineOpen_top Z) le_top
  have hVU : ((i ≫ p).appTop).hom.PseudoCoherent := by
    rw [← hpU]
    exact h.pseudoCoherent_appLE (isAffineOpen_top V) (isAffineOpen_top U) le_top
  exact Algebra.PseudoCoherent.of_restrictScalars hVZ hVU

section

open _root_.PseudoCoherence

/-- **The global sections of a closed subscheme are a pseudo-coherent module.** For a closed
immersion `i : U ⟶ Z` of affine schemes whose map on global sections is a pseudo-coherent ring
map, `Γ(U, ⊤)` is an `m`-pseudo-coherent `Γ(Z, ⊤)`-module for every `m`.

Pseudo-coherence of the ring map is relative pseudo-coherence of `Γ(U, ⊤)` over `Γ(Z, ⊤)` as a
module over itself; Stacks 0673 restricts that along the finite surjection
`Γ(Z, ⊤) ⟶ Γ(U, ⊤)`, and Stacks 0DHQ at the identity of `Γ(Z, ⊤)` makes it absolute. -/
public theorem Scheme.Hom.isModulePseudoCoherentFrom_sections_of_isClosedImmersion
    {U Z : Scheme.{u}} [IsAffine U] [IsAffine Z] (i : U ⟶ Z) [IsClosedImmersion i]
    (hO : (i.appTop).hom.PseudoCoherent) (k : ℤ) :
    StacksDraft.PseudoCoherence.IsModulePseudoCoherentFrom (R := Γ(Z, ⊤))
      ((ModuleCat.restrictScalars (i.appTop).hom).obj (ModuleCat.of Γ(U, ⊤) Γ(U, ⊤))) k := by
  let : Algebra Γ(Z, ⊤) Γ(U, ⊤) := (i.appTop).hom.toAlgebra
  have hsurj : Function.Surjective ((i.appTop).hom) :=
    Scheme.Hom.app_surjective i ⊤ (isAffineOpen_top Z)
  let : Module.Finite Γ(Z, ⊤) Γ(U, ⊤) :=
    Module.Finite.of_surjective (Algebra.linearMap Γ(Z, ⊤) Γ(U, ⊤)) hsurj
  have hZZ : Algebra.PseudoCoherent Γ(Z, ⊤) Γ(Z, ⊤) :=
    (RingHom.isPerfectRingMap_of_flat_of_finitePresentation Γ(Z, ⊤) Γ(Z, ⊤)).1
  have hres := isRelativelyPseudoCoherentFrom_and_isRelativelyPseudoCoherent_iff_restrictScalars
    (R := Γ(Z, ⊤)) (A := Γ(Z, ⊤)) (B := Γ(U, ⊤))
    ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(U, ⊤)) 0).obj
      (ModuleCat.of Γ(U, ⊤) Γ(U, ⊤))) 0
  have habs := relativelyPseudoCoherent_iff_pseudoCoherent (R := Γ(Z, ⊤)) (A := Γ(Z, ⊤)) hZZ
    ((ModuleCat.restrictScalars.{u} (algebraMap Γ(Z, ⊤) Γ(U, ⊤))).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(U, ⊤)) 0).obj
        (ModuleCat.of Γ(U, ⊤) Γ(U, ⊤)))) 0
  dsimp only at hres habs
  have hsingle := ((ModuleCat.restrictScalars.{u}
    (algebraMap Γ(Z, ⊤) Γ(U, ⊤))).mapDerivedCategorySingleFunctor 0).app
      (ModuleCat.of Γ(U, ⊤) Γ(U, ⊤))
  exact (StacksDraft.PseudoCoherence.pseudoCoherent_iff_pseudoCoherentFrom_all_iff_finiteProjective
    _ 0).1.mp ((habs.2.mp (hres.2.mp
      (Algebra.pseudoCoherent_iff_isModuleRelativelyPseudoCoherent.mp hO))).ofIso
        hsingle) k

end

/-! ### The sheafification of the global sections -/

/-- Along an isomorphism of schemes, the pushforward of the structure sheaf is the structure
sheaf. -/
private def pushforwardUnitIsoOfIso {X Y : Scheme.{u}} (e : X ≅ Y) :
    (Scheme.Modules.pushforward e.hom).obj (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit Y.ringCatSheaf :=
  letI : (Scheme.Modules.restrictFunctor e.hom).IsEquivalence :=
    Functor.isEquivalence_of_iso (Scheme.Modules.restrictFunctorIsoPullback e.hom).symm
  (Functor.FullyFaithful.ofFullyFaithful
      (Scheme.Modules.restrictFunctor e.hom)).preimageIso
    ((Scheme.Modules.restrictFunctorAdjCounitIso e.hom).app
        (SheafOfModules.unit X.ringCatSheaf) ≪≫
      (Scheme.Modules.restrictUnitIso e.hom).symm)

/-- The global sections over `Spec A` of the pushforward of the structure sheaf of `Spec B` are
`B`, as an `A`-module through `φ : A ⟶ B`. -/
private def pushforwardSectionsIso {A B : CommRingCat.{u}} (φ : A ⟶ B) :
    (ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of B B) ≅
      (moduleSpecΓFunctor (R := A)).obj
        ((Scheme.Modules.pushforward (Spec.map φ)).obj
          (SheafOfModules.unit (Spec B).ringCatSheaf)) := by
  let ρ : A →+* Γ(Spec B, ⊤) :=
    (Spec.map φ).appTop.hom.comp (Scheme.ΓSpecIso A).inv.hom
  letI : Algebra A Γ(Spec B, ⊤) := ρ.toAlgebra
  letI : Algebra A B := φ.hom.toAlgebra
  change ModuleCat.of A B ≅ ModuleCat.of A Γ(Spec B, ⊤)
  have hnat : ∀ a : A, (Scheme.ΓSpecIso B).inv.hom (φ.hom a) = ρ a := by
    intro a
    have h := congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_inv_naturality φ)
    rw [CommRingCat.hom_comp, CommRingCat.hom_comp] at h
    exact congrArg (fun g : A →+* Γ(Spec B, ⊤) => g a) h
  let l : B ≃ₗ[A] Γ(Spec B, ⊤) :=
    { toFun := (Scheme.ΓSpecIso B).inv.hom
      invFun := (Scheme.ΓSpecIso B).hom.hom
      left_inv _ := by simp
      right_inv _ := by simp
      map_add' := map_add (Scheme.ΓSpecIso B).inv.hom
      map_smul' a x := by
        change (Scheme.ΓSpecIso B).inv.hom (φ.hom a * x) = ρ a * (Scheme.ΓSpecIso B).inv.hom x
        rw [map_mul, hnat] }
  exact l.toModuleIso

/-- For a ring map `φ : A ⟶ B`, the sheaf on `Spec A` associated with `B` viewed as an `A`-module
is the pushforward of the structure sheaf of `Spec B`. -/
private def tildePushforwardUnitIso {A B : CommRingCat.{u}} (φ : A ⟶ B) :
    (tilde.functor A).obj ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of B B)) ≅
      (Scheme.Modules.pushforward (Spec.map φ)).obj
        (SheafOfModules.unit (Spec B).ringCatSheaf) :=
  have hG : IsIso ((Scheme.Modules.pushforward (Spec.map φ)).obj
      (SheafOfModules.unit (Spec B).ringCatSheaf)).fromTildeΓ :=
    AlgebraicGeometry.isIso_fromTildeΓ_pushforward φ (SheafOfModules.unit (Spec B).ringCatSheaf)
  (tilde.functor A).mapIso (pushforwardSectionsIso φ) ≪≫
    @asIso _ _ _ _ _ hG

/-- Pushing `i_*𝒪_U` forward to `Spec Γ(Z, ⊤)` gives the sheaf associated with `Γ(U, ⊤)` as a
`Γ(Z, ⊤)`-module: the naturality of `AlgebraicGeometry.Scheme.isoSpec` and the functoriality of
pushforward. -/
private def pushforwardIsoSpecUnit {U Z : Scheme.{u}} [IsAffine U] [IsAffine Z] (i : U ⟶ Z) :
    (Scheme.Modules.pushforward Z.isoSpec.hom).obj
        ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit U.ringCatSheaf)) ≅
      (tilde.functor Γ(Z, ⊤)).obj
        ((ModuleCat.restrictScalars (i.appTop).hom).obj (ModuleCat.of Γ(U, ⊤) Γ(U, ⊤))) :=
  (Scheme.Modules.pushforwardComp i Z.isoSpec.hom).app _ ≪≫
    (Scheme.Modules.pushforwardCongr (Scheme.isoSpec_hom_naturality i).symm).app _ ≪≫
    (Scheme.Modules.pushforwardComp U.isoSpec.hom (Spec.map (i.appTop))).symm.app _ ≪≫
    (Scheme.Modules.pushforward (Spec.map (i.appTop))).mapIso
      (pushforwardUnitIsoOfIso U.isoSpec) ≪≫
    (tildePushforwardUnitIso (i.appTop)).symm

/-- **`i_*𝒪_U` is the sheafification of `Γ(U, ⊤)`.** The comparison functor of an affine scheme
takes `Γ(U, ⊤)`, viewed as a `Γ(Z, ⊤)`-module, to the pushforward of the structure sheaf of `U`
along a morphism `i : U ⟶ Z` of affine schemes. -/
private def tildeOfIsoPushforwardUnit {U Z : Scheme.{u}} [IsAffine U] [IsAffine Z] (i : U ⟶ Z) :
    (tildeOf Z).obj
        ((ModuleCat.restrictScalars (i.appTop).hom).obj (ModuleCat.of Γ(U, ⊤) Γ(U, ⊤))) ≅
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit U.ringCatSheaf) :=
  ((Scheme.Modules.restrictFunctorIsoPullback Z.isoSpec.hom).app _).symm ≪≫
    (Scheme.Modules.restrictFunctor Z.isoSpec.hom).mapIso (pushforwardIsoSpecUnit i).symm ≪≫
    (Scheme.Modules.restrictFunctorAdjCounitIso Z.isoSpec.hom).app _

/-- **The sheafification of the rank-one free module is the structure sheaf**, in the `ULift`
spelling that the finite free dévissage consumes. -/
private def tildeOfULiftUnitIso (Z : Scheme.{u}) [IsAffine Z] :
    (tildeOf Z).obj (ModuleCat.of Γ(Z, ⊤) (ULift.{u} Γ(Z, ⊤))) ≅
      SheafOfModules.unit Z.ringCatSheaf :=
  (tildeOf Z).mapIso
      (ULift.moduleEquiv : ULift.{u} Γ(Z, ⊤) ≃ₗ[Γ(Z, ⊤)] Γ(Z, ⊤)).toModuleIso ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback Z.isoSpec.hom).app _).symm ≪≫
    (Scheme.Modules.restrictFunctor Z.isoSpec.hom).mapIso tildeSelf ≪≫
    Scheme.Modules.restrictUnitIso Z.isoSpec.hom

/-- The degree-zero sheafification of the rank-one free module is `𝒪_Z`. -/
private def derivedTildeOfULiftUnitIso (Z : Scheme.{u}) [IsAffine Z] :
    (tildeOf Z).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(Z, ⊤)) 0).obj
          (ModuleCat.of Γ(Z, ⊤) (ULift.{u} Γ(Z, ⊤)))) ≅
      (DerivedCategory.singleFunctor Z.Modules 0).obj (SheafOfModules.unit Z.ringCatSheaf) :=
  ((tildeOf Z).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor Z.Modules 0).mapIso (tildeOfULiftUnitIso Z)

/-- **`Ri_*𝒪_U` is the derived sheafification of `Γ(U, ⊤)` in degree zero.** This is the input of
the dévissage: the module is pseudo-coherent, so it is quasi-isomorphic to a bounded-above complex
of finite free modules, whose sheafification has terms a finite sum of copies of `𝒪_Z`. -/
private def derivedPushforwardUnitIsoTildeOf {U Z : Scheme.{u}} [IsAffine U] [IsAffine Z]
    (i : U ⟶ Z) [IsClosedImmersion i] :
    (tildeOf Z).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(Z, ⊤)) 0).obj
          ((ModuleCat.restrictScalars (i.appTop).hom).obj
            (ModuleCat.of Γ(U, ⊤) Γ(U, ⊤)))) ≅
      (derivedPushforward i.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor U.Modules 0).obj (SheafOfModules.unit U.ringCatSheaf)) :=
  ((tildeOf Z).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor Z.Modules 0).mapIso (tildeOfIsoPushforwardUnit i) ≪≫
    (((Scheme.Modules.pushforward i).mapDerivedCategorySingleFunctor 0).app
      (SheafOfModules.unit U.ringCatSheaf)).symm ≪≫
    ((Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategoryOfSchemes i).app _).symm

/-! ### The dévissage of the affine core -/

/-- Tensoring on the left with a fixed derived object, as an endofunctor of `D(𝒪_Z)`. -/
private def derivedTensorRight (Z : Scheme.{u}) (G : DerivedCategory Z.Modules) :
    DerivedCategory Z.Modules ⥤ DerivedCategory Z.Modules :=
  (canonicalDerivedTensorProduct Z.sheaf).tensor.flip.obj G

/-- **The dévissage of the affine core.** For `G` bounded above and relatively
`m`-pseudo-coherent, and `M` a pseudo-coherent `Γ(Z, ⊤)`-module, the derived tensor product of
the degree-zero sheafification of `M` with `G` is relatively `m`-pseudo-coherent.

The dévissage runs over a bounded-above finite free resolution of `M`; the derived tensor product
adds cohomological bounds with no hypothesis on the terms, so the auxiliary property carried on
them is trivial, and on the rank-one free module the claim is `𝒪_Z ⊗^𝐋 G = G`. -/
@[sga "6 III 1.11" "Part (a), special case"]
private theorem isPseudoCoherentFrom_derivedTensor_tildeOf {Z W : Scheme.{u}} [IsAffine Z]
    (q : Z ⟶ W) [LocallyOfFiniteType q] (G : DerivedCategory Z.Modules) (a : ℤ) (hGa : G.IsLE a)
    (m : ℤ) (M : ModuleCat.{u} Γ(Z, ⊤))
    (hM : ∀ k : ℤ, StacksDraft.PseudoCoherence.IsModulePseudoCoherentFrom (R := Γ(Z, ⊤)) M k)
    (hG : q.IsPseudoCoherentFrom G m) :
    q.IsPseudoCoherentFrom
      ((derivedTensorRight Z G).obj ((tildeOf Z).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(Z, ⊤)) 0).obj M))) m := by
  let : (derivedTensorRight Z G).CommShift ℤ :=
    (canonicalDerivedTensorProduct Z.sheaf).commShift_left G
  let : (derivedTensorRight Z G).IsTriangulated :=
    (canonicalDerivedTensorProduct Z.sheaf).exact_left G
  let : (derivedTensorRight Z G).Additive :=
    Functor.additive_of_preserves_binary_products (derivedTensorRight Z G)
  refine Scheme.Hom.isPseudoCoherentFrom_map_of_modulePseudoCoherent q
    ((tildeOf Z).mapDerivedCategory ⋙ derivedTensorRight Z G) a m (fun _ => True)
    (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ _ => trivial) ?_ ?_ M hM
  · intro L n _ hLn
    have := hLn
    have h1 : ((tildeOf Z).mapDerivedCategory.obj (DerivedCategory.Q.obj L)).IsLE n :=
      DerivedCategory.isLE_mapDerivedCategory (tildeOf Z) _ n inferInstance
    exact Scheme.Modules.isLE_derivedTensorProduct Z _ G n a h1 hGa
  · refine Scheme.Hom.IsPseudoCoherentFrom.of_iso q hG ?_
    exact ((derivedTensorRight Z G).mapIso (derivedTildeOfULiftUnitIso Z) ≪≫
      Scheme.Modules.derivedTensorUnitLeftIso Z G).symm

/-- **The affine core of Stacks 09US.** Let `i : U ⟶ Z` be a closed immersion of affine schemes
whose map on global sections is pseudo-coherent, let `q : Z ⟶ W` be locally of finite type with
`W` affine, and let `G` be relatively `m`-pseudo-coherent over `W`. Then so is `Ri_*Li^*G`.

The projection formula identifies `Ri_*Li^*G` with `Ri_*𝒪_U ⊗^𝐋 G`, the sheaf `Ri_*𝒪_U` is the
degree-zero sheafification of the pseudo-coherent `Γ(Z, ⊤)`-module `Γ(U, ⊤)`, and the dévissage
over a finite free resolution of that module finishes. -/
private theorem isPseudoCoherentFrom_derivedPushforward_derivedPullback {U Z W : Scheme.{u}}
    [IsAffine U] [IsAffine Z] [IsAffine W] (i : U ⟶ Z) [IsClosedImmersion i] (q : Z ⟶ W)
    [LocallyOfFiniteType q] (hO : (i.appTop).hom.PseudoCoherent)
    (G : DerivedCategory Z.Modules) (m : ℤ) (hG : q.IsPseudoCoherentFrom G m) :
    q.IsPseudoCoherentFrom ((derivedPushforward i.toLRSHom.toShHom).obj
      ((derivedPullback i.toLRSHom.toShHom).obj G)) m := by
  obtain ⟨a, hGa⟩ := Scheme.Hom.IsPseudoCoherentFrom.exists_isLE q G m hG
  obtain ⟨e⟩ := Stacks.ClosedImmersion.nonempty_derivedPushforwardDerivedPullbackIsoTensor i G
  refine Scheme.Hom.IsPseudoCoherentFrom.of_iso q ?_ e.symm
  refine Scheme.Hom.IsPseudoCoherentFrom.of_iso q
    (isPseudoCoherentFrom_derivedTensor_tildeOf q G a hGa m _
      (Scheme.Hom.isModulePseudoCoherentFrom_sections_of_isClosedImmersion i hO) hG) ?_
  exact (derivedTensorRight Z G).mapIso (derivedPushforwardUnitIsoTildeOf i)

/-! ### Flat base change along a closed immersion -/

section FlatBaseChange

open RingedSpaceModuleAdjunction
open Stacks.Cohomology.PerfectComplexTriangles
  (mapDerivedCategoryCompIso mapDerivedCategoryIsoOfNatIso)

/-- **The annihilation hypothesis of the flat case of Stacks 0E23.** For a cartesian square

```
Z' --i'--> X'
|g          |f
Z --i-----> X
```

with `i` a closed immersion, the kernel of the comorphism of `i'` annihilates `Lf^*(i_*M)`
section by section, for every `𝒪_Z`-module `M`.

Geometrically this is the statement that the closed subscheme `Z'` of `X'` is cut out by the
pullback of the ideal of `Z` in `X`: a section of `ker(i'^♯)` is locally a combination of
`f^♯` of sections of `ker(i^♯)`, and those annihilate `i_*M` by Stacks 08KS. Under it the two
constructions below give Stacks 0E23 for a flat `f`. -/
public abbrev KernelAnnihilatesPullbackPushforward {Z' X' Z X : Scheme.{u}} (i' : Z' ⟶ X')
    (f : X' ⟶ X) (i : Z ⟶ X) : Prop :=
  ∀ (M : Z.Modules) (U : X'.Opens) (a : Γ(X', U)), (i'.app U).hom a = 0 →
    ∀ n : Γ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pushforward i).obj M), U), a • n = 0

/-- Degreewise pushforward along a closed immersion of schemes is right exact: Stacks 08KS,
crossed to the scheme spelling of the two categories in term position. -/
public theorem preservesFiniteColimits_pushforward_of_isClosedImmersion {X Y : Scheme.{u}}
    (i : X ⟶ Y) [IsClosedImmersion i] :
    PreservesFiniteColimits (Scheme.Modules.pushforward i) :=
  have h : PreservesFiniteColimits (modulePushforward i.toLRSHom.toShHom) :=
    Stacks.ClosedImmersion.preservesFiniteColimits_modulePushforward _
      (Stacks.ClosedImmersion.isClosedEmbedding_base_toShHom i)
  h

/-- Degreewise pushforward of sheaves of modules is left exact for every morphism of schemes: it
is the right adjoint of the pullback. -/
public theorem preservesFiniteLimits_pushforward {X Y : Scheme.{u}} (i : X ⟶ Y) :
    PreservesFiniteLimits (Scheme.Modules.pushforward i) :=
  have : PreservesLimitsOfSize.{0, 0} (Scheme.Modules.pushforward i) :=
    (Scheme.Modules.pullbackPushforwardAdjunction i).rightAdjoint_preservesLimits
  inferInstance

/-- Degreewise pullback along a flat morphism of schemes is left exact: flatness of a morphism of
schemes is flatness of its germ maps, which is the hypothesis of Stacks 02N4. -/
public alias preservesFiniteLimits_pullback_of_flat :=
  preservesFiniteLimits_modulesPullback_of_flat

variable {Z' X' Z X : Scheme.{u}} {i' : Z' ⟶ X'} {g : Z' ⟶ Z} {f : X' ⟶ X} {i : Z ⟶ X}

/-- **The two iterated degreewise pullbacks around a commutative square agree.** Both are
pullback along the common composite, by the composition law of Stacks 0096. -/
public def pullbackCompSquareIso (hw : i' ≫ f = g ≫ i) :
    Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback i' ≅
      Scheme.Modules.pullback i ⋙ Scheme.Modules.pullback g :=
  (modulePullbackComp i'.toLRSHom.toShHom f.toLRSHom.toShHom).symm ≪≫
    modulePullbackCongr (show i'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
      g.toLRSHom.toShHom ≫ i.toLRSHom.toShHom by
        simpa only [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom] using
          congrArg (fun h : Z' ⟶ X => h.toLRSHom.toShHom) hw) ≪≫
    modulePullbackComp g.toLRSHom.toShHom i.toLRSHom.toShHom

/-- **Base change of a closed immersion, on sheaves of modules.** For a commutative square with
`i` and `i'` closed immersions in which the kernel of the comorphism of `i'` annihilates
`f^*(i_*M)` for every `M`, the two composites `f^* ∘ i_*` and `i'_* ∘ g^*` of degreewise
functors are isomorphic.

The chain is: the unit `N ⟶ i'_*i'^*N` of Stacks 08KS is invertible at `N = f^*(i_*M)` exactly
because of the annihilation hypothesis
(`Stacks.ClosedImmersion.isIso_unit_app_of_smul_eq_zero`); the iterated pullback
`i'^* ∘ f^*` is `g^* ∘ i^*` by `pullbackCompSquareIso`; and `i^* ∘ i_*` is the identity because
`i_*` is fully faithful, again Stacks 08KS, so the counit of `i^* ⊣ i_*` is invertible. -/
public def baseChangeIsoOfKernelAnnihilates (hw : i' ≫ f = g ≫ i) [IsClosedImmersion i]
    [IsClosedImmersion i'] (hann : KernelAnnihilatesPullbackPushforward i' f i) :
    Scheme.Modules.pushforward i ⋙ Scheme.Modules.pullback f ≅
      Scheme.Modules.pullback g ⋙ Scheme.Modules.pushforward i' :=
  have := Stacks.ClosedImmersion.full_pushforward i
  have := Stacks.ClosedImmersion.faithful_pushforward i
  have hcounit : IsIso (Scheme.Modules.pullbackPushforwardAdjunction i).counit := inferInstance
  let F := Scheme.Modules.pushforward i ⋙ Scheme.Modules.pullback f
  let e1 : F ≅ F ⋙ (Scheme.Modules.pullback i' ⋙ Scheme.Modules.pushforward i') :=
    NatIso.ofComponents
      (fun M => @asIso _ _ _ _ _
        (Stacks.ClosedImmersion.isIso_unit_app_of_smul_eq_zero i' (F.obj M) (hann M)))
      (fun φ => (Scheme.Modules.pullbackPushforwardAdjunction i').unit.naturality (F.map φ))
  let e2 : F ⋙ Scheme.Modules.pullback i' ≅ Scheme.Modules.pullback g :=
    Functor.isoWhiskerLeft (Scheme.Modules.pushforward i) (pullbackCompSquareIso hw) ≪≫
      Functor.isoWhiskerRight (@asIso _ _ _ _ _ hcounit) (Scheme.Modules.pullback g) ≪≫
      Functor.leftUnitor _
  e1 ≪≫ Functor.isoWhiskerRight e2 (Scheme.Modules.pushforward i')

/-- **The derived form of a flat base change along a closed immersion.** If the two horizontal
morphisms of the square are flat and the two vertical ones are closed immersions, then every
isomorphism `i_* ⋙ f^* ≅ g^* ⋙ i'_*` of degreewise functors induces one
`Ri_* ⋙ Lf^* ≅ Lg^* ⋙ Ri'_*` of the derived functors.

All four functors are derived functors of exact functors: pushforward along a closed immersion
is exact by Stacks 08KS and pullback along a flat morphism by Stacks 02N4, so
`Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategoryOfSchemes` and
`AlgebraicGeometry.SpecField.derivedPullbackMapDerivedIso` replace each of them by
`Functor.mapDerivedCategory` of the underived one, and `mapDerivedCategory` is a functor of the
exact functor. No base change map is involved and no Tor independence is needed: flatness of
`f` makes the Tor independence of Stacks 0E23 automatic, and is what collapses the derived
statement onto the underived one. -/
public def derivedBaseChangeIsoOfIso [IsClosedImmersion i] [IsClosedImmersion i'] [Flat f]
    [Flat g] (e : Scheme.Modules.pushforward i ⋙ Scheme.Modules.pullback f ≅
      Scheme.Modules.pullback g ⋙ Scheme.Modules.pushforward i') :
    derivedPushforward i.toLRSHom.toShHom ⋙ derivedPullback f.toLRSHom.toShHom ≅
      derivedPullback g.toLRSHom.toShHom ⋙ derivedPushforward i'.toLRSHom.toShHom := by
  letI : PreservesFiniteColimits (modulePushforward i.toLRSHom.toShHom) :=
    preservesFiniteColimits_pushforward_of_isClosedImmersion i
  letI : PreservesFiniteColimits (modulePushforward i'.toLRSHom.toShHom) :=
    preservesFiniteColimits_pushforward_of_isClosedImmersion i'
  letI : PreservesFiniteLimits (modulePushforward i.toLRSHom.toShHom) :=
    preservesFiniteLimits_pushforward i
  letI : PreservesFiniteLimits (modulePushforward i'.toLRSHom.toShHom) :=
    preservesFiniteLimits_pushforward i'
  letI : PreservesFiniteLimits (modulePullback f.toLRSHom.toShHom) :=
    preservesFiniteLimits_pullback_of_flat f
  letI : PreservesFiniteLimits (modulePullback g.toLRSHom.toShHom) :=
    preservesFiniteLimits_pullback_of_flat g
  letI : PreservesFiniteColimits (modulePullback f.toLRSHom.toShHom) :=
    preservesFiniteColimits_modulePullback _
  letI : PreservesFiniteColimits (modulePullback g.toLRSHom.toShHom) :=
    preservesFiniteColimits_modulePullback _
  have s1 : derivedPushforward i.toLRSHom.toShHom ≅
      (modulePushforward i.toLRSHom.toShHom).mapDerivedCategory :=
    Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategoryOfSchemes i
  have s1' : derivedPushforward i'.toLRSHom.toShHom ≅
      (modulePushforward i'.toLRSHom.toShHom).mapDerivedCategory :=
    Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategoryOfSchemes i'
  have s2 : derivedPullback f.toLRSHom.toShHom ≅
      (modulePullback f.toLRSHom.toShHom).mapDerivedCategory :=
    AlgebraicGeometry.SpecField.derivedPullbackMapDerivedIso f.toLRSHom.toShHom
  have s2' : derivedPullback g.toLRSHom.toShHom ≅
      (modulePullback g.toLRSHom.toShHom).mapDerivedCategory :=
    AlgebraicGeometry.SpecField.derivedPullbackMapDerivedIso g.toLRSHom.toShHom
  have t1 : (modulePushforward i.toLRSHom.toShHom).mapDerivedCategory ⋙
      (modulePullback f.toLRSHom.toShHom).mapDerivedCategory ≅
      (modulePushforward i.toLRSHom.toShHom ⋙
        modulePullback f.toLRSHom.toShHom).mapDerivedCategory :=
    (mapDerivedCategoryCompIso (modulePushforward i.toLRSHom.toShHom)
      (modulePullback f.toLRSHom.toShHom)).symm
  have t2 : (modulePushforward i.toLRSHom.toShHom ⋙
        modulePullback f.toLRSHom.toShHom).mapDerivedCategory ≅
      (modulePullback g.toLRSHom.toShHom ⋙
        modulePushforward i'.toLRSHom.toShHom).mapDerivedCategory :=
    mapDerivedCategoryIsoOfNatIso _ _ e
  have t3 : (modulePullback g.toLRSHom.toShHom ⋙
        modulePushforward i'.toLRSHom.toShHom).mapDerivedCategory ≅
      (modulePullback g.toLRSHom.toShHom).mapDerivedCategory ⋙
        (modulePushforward i'.toLRSHom.toShHom).mapDerivedCategory :=
    mapDerivedCategoryCompIso (modulePullback g.toLRSHom.toShHom)
      (modulePushforward i'.toLRSHom.toShHom)
  exact Functor.isoWhiskerRight s1 _ ≪≫ Functor.isoWhiskerLeft _ s2 ≪≫ t1 ≪≫ t2 ≪≫ t3 ≪≫
    Functor.isoWhiskerRight s2'.symm _ ≪≫ Functor.isoWhiskerLeft _ s1'.symm

/-- **The kernel of a germ map of a closed immersion annihilates the stalk of a pushforward.**
For a closed immersion `i : Z ⟶ X`, a point `z` of `Z` and an `𝒪_Z`-module `M`, an element of
`𝒪_{X, i z}` killed by the germ map `𝒪_{X, i z} ⟶ 𝒪_{Z, z}` annihilates the stalk of `i_* M` at
`i z`.

The image point is a free variable with an equation to it, compared by
`TopCat.Presheaf.stalkCongr`, so that a consumer reaching that point by another route — through
the commutativity of a cartesian square, say — can use the statement without transporting.

The kernel of the germ map is the ideal generated by germs of sections of the kernel of `i^♯`
over an affine open (`Stacks.Flatness.ker_stalkMap_eq_map_germ`), and those annihilate `i_* M`
section by section because `i_* M` is a direct image (Stacks 08KS,
`Stacks.ClosedImmersion.pushforward_essImage_iff`). -/
public theorem smul_stalk_pushforward_eq_zero {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (M : Z.Modules) (z : Z) (y : X) (hy : i.base z = y)
    (b : X.presheaf.stalk y)
    (hb : (i.stalkMap z).hom
      ((X.presheaf.stalkCongr (Inseparable.of_eq hy)).inv.hom b) = 0)
    (p : (Stacks.ModuleSkyscraper.modulesStalkFunctor X y).obj
      ((Scheme.Modules.pushforward i).obj M)) :
    b • p = 0 := by
  subst hy
  simp only [TopCat.Presheaf.stalkCongr, TopCat.Presheaf.stalkSpecializes_refl,
    CommRingCat.id_apply] at hb
  obtain ⟨U, hUaff, hzU, -⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (Opens.mem_top (i.base z))
  have hUa : IsAffineOpen U := hUaff
  have hVa : IsAffineOpen (i ⁻¹ᵁ U) := hUa.preimage i
  have hzV : z ∈ i ⁻¹ᵁ U := hzU
  have hsurj : Function.Surjective (i.appLE U (i ⁻¹ᵁ U) le_rfl).hom := by
    rw [Scheme.Hom.appLE_eq_app]
    exact i.app_surjective U hUa
  have hker := Stacks.Flatness.ker_stalkMap_eq_map_germ i hUa hVa le_rfl hzV hzU hsurj
  have hbker : b ∈ RingHom.ker (i.stalkMap z).hom := hb
  rw [hker] at hbker
  have hT : ∀ (V : X.Opens) (c : Γ(X, V)), (i.app V).hom c = 0 →
      ∀ n : Γ((Scheme.Modules.pushforward i).obj M, V), c • n = 0 :=
    (Stacks.ClosedImmersion.pushforward_essImage_iff i _).mp
      ((Scheme.Modules.pushforward i).obj_mem_essImage M)
  refine Module.mem_annihilator.mp
    ((Submodule.span_le (p := Module.annihilator _ _)).mpr ?_ hbker) p
  rintro - ⟨b₀, hb₀, rfl⟩
  refine Module.mem_annihilator.mpr fun p => ?_
  obtain ⟨W, hzW, m, hm⟩ := TopCat.Presheaf.exists_germ_eq
    ((Scheme.Modules.pushforward i).obj M).val.presheaf p
  have hzV₁ : i.base z ∈ U ⊓ W := ⟨hzU, hzW⟩
  set b₁ := (X.presheaf.map (homOfLE (inf_le_left : U ⊓ W ≤ U)).op).hom b₀ with hb₁
  set m₁ := (((Scheme.Modules.pushforward i).obj M).val.presheaf.map
    (homOfLE (inf_le_right : U ⊓ W ≤ W)).op).hom m with hm₁
  have hgb : (X.presheaf.germ (U ⊓ W) (i.base z) hzV₁).hom b₁ =
      (X.presheaf.germ U (i.base z) hzU).hom b₀ :=
    TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE inf_le_left) (i.base z) hzV₁ b₀
  have hgm : (TopCat.Presheaf.germ ((Scheme.Modules.pushforward i).obj M).val.presheaf
      (U ⊓ W) (i.base z) hzV₁).hom m₁ = p := by
    rw [hm₁, TopCat.Presheaf.germ_res_apply]
    exact hm
  have hzero : (i.app (U ⊓ W)).hom b₁ = 0 := by
    rw [hb₁, Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply,
      Scheme.Hom.map_appLE i le_rfl (homOfLE (inf_le_left : U ⊓ W ≤ U)).op,
      ← Scheme.Hom.appLE_map i le_rfl
        (homOfLE (Scheme.Hom.preimage_mono i (inf_le_left : U ⊓ W ≤ U))).op,
      CommRingCat.comp_apply, RingHom.mem_ker.mp hb₀, map_zero]
  have hsm : b₁ • (show Γ((Scheme.Modules.pushforward i).obj M, U ⊓ W) from m₁) = 0 :=
    hT (U ⊓ W) b₁ hzero _
  have hz1 : (X.presheaf.germ (U ⊓ W) (i.base z) hzV₁).hom b₁ •
      (TopCat.Presheaf.germ ((Scheme.Modules.pushforward i).obj M).val.presheaf
        (U ⊓ W) (i.base z) hzV₁).hom m₁ = 0 :=
    (Stacks.ModuleSkyscraper.germ_smul' (R := X.presheaf)
        ((Scheme.Modules.pushforward i).obj M).val (i.base z) (U ⊓ W) hzV₁ b₁ m₁).symm.trans
      ((congrArg (TopCat.Presheaf.germ ((Scheme.Modules.pushforward i).obj M).val.presheaf
          (U ⊓ W) (i.base z) hzV₁).hom hsm).trans (map_zero _))
  rw [← hgb, ← hgm]
  exact hz1

/-- Alias of `Stacks.Cohomology.ClosedImmersionBaseChange.range_eq_preimage_range_of_isPullback`. -/
public alias range_eq_preimage_range_of_isPullback :=
  Stacks.Cohomology.ClosedImmersionBaseChange.range_eq_preimage_range_of_isPullback

/-- `smul_zero` at the carrier of an object of `ModuleCat`, where the module instance is found;
after `TensorProduct.induction_on` the goal is stated at the unfolded carrier and instance search
no longer finds it. -/
public theorem smul_zero_moduleCat {S : Type u} [Ring S] (A : ModuleCat.{u} S) (t : S) :
    t • (0 : A) = 0 := smul_zero t

/-- `smul_add` at the carrier of an object of `ModuleCat`; see
`AlgebraicGeometry.smul_zero_moduleCat`. -/
public theorem smul_add_moduleCat {S : Type u} [Ring S] (A : ModuleCat.{u} S) (t : S)
    (u v : A) : t • (u + v) = t • u + t • v := smul_add t u v

/-- An element of a zero object of `AddCommGrpCat` is zero: the identity of a zero object is the
zero morphism, and both are read on the element. -/
public theorem eq_zero_of_isZero_addCommGrp {A : AddCommGrpCat.{u}} (hA : IsZero A) (q : A) :
    q = 0 := by
  have h0 : (𝟙 A) = 0 := (IsZero.iff_id_eq_zero A).mp hA
  have h1 := congrArg (fun φ : A ⟶ A => (ConcreteCategory.hom φ) q) h0
  simpa using h1

/-- An element of `S` annihilates `S ⊗_R P` once it annihilates every decomposable tensor. -/
private theorem smul_extendScalars_eq_zero_of_smul_tmul_eq_zero {R S : Type u} [CommRing R]
    [CommRing S] (φ : R →+* S) (P : ModuleCat.{u} R) (t : S)
    (h : ∀ (s : (ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)) (p : P),
      t • (show (ModuleCat.extendScalars φ).obj P from s ⊗ₜ[R] p) = 0)
    (z : (ModuleCat.extendScalars φ).obj P) : t • z = 0 := by
  refine TensorProduct.induction_on z (smul_zero_moduleCat ((ModuleCat.extendScalars φ).obj P) t)
    h fun u v hu hv => ?_
  exact (smul_add_moduleCat ((ModuleCat.extendScalars φ).obj P) t u v).trans
    (by rw [hu, hv]; exact add_zero 0)

/-- **An element of the base ring that annihilates a module annihilates its base change.**
For `φ : R ⟶ S` and `c : R` killing every element of `P`, the image `φ c` kills every element of
`S ⊗_R P`: on a decomposable element `φ c • (s ⊗ₜ p) = s ⊗ₜ (c • p) = 0`, the two steps being
`R`-linearity of `TensorProduct.mk` in its two arguments. -/
public theorem smul_extendScalars_eq_zero_of_smul_eq_zero {R S : Type u} [CommRing R]
    [CommRing S] (φ : R →+* S) (P : ModuleCat.{u} R) (c : R) (hc : ∀ p : P, c • p = 0)
    (z : (ModuleCat.extendScalars φ).obj P) : φ c • z = 0 := by
  refine smul_extendScalars_eq_zero_of_smul_tmul_eq_zero φ P _ (fun s p => ?_) z
  refine (ModuleCat.ExtendScalars.smul_tmul φ (φ c) s p).trans ?_
  have h1 : ((TensorProduct.mk R ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)) P)
      (c • s)) p = c • (((TensorProduct.mk R
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)) P) s) p) := by
    rw [map_smul, LinearMap.smul_apply]
  have h2 : ((TensorProduct.mk R ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)) P) s)
      (c • p) = c • (((TensorProduct.mk R
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)) P) s) p) := map_smul _ _ _
  exact h1.trans (h2.symm.trans (by rw [hc p]; exact map_zero _))

/-- **The base change of a zero module is annihilated by everything.** -/
public theorem smul_extendScalars_eq_zero_of_forall_eq_zero {R S : Type u} [CommRing R]
    [CommRing S] (φ : R →+* S) (P : ModuleCat.{u} R) (hP : ∀ p : P, p = 0) (t : S)
    (z : (ModuleCat.extendScalars φ).obj P) : t • z = 0 := by
  refine smul_extendScalars_eq_zero_of_smul_tmul_eq_zero φ P t (fun s p => ?_) z
  rw [hP p, TensorProduct.tmul_zero]
  exact smul_zero_moduleCat ((ModuleCat.extendScalars φ).obj P) t

/-- **The germ-level core of the annihilation.** At a point `x'` of `X'`, an element `t` of
`𝒪_{X',x'}` killed by the germ map of `i'` at every point of `Z'` over `x'` annihilates
`𝒪_{X',x'} ⊗_{𝒪_{X,f x'}} (i_*M)_{f x'}`, the stalk of `f^*(i_*M)` at `x'`.

Off the image of `i'` the hypothesis is vacuous and the second tensor factor is zero. On the
image the hypothesis says `t` lies in `ker(𝒪_{X',i'w} ⟶ 𝒪_{Z',w})`, which
`Stacks.Flatness.ker_stalkMap_of_isPullback` identifies with the ideal generated by the image of
`ker(𝒪_{X,i(gw)} ⟶ 𝒪_{Z,gw})`; a generator acts through
`AlgebraicGeometry.smul_extendScalars_eq_zero_of_smul_eq_zero`, whose hypothesis is
`AlgebraicGeometry.smul_stalk_pushforward_eq_zero`. -/
public theorem smul_extendScalars_stalk_pushforward_eq_zero (sq : IsPullback i' g f i)
    [IsClosedImmersion i] (M : Z.Modules) (x' : X') (t : X'.presheaf.stalk x')
    (ht : ∀ (w : Z') (h : i'.base w = x'),
      (i'.stalkMap w).hom ((X'.presheaf.stalkCongr (Inseparable.of_eq h)).inv.hom t) = 0)
    (z : (ModuleCat.extendScalars (f.stalkMap x').hom).obj
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor X (f.base x')).obj
        ((Scheme.Modules.pushforward i).obj M))) :
    t • z = 0 := by
  by_cases hmem : x' ∈ Set.range (⇑i')
  · obtain ⟨w, hw⟩ := hmem
    subst hw
    have hpt : i.base (g w) = f.base (i'.base w) :=
      (congrArg (fun k : Z' ⟶ X => k.base w) sq.w).symm
    have htw : t ∈ RingHom.ker (i'.stalkMap w).hom := RingHom.mem_ker.mpr (by
      have h := ht w rfl
      simpa only [TopCat.Presheaf.stalkCongr, TopCat.Presheaf.stalkSpecializes_refl,
        Iso.refl_inv, CommRingCat.id_apply] using h)
    rw [Stacks.Flatness.ker_stalkMap_of_isPullback sq w hpt] at htw
    refine Module.mem_annihilator.mp
      ((Submodule.span_le (p := Module.annihilator _ _)).mpr ?_ htw) z
    rintro - ⟨c₀, hc₀, rfl⟩
    refine Module.mem_annihilator.mpr fun z' => ?_
    have hcp : ∀ p : (Stacks.ModuleSkyscraper.modulesStalkFunctor X
        (f.base (i'.base w))).obj ((Scheme.Modules.pushforward i).obj M),
        ((X.presheaf.stalkCongr (Inseparable.of_eq hpt)).hom.hom c₀) • p = 0 := by
      intro p
      refine smul_stalk_pushforward_eq_zero i M (g w) (f.base (i'.base w)) hpt _ ?_ p
      rw [Iso.hom_inv_id_apply]
      exact hc₀
    exact smul_extendScalars_eq_zero_of_smul_eq_zero (f.stalkMap (i'.base w)).hom _
      ((X.presheaf.stalkCongr (Inseparable.of_eq hpt)).hom.hom c₀) hcp z'
  · have hfx : f.base x' ∉ Set.range (⇑i) := by
      rw [← Set.mem_preimage, ← range_eq_preimage_range_of_isPullback sq]
      exact hmem
    have hzero : IsZero ((AlgebraicGeometry.SheafOfModules.stalkFunctor
        (structureSheafRing X.toRingedSpace) (f.base x')).obj
        ((RingedSpaceModuleAdjunction.modulePushforward i.toLRSHom.toShHom).obj M)) :=
      Stacks.ClosedImmersion.isZero_stalk_modulePushforward_of_notMemRange
        i.toLRSHom.toShHom (Stacks.ClosedImmersion.isClosedEmbedding_base_toShHom i) M
        (f.base x') hfx
    have hzeroAb : IsZero (AddCommGrpCat.of (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        ((Scheme.Modules.pushforward i).obj M).val.presheaf (f.base x'))) :=
      (AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj_iff _ _ _).mp hzero
    have hp : ∀ q : (Stacks.ModuleSkyscraper.modulesStalkFunctor X (f.base x')).obj
        ((Scheme.Modules.pushforward i).obj M), q = 0 := fun q =>
      eq_zero_of_isZero_addCommGrp hzeroAb q
    exact smul_extendScalars_eq_zero_of_forall_eq_zero (f.stalkMap x').hom _ hp t z

/-- **The kernel ideal of a base-changed closed immersion annihilates the pullback of a
pushforward.** This is the input of the flat case of Stacks 0E23 that
`AlgebraicGeometry.nonempty_derivedPullbackPushforwardIso` asks for; geometrically it says the
base-changed closed subscheme is cut out by the pulled-back ideal.

A section is zero iff all its germs are, and the germ of `a • n` is the germ of `a` acting on the
germ of `n` (`Stacks.ModuleSkyscraper.germ_smul'`), so it is enough to annihilate the stalk of
`f^*(i_*M)` at each point of the open; `Stacks.ModuleSkyscraper.pullbackStalkIso` presents that
stalk as `𝒪_{X',x'} ⊗_{𝒪_{X,f x'}} (i_*M)_{f x'}` and
`AlgebraicGeometry.smul_extendScalars_stalk_pushforward_eq_zero` annihilates it. -/
public theorem kernelAnnihilatesPullbackPushforward_of_isPullback (sq : IsPullback i' g f i)
    [IsClosedImmersion i] : KernelAnnihilatesPullbackPushforward i' f i := by
  intro M U a ha n
  refine TopCat.Presheaf.section_ext
    ((SheafOfModules.toSheaf X'.ringCatSheaf).obj
      ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pushforward i).obj M))) U _ _ ?_
  intro x' hx'
  have ht : ∀ (w : Z') (h : i'.base w = x'),
      (i'.stalkMap w).hom ((X'.presheaf.stalkCongr (Inseparable.of_eq h)).inv.hom
        ((X'.presheaf.germ U x' hx').hom a)) = 0 := by
    intro w h
    subst h
    simp only [TopCat.Presheaf.stalkCongr, TopCat.Presheaf.stalkSpecializes_refl,
      CommRingCat.id_apply]
    have h2 := congrArg (fun φ : X'.presheaf.obj (Opposite.op U) ⟶ Z'.presheaf.stalk w =>
      (CommRingCat.Hom.hom φ) a) (i'.germ_stalkMap U w hx')
    simp only [CommRingCat.comp_apply] at h2
    exact h2.trans (by rw [ha]; exact map_zero _)
  have key : ∀ y : (Stacks.ModuleSkyscraper.modulesStalkFunctor X' x').obj
      ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pushforward i).obj M)),
      (X'.presheaf.germ U x' hx').hom a • y = 0 := by
    intro y
    set e := (Stacks.ModuleSkyscraper.pullbackStalkIso f x').app
      ((Scheme.Modules.pushforward i).obj M) with he
    obtain ⟨z, rfl⟩ : ∃ z, (ConcreteCategory.hom e.hom) z = y :=
      ⟨(ConcreteCategory.hom e.inv) y, CategoryTheory.Iso.inv_hom_id_apply e y⟩
    have hcore := smul_extendScalars_stalk_pushforward_eq_zero sq M x'
      ((X'.presheaf.germ U x' hx').hom a) ht z
    exact (map_smul (ConcreteCategory.hom e.hom)
        ((X'.presheaf.germ U x' hx').hom a) z).symm.trans
      ((congrArg (fun q => (ConcreteCategory.hom e.hom) q) hcore).trans (map_zero _))
  refine Eq.trans ?_ (map_zero _).symm
  exact (Stacks.ModuleSkyscraper.germ_smul' (R := X'.presheaf)
    ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pushforward i).obj M)).val x' U hx'
    a n).trans (key _)

/-- **The flat case of Stacks 0E23.** For a cartesian square

```
Z' --i'--> X'
|g          |f
Z --i-----> X
```

with `i` a closed immersion and `f` flat, `Lf^*(Ri_*K)` and `Ri'_*(Lg^*K)` are isomorphic for
every `K` in `D(𝒪_Z)`.

This is **not** Stacks 0E23, whose hypothesis is Tor independence of `Z` and `X'` over `X` and
not flatness of `f`; flatness is what the consumers of 0E23 in this file supply, and it is what
collapses the derived statement onto the underived one — all four functors become derived
functors of exact functors.

The conclusion is an unnamed isomorphism rather than invertibility of the canonical base change
map of Stacks 08HY, because
`AlgebraicGeometry.isPseudoCoherentFromAfterPushforward_baseChange_of_iso` uses 0E23 only
through its isomorphism class. -/
public theorem nonempty_derivedPullbackPushforwardIso (sq : IsPullback i' g f i)
    [IsClosedImmersion i] [Flat f] (K : DerivedCategory Z.Modules) :
    Nonempty ((derivedPullback f.toLRSHom.toShHom).obj
        ((derivedPushforward i.toLRSHom.toShHom).obj K) ≅
      (derivedPushforward i'.toLRSHom.toShHom).obj
        ((derivedPullback g.toLRSHom.toShHom).obj K)) :=
  have : IsClosedImmersion i' :=
    MorphismProperty.of_isPullback sq.flip ‹IsClosedImmersion i›
  have : Flat g := MorphismProperty.of_isPullback sq ‹Flat f›
  ⟨(derivedBaseChangeIsoOfIso (baseChangeIsoOfKernelAnnihilates sq.w
    (kernelAnnihilatesPullbackPushforward_of_isPullback sq))).app K⟩

/-- **The local condition of relative pseudo-coherence is inherited by a base change at which the
two sides are isomorphic.** This is
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_baseChange` with the
invertibility of the canonical base change map of Stacks 08HY replaced by the isomorphism it
produces, which is all the proof uses. -/
public theorem isPseudoCoherentFromAfterPushforward_baseChange_of_iso {U W P P' : Scheme.{u}}
    (i₀ : U ⟶ P) (e : W ⟶ P') (wU : W ⟶ U) (q : P' ⟶ P)
    [IsClosedImmersion i₀] [IsClosedImmersion e] (F : DerivedCategory U.Modules) (m : ℤ)
    (hF : Scheme.Modules.IsPseudoCoherentFromAfterPushforward i₀ F m)
    (eBC : (derivedPullback q.toLRSHom.toShHom).obj
        ((derivedPushforward i₀.toLRSHom.toShHom).obj F) ≅
      (derivedPushforward e.toLRSHom.toShHom).obj
        ((derivedPullback wU.toLRSHom.toShHom).obj F)) :
    Scheme.Modules.IsPseudoCoherentFromAfterPushforward e
      ((derivedPullback wU.toLRSHom.toShHom).obj F) m := by
  have h3 : RingedSpace.IsPseudoCoherentFrom (X := P'.toRingedSpace)
      ((derivedPullback q.toLRSHom.toShHom).obj
        ((derivedPushforward i₀.toLRSHom.toShHom).obj F)) m :=
    RingedSpace.KFlatDerivedPullback.isPseudoCoherentFrom_derivedPullback
      q.toLRSHom.toShHom _ m
      ((isPseudoCoherentFromAfterPushforward_iff_derivedPushforward i₀ F m).mp hF)
  exact (isPseudoCoherentFromAfterPushforward_iff_derivedPushforward e _ m).mpr (h3.of_iso eBC)

/-- The base change of a flat morphism to affine space is flat. -/
private theorem flat_affineSpace_map_resLE {S S' : Scheme.{u}} (g : S' ⟶ S) [Flat g]
    (V : S.Opens) (V' : S'.Opens) (hV' : V' ≤ g ⁻¹ᵁ V) (ι : Type u) :
    Flat (AffineSpace.map ι (g.resLE V V' hV')) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Flat)
    (AffineSpace.isPullback_map (n := ι) (g.resLE V V' hV')).flip inferInstance

/-- **Base change of relative pseudo-coherence along a flat morphism.** Let `f : X ⟶ S` be
locally of finite type, let `E` be an object of `D(𝒪_X)` which is `m`-pseudo-coherent relative to
`S`, and let `g : S' ⟶ S` be FLAT. Then the derived pullback of `E` to `X ×_S S'` is
`m`-pseudo-coherent relative to `S'`.

This is Stacks 09UR with its Tor independence hypothesis replaced by flatness of `g`, which
implies it, and with the appeal to Stacks 0E23 replaced by
`AlgebraicGeometry.nonempty_derivedPullbackPushforwardIso`: the chart square of the proof has
`AlgebraicGeometry.AffineSpace.map` of a restriction of `g` as its horizontal morphism, and that
is flat because flatness is stable under base change. Stacks 09UR itself, with its Tor
independence hypothesis, is
`AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_derivedPullback_of_torIndependentCharts`.

The covers, the chart geometry and the identification of the restricted derived pullback are the
ones of Stacks 09UR. -/
@[sga "6 III 1.10" "partial", sga "6 III 1.8" "special case"]
public theorem Scheme.Hom.isPseudoCoherentFrom_derivedPullback_of_flat
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] [Flat g]
    (E : DerivedCategory X.Modules) (m : ℤ) (hE : f.IsPseudoCoherentFrom E m) :
    (pullback.snd f g).IsPseudoCoherentFrom
      ((derivedPullback (pullback.fst f g).toLRSHom.toShHom).obj E) m := by
  classical
  refine ⟨Σ V : S.affineOpens, {V' : S'.affineOpens // V'.1 ≤ g ⁻¹ᵁ V.1}, fun a => a.2.1,
    ?_, fun a => ?_⟩
  · refine le_antisymm le_top fun y _ => ?_
    obtain ⟨V₀, hV₀, hyV₀, -⟩ :=
      exists_isAffineOpen_mem_and_subset (X := S) (x := g.base y) (U := (⊤ : S.Opens)) trivial
    obtain ⟨V'₀, hV'₀, hyV'₀, hV'sub⟩ :=
      exists_isAffineOpen_mem_and_subset (X := S') (x := y) (U := g ⁻¹ᵁ V₀) hyV₀
    exact Opens.mem_iSup.mpr ⟨⟨⟨V₀, hV₀⟩, ⟨⟨V'₀, hV'₀⟩, hV'sub⟩⟩, hyV'₀⟩
  · set V : S.affineOpens := a.1 with hV
    set V' : S'.affineOpens := a.2.1 with hV'def
    have hV' : V'.1 ≤ g ⁻¹ᵁ V.1 := a.2.2
    have : IsAffine (V.1 : Scheme.{u}) := V.2
    have : IsAffine (V'.1 : Scheme.{u}) := V'.2
    refine ⟨{U : X.affineOpens // U.1 ≤ f ⁻¹ᵁ V.1},
      fun p => ⟨pullback.fst f g ⁻¹ᵁ p.1.1 ⊓ pullback.snd f g ⁻¹ᵁ V'.1,
        have : IsAffine (p.1.1 : Scheme.{u}) := p.1.2
        isAffineOpen_inf_preimage f g p.2 hV'⟩, ?_, fun p => ?_⟩
    · refine le_antisymm (iSup_le fun p => inf_le_right) fun z hz => ?_
      have hxy : f.base ((pullback.fst f g).base z) = g.base ((pullback.snd f g).base z) := by
        simpa [Scheme.Hom.comp_base] using
          congrArg (fun k : pullback f g ⟶ S => k.base z) (pullback.condition (f := f) (g := g))
      have hfxV : f.base ((pullback.fst f g).base z) ∈ V.1 := hxy ▸ hV' hz
      obtain ⟨U₀, hU₀, hzU₀, hU₀sub⟩ :=
        exists_isAffineOpen_mem_and_subset (X := X) (x := (pullback.fst f g).base z)
          (U := f ⁻¹ᵁ V.1) hfxV
      exact Opens.mem_iSup.mpr ⟨⟨⟨U₀, hU₀⟩, hU₀sub⟩, ⟨hzU₀, hz⟩⟩
    · obtain ⟨n, i₀, hi, hio, hafter⟩ :=
        Scheme.Hom.isPseudoCoherentFromOnAffinePair_of_isPseudoCoherentFrom f hE p.1 V p.2
      have : IsClosedImmersion i₀ := hi
      obtain ⟨e, he, hebase, hSq⟩ :=
        exists_isClosedImmersion_baseChange_affineSpace f g p.2 hV' (ULift.{u} (Fin n)) i₀ hio
      have : IsClosedImmersion e := he
      have := flat_affineSpace_map_resLE g V.1 V'.1 hV' (ULift.{u} (Fin n))
      have hbase := isPseudoCoherentFromAfterPushforward_baseChange_of_iso i₀ e
        ((pullback.fst f g).resLE p.1.1 _ inf_le_left) (AffineSpace.map (ULift.{u} (Fin n))
          (g.resLE V.1 V'.1 hV')) _ m hafter
        (Classical.choice (nonempty_derivedPullbackPushforwardIso hSq.flip _))
      refine ⟨inf_le_right, n, e, he, hebase, hbase.of_iso e ?_⟩
      exact (Scheme.Modules.openRestrictionDerivedPullbackIso
        (pullback.fst f g ⁻¹ᵁ p.1.1 ⊓ pullback.snd f g ⁻¹ᵁ V'.1 : (pullback f g).Opens).ι
        (pullback.fst f g) p.1.1.ι ((pullback.fst f g).resLE p.1.1 _ inf_le_left)
        (Scheme.Hom.resLE_comp_ι (pullback.fst f g) inf_le_left).symm E).symm

end FlatBaseChange

/-! ### The affine case -/

/-- **The affine case of Stacks 09US, with the morphism factored through a flat chart.**
Stacks 09UU moves the conclusion along the closed immersion `i`, the composition isomorphism
splits `L(i ≫ p)^*` as `Li^* ∘ Lp^*`, and what is left is the affine core. -/
private theorem isPseudoCoherentFrom_derivedPullback_of_flatChart {U V W Z : Scheme.{u}}
    [IsAffine U] [IsAffine V] [IsAffine W] [IsAffine Z] (g₀ : V ⟶ W) [LocallyOfFiniteType g₀]
    (i : U ⟶ Z) [IsClosedImmersion i] (p : Z ⟶ V) [Flat p] [LocallyOfFinitePresentation p]
    (E₀ : DerivedCategory V.Modules) (m : ℤ) (hO : PseudoCoherent (i ≫ p))
    (hG : (p ≫ g₀).IsPseudoCoherentFrom ((derivedPullback p.toLRSHom.toShHom).obj E₀) m) :
    ((i ≫ p) ≫ g₀).IsPseudoCoherentFrom
      ((derivedPullback (i ≫ p).toLRSHom.toShHom).obj E₀) m := by
  have := hO
  refine (Scheme.Hom.isPseudoCoherentFrom_congr_hom (Category.assoc i p g₀) _ m).mp ?_
  refine (Scheme.Hom.isPseudoCoherentFrom_iff_derivedPushforwardRelative i (p ≫ g₀) _ m).mpr ?_
  have hs : i.toLRSHom.toShHom ≫ p.toLRSHom.toShHom = (i ≫ p).toLRSHom.toShHom := by
    simp only [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom]
  refine Scheme.Hom.IsPseudoCoherentFrom.of_iso _
    (isPseudoCoherentFrom_derivedPushforward_derivedPullback i (p ≫ g₀)
      (pseudoCoherent_appTop_of_comp i p hO) _ m hG) ?_
  exact (derivedPushforward i.toLRSHom.toShHom).mapIso
    ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
        i.toLRSHom.toShHom p.toLRSHom.toShHom).app E₀ ≪≫
      eqToIso (congrArg (fun k : U.toRingedSpace ⟶ V.toRingedSpace =>
        (derivedPullback k).obj E₀) hs))

/-- **Tor independence at an affine-space chart over a flat morphism.** The base change of a flat
morphism to affine space is flat, so every closed immersion of a chart is Tor independent from
it. -/
private theorem chartTorIndependence_of_flat {V W A : Scheme.{u}} (g₀ : V ⟶ W) (r : A ⟶ W)
    [Flat r] : g₀.ChartTorIndependence r := by
  intro T T' hT' U hUT n j _ _
  have := flat_affineSpace_map_resLE r T.1 T'.1 hT' (ULift.{u} (Fin n))
  exact torIndependent_of_flat_right j _

/-- **The affine case of Stacks 09US, given a flat, locally finitely presented chart.**
Stacks 09UR transports the hypothesis on `E₀` to the base change `V ×_W A`, and Stacks 09UT turns
relative `m`-pseudo-coherence over `A` into relative `m`-pseudo-coherence over `W`. -/
private theorem isPseudoCoherentFrom_derivedPullback_of_chart {U V W A : Scheme.{u}} [IsAffine U]
    [IsAffine V] [IsAffine W] (g₀ : V ⟶ W) [LocallyOfFiniteType g₀] (r : A ⟶ W) [Flat r]
    [LocallyOfFinitePresentation r] [IsAffine (pullback g₀ r)] (i : U ⟶ pullback g₀ r)
    [IsClosedImmersion i] (E₀ : DerivedCategory V.Modules) (m : ℤ)
    (hO : PseudoCoherent (i ≫ pullback.fst g₀ r)) (hE₀ : g₀.IsPseudoCoherentFrom E₀ m) :
    ((i ≫ pullback.fst g₀ r) ≫ g₀).IsPseudoCoherentFrom
      ((derivedPullback (i ≫ pullback.fst g₀ r).toLRSHom.toShHom).obj E₀) m := by
  refine isPseudoCoherentFrom_derivedPullback_of_flatChart g₀ i (pullback.fst g₀ r) E₀ m hO ?_
  refine (Scheme.Hom.isPseudoCoherentFrom_congr_hom
    (pullback.condition (f := g₀) (g := r)) _ m).mpr ?_
  exact (Scheme.Hom.isPseudoCoherentFrom_iff_comp (pullback.snd g₀ r) r _ m).mp
    (Scheme.Hom.isPseudoCoherentFrom_derivedPullback_of_flat g₀ r E₀ m hE₀)

/-- **The affine case of Stacks 09US.** Affine `d`-space over `V` is the base change of affine
`d`-space over `W` along `g₀`, which supplies the chart. -/
private theorem isPseudoCoherentFrom_derivedPullback_affine {U V W : Scheme.{u}} [IsAffine U]
    [IsAffine V] [IsAffine W] (f₀ : U ⟶ V) (g₀ : V ⟶ W) [LocallyOfFiniteType g₀]
    (E₀ : DerivedCategory V.Modules) (m : ℤ)
    (hO : PseudoCoherent f₀) (hE₀ : g₀.IsPseudoCoherentFrom E₀ m) :
    (f₀ ≫ g₀).IsPseudoCoherentFrom ((derivedPullback f₀.toLRSHom.toShHom).obj E₀) m := by
  have := hO
  obtain ⟨d, i₀, hclosed, hbase⟩ := exists_isClosedImmersion_affineSpace f₀
  have := hclosed
  have : Flat (𝔸(ULift.{u} (Fin d); W) ↘ W) := flat_affineSpace (ULift.{u} (Fin d)) W
  have hpb := (AffineSpace.isPullback_map (n := ULift.{u} (Fin d)) g₀).flip
  have : IsAffine (pullback g₀ (𝔸(ULift.{u} (Fin d); W) ↘ W)) :=
    IsAffine.of_isIso hpb.isoPullback.symm.hom
  have hbase' : (i₀ ≫ hpb.isoPullback.hom) ≫
      pullback.fst g₀ (𝔸(ULift.{u} (Fin d); W) ↘ W) = f₀ := by
    rw [Category.assoc, hpb.isoPullback_hom_fst]
    exact hbase
  subst hbase'
  exact isPseudoCoherentFrom_derivedPullback_of_chart g₀ (𝔸(ULift.{u} (Fin d); W) ↘ W)
    (i₀ ≫ hpb.isoPullback.hom) E₀ m hO hE₀

/-! ### Reduction to affine charts -/

/-- Relative `m`-pseudo-coherence may be checked on affine charts chosen near each point: the
affine opens of the base cover the base, and for a fixed base chart the affine opens carrying the
pair condition cover its inverse image. -/
private theorem isPseudoCoherentFrom_of_exists_affinePair {X S : Scheme.{u}} (q : X ⟶ S)
    [LocallyOfFiniteType q] (F : DerivedCategory X.Modules) (m : ℤ)
    (h : ∀ (W : S.affineOpens) (x : X), q.base x ∈ W.1 →
      ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ hUW : U.1 ≤ q ⁻¹ᵁ W.1,
        q.IsPseudoCoherentFromOnAffinePair F m U W hUW) :
    q.IsPseudoCoherentFrom F m := by
  refine ⟨S.affineOpens, id, iSup_affineOpens_eq_top S, fun W => ?_⟩
  refine ⟨{U : X.affineOpens // ∃ hUW : U.1 ≤ q ⁻¹ᵁ W.1,
    q.IsPseudoCoherentFromOnAffinePair F m U W hUW}, fun U => U.1, ?_, fun U => U.2⟩
  refine le_antisymm (iSup_le fun U => U.2.choose) fun x hx => ?_
  obtain ⟨U, hxU, hU⟩ := h W x hx
  exact Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hxU⟩

/-- Restricting a derived pullback to a chart `U ≤ f ⁻¹ᵁ V` is the derived pullback of the
restriction to `V` along the restricted morphism. -/
private def restrictDerivedPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens)
    (hUV : U ≤ f ⁻¹ᵁ V) (E : DerivedCategory Y.Modules) :
    (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj
        ((derivedPullback f.toLRSHom.toShHom).obj E) ≅
      (derivedPullback (f.resLE V U hUV).toLRSHom.toShHom).obj
        ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj E) :=
  Scheme.Modules.openRestrictionDerivedPullbackIso U.ι f V.ι (f.resLE V U hUV)
    (Scheme.Hom.resLE_comp_ι f hUV).symm E

/-- **Stacks 09US is affine-local.** It suffices to know the statement for a chain `U ⟶ V ⟶ W` of
affine schemes: the covers, the chart geometry and Stacks 09UJ are discharged here. -/
private theorem isPseudoCoherentFrom_derivedPullback_of_affine {X Y S : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ S) [PseudoCoherent f] [LocallyOfFiniteType g] (E : DerivedCategory Y.Modules)
    (m : ℤ) (hE : g.IsPseudoCoherentFrom E m)
    (haffine : ∀ (U V W : Scheme.{u}) [IsAffine U] [IsAffine V] [IsAffine W] (f₀ : U ⟶ V)
      (g₀ : V ⟶ W) [PseudoCoherent f₀] [LocallyOfFiniteType g₀]
      (E₀ : DerivedCategory V.Modules), g₀.IsPseudoCoherentFrom E₀ m →
      (f₀ ≫ g₀).IsPseudoCoherentFrom ((derivedPullback f₀.toLRSHom.toShHom).obj E₀) m) :
    (f ≫ g).IsPseudoCoherentFrom ((derivedPullback f.toLRSHom.toShHom).obj E) m := by
  refine isPseudoCoherentFrom_of_exists_affinePair (f ≫ g) _ m fun W x hx => ?_
  have hfx : f.base x ∈ g ⁻¹ᵁ W.1 := hx
  obtain ⟨V, hV, hfxV, hVW⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := f.base x)
    (U := g ⁻¹ᵁ W.1) hfx
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := x)
    (U := f ⁻¹ᵁ V) hfxV
  have hVW' : V ≤ g ⁻¹ᵁ W.1 := hVW
  have hUV' : U ≤ f ⁻¹ᵁ V := hUV
  have hUW : U ≤ (f ≫ g) ⁻¹ᵁ W.1 := by
    rw [Scheme.Hom.comp_preimage]
    exact hUV'.trans (f.preimage_mono hVW')
  have hUa : IsAffine (U : Scheme.{u}) := hU
  have hVa : IsAffine (V : Scheme.{u}) := hV
  have hWa : IsAffine (W.1 : Scheme.{u}) := W.2
  have hgr := locallyOfFiniteType_resLE g W.1 V hVW'
  refine ⟨⟨U, hU⟩, hxU, hUW, ?_⟩
  refine isPseudoCoherentFromOnAffinePair_of_isPseudoCoherentFrom_resLE (f ≫ g) _ m
    ⟨U, hU⟩ W hUW ?_
  have hmor : f.resLE V U hUV' ≫ g.resLE W.1 V hVW' = (f ≫ g).resLE W.1 U hUW := by
    rw [Scheme.Hom.resLE_comp_resLE]
  refine (Scheme.Hom.isPseudoCoherentFrom_congr_hom hmor _ m).mp ?_
  refine Scheme.Hom.IsPseudoCoherentFrom.of_iso _
    (haffine (U : Scheme.{u}) (V : Scheme.{u}) (W.1 : Scheme.{u}) (f.resLE V U hUV')
      (g.resLE W.1 V hVW') _
      (Scheme.Hom.IsPseudoCoherentFrom.resLE g E m V W.1 hVW' hE))
    (restrictDerivedPullbackIso f U V hUV' E).symm

/-! ### Stacks 09US -/

/-- **Stacks 09US.** Let `f : X ⟶ Y` be a pseudo-coherent morphism of schemes, let `g : Y ⟶ S` be
locally of finite type and let `E` be an object of `D(𝒪_Y)` which is `m`-pseudo-coherent relative
to `S`. Then the derived pullback `Lf^*E` is `m`-pseudo-coherent relative to `S`.

The hypothesis on `f` is `AlgebraicGeometry.PseudoCoherent`, which by Stacks 067Y is the
conjunction of the two hypotheses of the source: `f` is locally of finite type and `𝒪_X` is
pseudo-coherent relative to `Y`.

No hypothesis beyond those of the source is needed. The appeal the source makes to Stacks 0E23,
through Stacks 09UR, is at a square whose horizontal morphism is flat — it is
`AlgebraicGeometry.AffineSpace.map` of a restriction of the flat projection `𝔸ᵈ_W ⟶ W` — and that
case of 0E23 is `AlgebraicGeometry.nonempty_derivedPullbackPushforwardIso`, proved in this file. -/
@[stacks 09US]
public theorem Scheme.Hom.isPseudoCoherentFrom_comp_derivedPullback {X Y S : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ S) [PseudoCoherent f] [LocallyOfFiniteType g] (E : DerivedCategory Y.Modules)
    (m : ℤ) (hE : g.IsPseudoCoherentFrom E m) :
    (f ≫ g).IsPseudoCoherentFrom ((derivedPullback f.toLRSHom.toShHom).obj E) m := by
  refine isPseudoCoherentFrom_derivedPullback_of_affine f g E m hE ?_
  intro U V W _ _ _ f₀ g₀ hf₀ _ E₀ hE₀
  exact isPseudoCoherentFrom_derivedPullback_affine f₀ g₀ E₀ m hf₀ hE₀

end AlgebraicGeometry

end
