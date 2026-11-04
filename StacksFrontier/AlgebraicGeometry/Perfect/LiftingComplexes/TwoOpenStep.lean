module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.SupportedPushforward
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.TwoOpenLocality
public import StacksFrontier.AlgebraicGeometry.Perfect.LiftingComplexes.AffineCase
public import StacksFrontier.Topology.Sheaves.Cohomology.GlueingComplexes.TwoOpens
import StacksCore.Tactic.StacksAttribute

/-!
# Lifting a map from a perfect complex across one affine open

Let `X` be a scheme covered by a quasi-compact open `U` and the image of an open immersion
`f : Spec A ⟶ X`, let `T ⊆ X` be a closed subset whose preimage in `Spec A` has quasi-compact
complement, and let `E` be an object of `D_QCoh(𝒪_X)`. Every map `α : P ⟶ E|_U` out of a perfect
object `P` of `D(𝒪_U)` whose cohomology is supported on `T ∩ U` is, up to a direct summand, the
restriction of a map `β : R ⟶ E` out of a perfect object `R` of `D(𝒪_X)` whose cohomology is
supported on `T`.

This is the step of the induction of [Stacks, Tag 09IM] over an affine cover
`X = U ∪ V₁ ∪ … ∪ V_m`: the one place where glueing happens. The induction itself is
`Stacks.Perfect.LiftingComplexes.exists_isPerfect_lift_of_list`, and the tag is registered on
`Stacks.Perfect.LiftingComplexes.exists_isPerfect_lift`. The affine case
`Stacks.Perfect.LiftingComplexes.exists_isPerfect_lift_spec` produces over `Spec A` a perfect `Q`
supported on the preimage of `T`, a map `γ : Q ⟶ E|_{Spec A}` and an *isomorphism* of
`Q|_{f^{-1}U}` with `(P ⊞ P[1])|_{f^{-1}U}`; the second clause of [Stacks, Tag 08DG] glues
`P ⊞ P[1]` on `U` to `Q` on `Spec A` along that isomorphism and carries the pair
`biprod.fst ≫ α`, `γ` to a map out of the glued object. Perfectness and the support condition are
then read off the two restrictions by `Stacks.DerivedQCoh.isPerfect_of_cover` and
`Stacks.DerivedQCoh.cohomologySupportedOn_of_cover`.

The second open is presented as an open immersion *from a spectrum* rather than as an affine open
subscheme. That is what removes the need to transport [Stacks, Tag 08EK] and [Stacks, Tag 08EH]
off `Spec A`: the second clause of [Stacks, Tag 08DG] takes two arbitrary open immersions, so the
affine piece can be handed in as `Spec Γ(X, V)` through `AlgebraicGeometry.IsAffineOpen.fromSpec`,
and the affine case applies to it verbatim.

## Main results

* `Stacks.Perfect.LiftingComplexes.exists_isPerfect_lift_of_cover_spec`: **the glueing step of
  [Stacks, Tag 09IM]**.
* `Stacks.Perfect.LiftingComplexes.exists_glued_of_overlap_data`: the second clause of
  [Stacks, Tag 08DG] packaged for that step, at variable ringed spaces.
* `Stacks.Perfect.LiftingComplexes.overlap_compat`,
  `Stacks.Perfect.LiftingComplexes.trans_hom_comp_eq`: the two formal identities the glueing
  datum has to satisfy.
* `Stacks.Perfect.LiftingComplexes.exists_mapBiprodShift`: an additive shift-compatible functor
  carries `P ⊞ P[1]` to `F P ⊞ (F P)[1]`, compatibly with the first projection.
* `Stacks.Perfect.LiftingComplexes.isPerfect_of_eq_biprod`,
  `Stacks.Perfect.LiftingComplexes.cohomologySupportedOn_biprod`: perfectness and the support
  condition pass to a biproduct.

## Implementation notes

**Three spellings of restriction to an open meet here, and the proof is organized around them.**
[Stacks, Tag 08DG] is stated for the derived pullback
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback` along a morphism of ringed
spaces; the affine case and the support condition are stated for
`Stacks.Duality.OpenImmersion.derivedRestrict`, the functor Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` induces on derived categories; and perfectness
is local on the space in the spelling `AlgebraicGeometry.RingedSpace.restrictModules`. The first
two are crossed by `AlgebraicGeometry.Scheme.Modules.derivedRestrictIsoDerivedPullback` and the
last two inside `Stacks.DerivedQCoh.isPerfect_of_cover`.

**The compatibility on the intersection is free, because the map there is *defined* by
transport.** [Stacks, Tag 08DG] asks that the two maps out of the glueing datum agree on the
intersection through the canonical comparison `Stacks.Cohomology.GlueingComplexes.overlapIso` of
the two iterated restrictions. No coherence of that comparison with the change of spelling is
needed: the map fed to the affine case *is* the restriction of `α` composed with `overlapIso`, so
the affine case's own compatibility transports back to the required identity by
`Stacks.Perfect.LiftingComplexes.overlap_compat`, which is nothing but cancellation of two
isomorphisms and one naturality square. This is why the naturality in the open subspace of
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPullback/OpenImmersionRestrictionNaturality.lean`
is not needed here.

**Why the glueing is stated at variable ringed spaces.** `Stacks.Cohomology.GlueingComplexes`
writes the category of derived modules on a ringed space `Y` as
`DerivedCategory (SheafOfModules (structureSheafRing Y))`, which for `Y = X.toRingedSpace` is the
same type as `DerivedCategory X.Modules` -- but only by a conversion that is not available at
reducible transparency, and `CategoryTheory.Limits.HasZeroMorphisms` and
`CategoryTheory.Limits.HasBinaryBiproduct` are not *synthesizable* at the first spelling with a
concrete `Y`. Every step that forms a biproduct or rewrites under one is therefore either taken at
a variable ringed space -- `Stacks.Perfect.LiftingComplexes.exists_glued_of_overlap_data` -- or in
a category with no derived categories in it at all --
`Stacks.Perfect.LiftingComplexes.overlap_compat`,
`Stacks.Perfect.LiftingComplexes.trans_hom_comp_eq`,
`Stacks.Perfect.LiftingComplexes.exists_mapBiprodShift`. Only the statements of the two biproduct
lemmas are at a scheme, and they receive the biproduct rather than forming it, for a related
reason: `Stacks.Cohomology.PerfectComplexes.IsPerfect` is indexed by a ringed space and its
`CategoryTheory.HasDerivedCategory` argument can be fixed by unification with an already-typed
object but not by synthesis.

## References

* [Stacks Project, Lemma 36.13.11 (Tag 09IM)](https://stacks.math.columbia.edu/tag/09IM)
* [Stacks Project, Lemma 20.47.1 (Tag 08DG)](https://stacks.math.columbia.edu/tag/08DG)
* [Stacks Project, Lemma 36.13.10 (Tag 08EK)](https://stacks.math.columbia.edu/tag/08EK)
* [Stacks Project, Lemma 36.13.7 (Tag 08EH)](https://stacks.math.columbia.edu/tag/08EH)
* [Stacks Project, Lemma 36.60.9 (Tag 08CR)](https://stacks.math.columbia.edu/tag/08CR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.Pretriangulated
open Stacks.Cohomology.PerfectComplexes (IsPerfect)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.Cohomology.GlueingComplexes (DerivedModules overlapIso exists_glueing
  exists_hom_of_compatible)
open Stacks.Duality.OpenImmersion (derivedRestrict)
open Stacks.SchemeCohomology (ringedSpace hom)

namespace Stacks.Perfect.LiftingComplexes

universe u

attribute [local instance 10000] HasDerivedCategory.standard

/-- **A biproduct of perfect objects is perfect**, stated for an object *equal* to the
biproduct. -/
theorem isPerfect_of_eq_biprod {Y : RingedSpace.{u, u}}
    [HasDerivedCategory.{u + 1} (StrictlyPerfect.OXMod.{u, u} Y)]
    {K L M : DerivedCategory (StrictlyPerfect.OXMod.{u, u} Y)} (hM : M = (K ⊞ L))
    (hK : IsPerfect (X := Y) K) (hL : IsPerfect (X := Y) L) :
    IsPerfect (X := Y) M := by
  rw [hM]
  exact Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₂_of_distinguished
    (binaryBiproductTriangle K L) (binaryBiproductTriangle_distinguished K L) hK hL

/-- **The cohomology of a biproduct is supported where that of the two summands is.** -/
theorem cohomologySupportedOn_biprod (Y : Scheme.{u}) (T : Set Y) (hT : IsClosed T)
    (K L : DerivedCategory Y.Modules)
    (hK : CohomologySupportedOn Y.ringCatSheaf T K)
    (hL : CohomologySupportedOn Y.ringCatSheaf T L) :
    CohomologySupportedOn Y.ringCatSheaf T ((K ⊞ L : DerivedCategory Y.Modules)) :=
  Stacks.DerivedQCoh.OpenLift.cohomologySupportedOn_obj₃_of_distinguished Y T hT
    (binaryBiproductTriangle K L).invRotate
    (inv_rot_of_distTriang _ (binaryBiproductTriangle_distinguished K L))
    (Stacks.DerivedQCoh.cohomologySupportedOn_shift T L hL (-1)) hK

/-- **The compatibility [Stacks, Tag 08DG] asks for on the intersection, when the map there is
defined by transport.** Stated for two isomorphic functors between arbitrary categories: the
conversion check is then a computation on small terms. -/
theorem overlap_compat {C₂ D : Type*} [Category* C₂] [Category* D] (R₂ G : C₂ ⥤ D)
    (Θ : R₂ ≅ G) {AA : D} {Q EV EV' : C₂} (γ : Q ⟶ EV) (θ : EV ≅ EV')
    (c : AA ≅ R₂.obj Q) (ovm : AA ⟶ G.obj EV')
    (hc : c.hom ≫ R₂.map γ = ovm ≫ G.map θ.inv ≫ Θ.inv.app EV) :
    ovm = (c ≪≫ Θ.app Q).hom ≫ G.map (γ ≫ θ.hom) := by
  have h1 : (c ≪≫ Θ.app Q).hom ≫ G.map (γ ≫ θ.hom) =
      (c.hom ≫ R₂.map γ) ≫ Θ.hom.app EV ≫ G.map θ.hom := by
    rw [Iso.trans_hom, Functor.map_comp]
    simp only [Iso.app_hom, Category.assoc]
    rw [← Category.assoc (Θ.hom.app Q), ← Θ.hom.naturality γ]
    simp only [Category.assoc]
  have h3 : G.map θ.inv ≫ Θ.inv.app EV ≫ Θ.hom.app EV ≫ G.map θ.hom = 𝟙 (G.obj EV') := by
    rw [← Category.assoc (Θ.inv.app EV), Iso.inv_hom_id_app, Category.id_comp,
      ← Functor.map_comp, Iso.inv_hom_id]
    exact G.map_id _
  rw [h1, hc]
  simp only [Category.assoc]
  rw [h3, Category.comp_id]

/-- Composing an identity `e.hom ≫ g = π ≫ w` with an isomorphism in front, when the composite
`mbi.hom ≫ π` has a name. Stated in an arbitrary category: the identity is formal, and at the
derived categories of the two spellings of a scheme's modules the conversion check that would
identify the two sides is not type-correct at reducible transparency. -/
theorem trans_hom_comp_eq {D : Type*} [Category* D] {A B C₀ P' Z : D} (mbi : A ≅ B) (e : B ≅ C₀)
    (g : C₀ ⟶ Z) (π : B ⟶ P') (w : P' ⟶ Z) (m : A ⟶ P') (he : e.hom ≫ g = π ≫ w)
    (hm : mbi.hom ≫ π = m) : (mbi ≪≫ e).hom ≫ g = m ≫ w := by
  rw [Iso.trans_hom, Category.assoc, he, ← Category.assoc, hm]

/-- **[Stacks, Tag 08DG], second clause, in the form the lifting lemma uses it.** Stated at
variable ringed spaces, with the second open's restriction functor `RV` and its comparison `ΘV`
with the derived pullback given, so that the caller may present it in whichever spelling its
inputs are written in. -/
theorem exists_glued_of_overlap_data {XX XU XV XW : RingedSpace.{u, u}} (jU : XU ⟶ XX)
    (jV : XV ⟶ XX) (iU : XW ⟶ XU) (iV : XW ⟶ XV) [SheafedSpace.IsOpenImmersion jU]
    [SheafedSpace.IsOpenImmersion jV] (hpb : IsPullback iU iV jU jV)
    (hcov : Set.range jU.hom.base ∪ Set.range jV.hom.base = Set.univ)
    (EE : DerivedModules XX) (PP AA : DerivedModules XU) (QQ : DerivedModules XV)
    (ι₀ : PP ⟶ AA) (π₀ : AA ⟶ PP) (hsplit : ι₀ ≫ π₀ = 𝟙 PP)
    (RU : DerivedModules XX ⥤ DerivedModules XU)
    (ΘU : RU ≅ Stacks.Cohomology.GlueingComplexes.derivedRestrict jU)
    (RV : DerivedModules XV ⥤ DerivedModules XW)
    (ΘV : RV ≅ Stacks.Cohomology.GlueingComplexes.derivedRestrict iV)
    (EV : DerivedModules XV)
    (θ : EV ≅ (Stacks.Cohomology.GlueingComplexes.derivedRestrict jV).obj EE) (γ : QQ ⟶ EV)
    (α₀ : PP ⟶ RU.obj EE)
    (c : (Stacks.Cohomology.GlueingComplexes.derivedRestrict iU).obj AA ≅ RV.obj QQ)
    (hc : c.hom ≫ RV.map γ =
      (Stacks.Cohomology.GlueingComplexes.derivedRestrict iU).map π₀ ≫
        ((Stacks.Cohomology.GlueingComplexes.derivedRestrict iU).map
              (α₀ ≫ ΘU.hom.app EE) ≫
            (overlapIso jU jV iU iV hpb.w).hom.app EE) ≫
          (Stacks.Cohomology.GlueingComplexes.derivedRestrict iV).map θ.inv ≫
            ΘV.inv.app EV) :
    ∃ (R : DerivedModules XX) (φ : R ⟶ EE)
      (_fU : (Stacks.Cohomology.GlueingComplexes.derivedRestrict jU).obj R ≅ AA)
      (_fV : (Stacks.Cohomology.GlueingComplexes.derivedRestrict jV).obj R ≅ QQ)
      (i : PP ⟶ RU.obj R) (p : RU.obj R ⟶ PP),
      i ≫ p = 𝟙 PP ∧ i ≫ RU.map φ = α₀ := by
  obtain ⟨G⟩ := exists_glueing jU jV iU iV hpb AA QQ (c ≪≫ ΘV.app QQ)
  have hG := exists_hom_of_compatible jU jV iU iV hpb hcov G
  have hc' : c.hom ≫ RV.map γ =
      ((Stacks.Cohomology.GlueingComplexes.derivedRestrict iU).map
            (π₀ ≫ α₀ ≫ ΘU.hom.app EE) ≫
          (overlapIso jU jV iU iV hpb.w).hom.app EE) ≫
        (Stacks.Cohomology.GlueingComplexes.derivedRestrict iV).map θ.inv ≫
          ΘV.inv.app EV := by
    rw [hc]
    simp only [Functor.map_comp, Category.assoc]
  obtain ⟨φ, hφU, hφV⟩ := hG EE (π₀ ≫ α₀ ≫ ΘU.hom.app EE) (γ ≫ θ.hom)
    (overlap_compat RV _ ΘV γ θ c _ hc')
  refine ⟨G.F, φ, G.f, G.g, ι₀ ≫ G.f.inv ≫ ΘU.inv.app G.F,
    ΘU.hom.app G.F ≫ G.f.hom ≫ π₀, ?_, ?_⟩
  · simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_assoc]
    exact hsplit
  · have hn := ΘU.inv.naturality φ
    simp only [Category.assoc]
    rw [← hn, hφU]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_app]
    rw [Category.comp_id, ← Category.assoc, hsplit, Category.id_comp]

/-- The restriction of `P ⊞ P[1]` along a functor is the biproduct of the restriction and its
shift, by a comparison carrying the first projection to the restriction of the first
projection. -/
theorem exists_mapBiprodShift {C D : Type*} [Category* C] [Category* D] [Preadditive C]
    [Preadditive D] [HasBinaryBiproducts C] [HasBinaryBiproducts D] [HasShift C ℤ]
    [HasShift D ℤ] (F : C ⥤ D) [F.Additive] [F.CommShift ℤ] (P : C) :
    ∃ m : F.obj (P ⊞ P⟦(1 : ℤ)⟧) ≅ F.obj P ⊞ (F.obj P)⟦(1 : ℤ)⟧,
      m.hom ≫ biprod.fst = F.map biprod.fst := by
  refine ⟨({ hom := biprod.lift (F.map biprod.fst) (F.map biprod.snd)
             inv := biprod.desc (F.map biprod.inl) (F.map biprod.inr)
             hom_inv_id := ?_
             inv_hom_id := ?_ } :
        F.obj (P ⊞ P⟦(1 : ℤ)⟧) ≅ F.obj P ⊞ F.obj (P⟦(1 : ℤ)⟧)) ≪≫
      biprod.mapIso (Iso.refl _) ((F.commShiftIso (1 : ℤ)).app P), ?_⟩
  · rw [biprod.lift_desc]
    simp only [← Functor.map_comp, ← F.map_add, biprod.total]
    exact F.map_id _
  · ext <;> simp [← Functor.map_comp]
  · simp only [Iso.trans_hom, Category.assoc, biprod.mapIso_hom, biprod.map_fst, Iso.refl_hom,
      Category.comp_id]
    exact biprod.lift_fst _ _

/-- **The glueing step of [Stacks, Tag 09IM].** Let `X` be a scheme covered by the images of an
open immersion `g : Y ⟶ X` and an open immersion `f : Spec A ⟶ X`, let `T ⊆ X` be closed with
quasi-compact complement in `Spec A`, let the intersection be quasi-compact in `Spec A`, and let
`E` be an object of `D(𝒪_X)` with quasi-coherent cohomology. Every map `α : P ⟶ E|_Y` out of a
perfect object `P` of `D(𝒪_Y)` whose cohomology is supported on the preimage of `T` comes from a
map `β : R ⟶ E` out of a perfect object `R` of `D(𝒪_X)` supported on `T`, with `R|_Y` identified
with `P ⊞ P[1]` and `P` a direct summand of it compatibly with `α` and `β|_Y`.

The identification of `R|_Y` is recorded because it, and not only the splitting, is what bounds
the cohomology of `R` on `Y`: `P ⊞ P[1]` has no cohomology above the top degree of `P`.

This is the case `m = 1` of the induction of [Stacks, Tag 09IM]: the affine case
`Stacks.Perfect.LiftingComplexes.exists_isPerfect_lift_spec` produces over `Spec A` a perfect `Q`
supported on the preimage of `T` together with an identification of `Q|_{f^{-1}Y}` with
`(P ⊞ P[1])|_{f^{-1}Y}`, and the second clause of [Stacks, Tag 08DG] glues `P ⊞ P[1]` on `Y` to
`Q` on `Spec A` along that identification, carrying with it the pair of maps to `E`.

Both opens are presented by open immersions rather than as subschemes. For the affine one that is
what keeps the affine case applicable verbatim; for the first one it is what makes the lemma
usable in the induction of [Stacks, Tag 08DR], where the ambient scheme is a varying open
subscheme of a fixed one and `Y` stays put. -/
theorem exists_isPerfect_lift_of_cover_spec {X Y : Scheme.{u}} {A : CommRingCat.{u}}
    (g : Y ⟶ X) (f : Spec A ⟶ X) [IsOpenImmersion g] [IsOpenImmersion f]
    (hcover : ∀ x : X, x ∈ Set.range ⇑g.base ∨ x ∈ Set.range ⇑f.base)
    (T : Set X) (hT : IsClosed T) (hTf : IsCompact ((⇑f.base ⁻¹' T)ᶜ : Set (Spec A)))
    (hW : IsCompact ((f ⁻¹ᵁ g.opensRange : (Spec A).Opens) : Set (Spec A)))
    (E : DerivedCategory X.Modules)
    (hE : Stacks.DerivedQCoh.IsDQCoh (R := X.ringCatSheaf) E)
    (P : DerivedCategory Y.Modules)
    (hP : IsPerfect (X := ringedSpace Y) P)
    (hPT : CohomologySupportedOn Y.ringCatSheaf (⇑g.base ⁻¹' T) P)
    (α : P ⟶ (derivedRestrict g).obj E) :
    ∃ (R : DerivedCategory X.Modules) (β : R ⟶ E),
      IsPerfect (X := ringedSpace X) R ∧
      CohomologySupportedOn X.ringCatSheaf T R ∧
      Nonempty ((derivedRestrict g).obj R ≅
        (P ⊞ P⟦(1 : ℤ)⟧ : DerivedCategory Y.Modules)) ∧
      ∃ (i : P ⟶ (derivedRestrict g).obj R) (p : (derivedRestrict g).obj R ⟶ P),
        i ≫ p = 𝟙 P ∧ i ≫ (derivedRestrict g).map β = α := by
  classical
  -- the intersection, and its two inclusions
  have hrange : Set.range ⇑((f ⁻¹ᵁ g.opensRange).ι ≫ f).base ⊆ Set.range ⇑g.base := by
    rintro x ⟨z, rfl⟩
    exact z.2
  obtain ⟨iU, hiUfac⟩ : ∃ iU : (f ⁻¹ᵁ g.opensRange).toScheme ⟶ Y,
      iU ≫ g = (f ⁻¹ᵁ g.opensRange).ι ≫ f :=
    ⟨IsOpenImmersion.lift g _ hrange, IsOpenImmersion.lift_fac _ _ hrange⟩
  have hiU : IsOpenImmersion iU := by
    have hcomp : IsOpenImmersion (iU ≫ g) := by rw [hiUfac]; infer_instance
    exact IsOpenImmersion.of_comp iU g
  have hbase : ∀ z : (f ⁻¹ᵁ g.opensRange).toScheme,
      ⇑g.base (⇑iU.base z) = ⇑f.base (⇑(f ⁻¹ᵁ g.opensRange).ι.base z) := by
    intro z
    simpa using congrArg (fun k : (f ⁻¹ᵁ g.opensRange).toScheme ⟶ X => ⇑k.base z) hiUfac
  -- the Cartesian square of ringed spaces and the cover
  have hcomm : hom iU ≫ hom g = hom (f ⁻¹ᵁ g.opensRange).ι ≫ hom f := by
    simpa only [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom] using
      congrArg (fun k : (f ⁻¹ᵁ g.opensRange).toScheme ⟶ X => k.toLRSHom.toShHom) hiUfac
  have hpb : IsPullback (hom iU) (hom (f ⁻¹ᵁ g.opensRange).ι) (hom g) (hom f) := by
    refine Stacks.DerivedQCoh.isPullback_of_range _ _ _ _ hcomm fun z hz => ?_
    exact ⟨⟨z, hz⟩, rfl⟩
  have hcov : Set.range (hom g).hom.base ∪ Set.range (hom f).hom.base = Set.univ :=
    Set.eq_univ_of_forall fun x => hcover x
  -- the affine case over `Spec A`
  have hP' := AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
    (hom iU) P hP
  have hsets : ⇑iU.base ⁻¹' (⇑g.base ⁻¹' T) =
      (Subtype.val ⁻¹' (⇑f.base ⁻¹' T) : Set (f ⁻¹ᵁ g.opensRange).toScheme) := by
    ext z
    show ⇑g.base (⇑iU.base z) ∈ T ↔ ⇑f.base (⇑(f ⁻¹ᵁ g.opensRange).ι.base z) ∈ T
    rw [hbase z]
  have hP'T : CohomologySupportedOn (f ⁻¹ᵁ g.opensRange).toScheme.ringCatSheaf
      (Subtype.val ⁻¹' (⇑f.base ⁻¹' T)) ((derivedPullback (hom iU)).obj P) := by
    refine Stacks.Cohomology.PushforwardRestriction.cohomologySupportedOn_of_iso _ _
      ((Scheme.Modules.derivedRestrictIsoDerivedPullback iU).app P) ?_
    rw [← hsets]
    exact Stacks.DerivedQCoh.cohomologySupportedOn_derivedRestrictFunctor iU
      (⇑g.base ⁻¹' T) P hPT
  obtain ⟨Q, γ, hQp, hQT, e, he⟩ :=
    exists_isPerfect_lift_spec (A := A) (⇑f.base ⁻¹' T)
      (hT.preimage f.base.hom.continuous) hTf (f ⁻¹ᵁ g.opensRange) hW
      ((derivedRestrict f).obj E) (Stacks.DerivedQCoh.isDQCoh_derivedRestrict f E hE)
      ((derivedPullback (hom iU)).obj P) hP' hP'T
      (((derivedPullback (hom iU)).map
            (α ≫ (Scheme.Modules.derivedRestrictIsoDerivedPullback g).hom.app E) ≫
          (overlapIso (hom g) (hom f) (hom iU)
            (hom (f ⁻¹ᵁ g.opensRange).ι) hpb.w).hom.app E) ≫
        (derivedPullback (hom (f ⁻¹ᵁ g.opensRange).ι)).map
            ((Scheme.Modules.derivedRestrictIsoDerivedPullback f).inv.app E) ≫
          (Scheme.Modules.derivedRestrictIsoDerivedPullback (f ⁻¹ᵁ g.opensRange).ι).inv.app
            ((derivedRestrict f).obj E))
  -- the comparison of the restriction of the biproduct with the biproduct of the restrictions
  obtain ⟨mbi, hmbi⟩ := exists_mapBiprodShift
    (derivedPullback (hom iU) :
      DerivedCategory Y.Modules ⥤ DerivedCategory (f ⁻¹ᵁ g.opensRange).toScheme.Modules) P
  -- the glueing
  obtain ⟨R, φ, fU, fV, i, p, hip, hiφ⟩ := exists_glued_of_overlap_data (hom g) (hom f)
    (hom iU) (hom (f ⁻¹ᵁ g.opensRange).ι) hpb hcov E P
    (P ⊞ P⟦(1 : ℤ)⟧ : DerivedCategory Y.Modules) Q
    (biprod.inl : P ⟶ (P ⊞ P⟦(1 : ℤ)⟧ : DerivedCategory Y.Modules))
    (biprod.fst : (P ⊞ P⟦(1 : ℤ)⟧ : DerivedCategory Y.Modules) ⟶ P)
    (biprod.inl_fst :
      (biprod.inl : P ⟶ (P ⊞ P⟦(1 : ℤ)⟧ : DerivedCategory Y.Modules)) ≫
        biprod.fst = 𝟙 P)
    (derivedRestrict g)
    (Scheme.Modules.derivedRestrictIsoDerivedPullback g)
    (derivedRestrict (f ⁻¹ᵁ g.opensRange).ι)
    (Scheme.Modules.derivedRestrictIsoDerivedPullback (f ⁻¹ᵁ g.opensRange).ι)
    ((derivedRestrict f).obj E)
    ((Scheme.Modules.derivedRestrictIsoDerivedPullback f).app E)
    γ α (mbi ≪≫ e) (trans_hom_comp_eq mbi e _ biprod.fst _ _ he hmbi)
  -- assembling the conclusion
  have hAAp := isPerfect_of_eq_biprod (Y := ringedSpace Y)
    (show (P ⊞ P⟦(1 : ℤ)⟧ : DerivedCategory Y.Modules) = _ from rfl) hP
    (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_shift hP 1)
  have hAAT := cohomologySupportedOn_biprod Y (⇑g.base ⁻¹' T)
    (hT.preimage g.base.hom.continuous) P (P⟦(1 : ℤ)⟧) hPT
    (Stacks.DerivedQCoh.cohomologySupportedOn_shift _ P hPT 1)
  have eU := (Scheme.Modules.derivedRestrictIsoDerivedPullback g).app R ≪≫ fU
  have eV := (Scheme.Modules.derivedRestrictIsoDerivedPullback f).app R ≪≫ fV
  refine ⟨R, φ, ?_, ?_, ⟨eU⟩, i, p, hip, hiφ⟩
  · exact Stacks.DerivedQCoh.isPerfect_of_cover g f hcover R
      (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso.{u, u + 1} eU.symm hAAp)
      (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso.{u, u + 1} eV.symm hQp)
  · exact Stacks.DerivedQCoh.cohomologySupportedOn_of_cover g f hcover T R
      (Stacks.Cohomology.PushforwardRestriction.cohomologySupportedOn_of_iso _ _ eU.symm hAAT)
      (Stacks.Cohomology.PushforwardRestriction.cohomologySupportedOn_of_iso _ _ eV.symm hQT)

end Stacks.Perfect.LiftingComplexes

end
