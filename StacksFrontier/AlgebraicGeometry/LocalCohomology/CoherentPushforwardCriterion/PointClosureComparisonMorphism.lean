module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import StacksFrontier.AlgebraicGeometry.AssociatedPointsMono.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.LocalHom
public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.StructureSheafCoherent
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.StructureSheafStalk
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.AssociatedPointResidueField
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.PointClosureAssociatedPoints
public import
  StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.PrincipalIdealExtension
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization

/-!
# The comparison morphism of Stacks 0BJZ, built from an associated point

Let `U` be a locally Noetherian scheme, `F` an `𝒪_U`-module and `x ∈ U` a point associated to
`F`. Write `i_x : W_x → U` for the integral closed subscheme with generic point `x` and
`G = i_{x,*} 𝒪_{W_x}` for `AlgebraicGeometry.pointClosureStructureSheaf x`. The proof of
[Stacks, Tag 0BJZ] produces from `x ∈ Ass(F)` a monomorphism `G ⟶ F`, in three moves: the
associated-point hypothesis gives an injection `κ(x) → F_x`; the stalk `G_x` *is* `κ(x)`, so
that injection is a map `G_x → F_x`; [Stacks, Tag 01Y4] spreads it to a morphism over some open
neighbourhood of `x`; and [Stacks, Tag 01YB], after multiplication by a power of a global
function not vanishing at `x`, extends that to all of `U`.

This file carries out all four moves. The first three need only local Noetherianity of `U`; the
fourth needs `U` Noetherian *and* quasi-affine, because the function to multiply by must be a
global section of `𝒪_U` whose non-vanishing locus is a small neighbourhood of `x`.

## Main results

All in the namespace `Stacks.AlgebraicGeometry.PointClosureComparison`.

* `nonempty_stalkLinearEquiv_residueField_pointClosureStructureSheaf` and
  `isSimpleModule_stalk_pointClosureStructureSheaf`: **`G_x = κ(x)`**, the identity the source
  states as "we have `𝒢_x = κ(x)`", and its consequence that `G_x` is a simple module.
* `exists_hom_over_germ_eq_of_isSimpleModule`: **the spreading step.** From `x ∈ Ass(F)` there
  is an open `V ∋ x` and a morphism `G|_V ⟶ F|_V` whose map on stalks at `x` is injective.
* `exists_mono_of_isSimpleModule` and `exists_mono_of_isAssociatedPoint`: **the comparison
  morphism.** On a Noetherian quasi-affine `U` the morphism extends over `U` and is a
  monomorphism.
* `isCoherent_pushforward_pointClosure_of_isAssociatedPoint`: the implication (2) ⇒ (1) of
  [Stacks, Tag 0BJZ] at `x` with the monomorphism hypothesis of
  `AlgebraicGeometry.isCoherent_pushforward_pointClosure_of_mono` discharged.

The spreading and extension steps are stated for an arbitrary coherent `G` whose stalk at `x` is
simple and whose only possible associated point is `x`, since that is all the argument uses;
`i_{x,*} 𝒪_{W_x}` has both properties. The extra generality is what lets the affine reduction of
`isCoherent_pushforward_pointClosure_of_isAssociatedPoint'`, in the namespace
`Stacks.AlgebraicGeometry.CoherenceFromPointClosures`, run at the *restriction* of
`i_{x,*} 𝒪_{W_x}` to an open subscheme, without having to identify that restriction with a
point-closure sheaf of the open subscheme.

## Implementation notes

**`G_x = κ(x)`.** `W_x` is integral, so its local ring at its generic point is its function
field, hence a field; the stalk map `𝒪_{U, x} → 𝒪_{W_x, x}` of a closed immersion is a surjective
local homomorphism, so its kernel is the preimage of the zero ideal, which is the maximal ideal.
That gives `𝒪_{U,x} ⧸ 𝔪_x ≅ 𝒪_{W_x, x}` as `𝒪_{U,x}`-modules, and
`AlgebraicGeometry.stalk_isomorphic_pushforward_of_finite_singleton_fiber` together with
`AlgebraicGeometry.structureSheafStalkLinearEquiv` identifies `𝒪_{W_x, x}` with `G_x`. The
residue field is spelled as the quotient `𝒪_{U,x} ⧸ 𝔪_x`, which is the spelling used by
`isAssociatedPoint_iff_exists_injective_residueField` of the namespace
`Stacks.AlgebraicGeometry.AssociatedPointResidueField`.

**The spreading step** is [Stacks, Tag 01Y4] through
`Stacks.SheafOfModules.SheafHomStalk.exists_localHom_of_stalkLinearMap`, whose hypothesis is
finite presentation of the source. `G` is coherent — it is a direct image of a structure sheaf
along a closed immersion, so
`Stacks.AlgebraicGeometry.ClosedImmersionCoherence.isCoherent_pushforward_iff` reduces this to
coherence of `𝒪_{W_x}` — and a coherent module is of finite presentation.

**The extension step** is
`Stacks.AlgebraicGeometry.PrincipalIdealExtension.exists_hom_app_eq_overApp_smul_pow_basicOpen`,
which needs its morphism to be given on a *principal* open `D(f)` for a global `f`, while
Tag 01Y4 produces one on an arbitrary neighbourhood `V`. `overRestrict` bridges that: it
restricts a morphism of restricted modules along `W ≤ V`, and `overApp_overRestrict` says it does
not change the values on sections, which is true by definition because the comparison
isomorphisms of `SheafOfModules.overFunctorMap` are identities on sections. Choosing `f` with
`x ∈ D(f) ⊆ V` is exactly what quasi-affineness of `U` supplies, through
`AlgebraicGeometry.Scheme.IsQuasiAffine.isBasis_basicOpen`.

**Why the extension needs more than `IsLocallyNoetherian U`.** The conclusion of
`exists_mono_of_isAssociatedPoint` is false for a general locally Noetherian `U`: on `U = ℙ¹`
over a field, with `F = 𝒪(-1)` and `x` the generic point, `x ∈ Ass(F)` holds, `W_x = U` and
`G = 𝒪_U`, and `Hom(𝒪_U, 𝒪(-1)) = Γ(ℙ¹, 𝒪(-1)) = 0`, so the only morphism `G ⟶ F` is zero and
no monomorphism exists. The source's proof of [Stacks, Tag 0BJZ] reduces to `X` affine before
constructing the morphism, which makes `U` a quasi-compact open subscheme of an affine scheme,
hence quasi-affine; that is the hypothesis used here.

Consequently `isCoherent_pushforward_pointClosure_of_isAssociatedPoint` is not yet 0BJZ's
clause (2) ⇒ (1), which is stated for an arbitrary open immersion of locally Noetherian schemes,
and so carries no tag — the same convention as
`AlgebraicGeometry.isCoherent_pushforward_pointClosure_of_injective_stalk_at`. The source's
reduction of the *coherence statement* to an affine base is carried out in
`StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.CoherenceEquivalence`,
which turns this into the unconditional clause.

## References

* [Stacks Project, Tag 0BJZ](https://stacks.math.columbia.edu/tag/0BJZ)
* [Stacks Project, Tag 01Y4](https://stacks.math.columbia.edu/tag/01Y4)
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
* [Stacks Project, Tag 0AVL](https://stacks.math.columbia.edu/tag/0AVL)
* [Stacks Project, Tag 02OJ](https://stacks.math.columbia.edu/tag/02OJ)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.PrincipalIdealExtension
open Stacks.RingedSpace

universe u

namespace Stacks.AlgebraicGeometry.IdealPowerColimit

/-- **Restriction of a morphism of restricted modules to a smaller open.** For `W ≤ V` a morphism
`G|_V ⟶ F|_V` restricts to a morphism `G|_W ⟶ F|_W`, by transporting along the pushforward
comparison `SheafOfModules.overFunctorMap` of the inclusion `W ⟶ V`. -/
noncomputable def overRestrict {X : Scheme.{u}} {G F : X.Modules} {V W : X.Opens} (hWV : W ≤ V)
    (θ : G.over V ⟶ F.over V) : G.over W ⟶ F.over W :=
  (SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE hWV)).inv.app G ≫
    (SheafOfModules.overMap X.ringCatSheaf (homOfLE hWV)).map θ ≫
    (SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE hWV)).hom.app F

/-- Restricting a morphism of restricted modules does not change its values on sections: the
comparison isomorphisms it is conjugated by are identities on sections. -/
theorem overApp_overRestrict {X : Scheme.{u}} {G F : X.Modules} {V W : X.Opens} (hWV : W ≤ V)
    (θ : G.over V ⟶ F.over V) {V' : X.Opens} (hV'W : V' ≤ W) (g : Γ(G, V')) :
    overApp (overRestrict hWV θ) hV'W g = overApp θ (hV'W.trans hWV) g := rfl

end Stacks.AlgebraicGeometry.IdealPowerColimit

open Stacks.AlgebraicGeometry.IdealPowerColimit

namespace Stacks.AlgebraicGeometry.PointClosureComparison

/-- **A surjective local homomorphism onto a field identifies the field with the residue field of
the source.** If `φ : R → S` is a surjective local homomorphism of local rings and `S` is a
field, then `S`, read as an `R`-module along `φ`, is `R ⧸ 𝔪_R`.

The kernel of `φ` is the `φ`-preimage of the zero ideal, which is the preimage of the maximal
ideal of `S` because `S` is a field, and that preimage is `𝔪_R`. -/
theorem nonempty_linearEquiv_residueField_of_surjective {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (φ : R →+* S) [IsLocalHom φ] (hφ : Function.Surjective φ)
    (hS : IsField S) :
    letI : Module R S := Module.compHom S φ
    Nonempty ((R ⧸ IsLocalRing.maximalIdeal R) ≃ₗ[R] S) := by
  let _ : Module R S := Module.compHom S φ
  have hsmul : ∀ (r : R) (s : S), r • s = φ r * s := fun _ _ => rfl
  let f : R →ₗ[R] S :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := fun r s => by
        simp only [hsmul, RingHom.id_apply, smul_eq_mul, map_mul] }
  have hker : LinearMap.ker f = IsLocalRing.maximalIdeal R := by
    have h1 := IsLocalRing.maximalIdeal_comap φ
    rw [IsLocalRing.isField_iff_maximalIdeal_eq.mp hS] at h1
    ext r
    simpa [LinearMap.mem_ker, f, Ideal.mem_comap] using congrArg (fun I => r ∈ I) h1
  exact ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans
    (LinearMap.quotKerEquivOfSurjective f hφ)⟩

/-- **The stalk of `i_* 𝒪_W` at the image of the generic point is the residue field there.** For
`i : W ⟶ U` a closed immersion from an integral scheme and `y` the image of the generic point of
`W`, the stalk of `i_* 𝒪_W` at `y` is `𝒪_{U, y} ⧸ 𝔪_y` as an `𝒪_{U, y}`-module.

The fibre of `i` over `y` is a single point, so the stalk of the direct image at `y` is the stalk
of `𝒪_W` at the generic point, which is the function field of `W` and hence a field; the stalk
map of `i` is then a surjective local homomorphism onto a field. -/
theorem nonempty_stalkLinearEquiv_residueField_pushforward_unit {W U : Scheme.{u}} (i : W ⟶ U)
    [IsClosedImmersion i] [IsIntegral W] (y : U) (hy : i (genericPoint W) = y) :
    Nonempty (TopCat.Presheaf.stalk (C := Ab.{u})
        ((Scheme.Modules.pushforward i).obj (structureSheafModule W)).val.presheaf y
      ≃ₗ[U.presheaf.stalk y]
        (U.presheaf.stalk y ⧸ IsLocalRing.maximalIdeal (U.presheaf.stalk y))) := by
  subst hy
  have hfib : i ⁻¹' ({i (genericPoint W)} : Set U) = {genericPoint W} :=
    Set.eq_singleton_iff_unique_mem.2
      ⟨rfl, fun z hz => (IsClosedImmersion.isClosedEmbedding i).injective hz⟩
  let φ := ConcreteCategory.hom (i.stalkMap (genericPoint W))
  let _ : Module (U.presheaf.stalk (i (genericPoint W)))
      (ToType (W.presheaf.stalk (genericPoint W))) := Module.compHom _ φ
  let _ : Module (U.presheaf.stalk (i (genericPoint W)))
      (TopCat.Presheaf.stalk (C := Ab.{u}) (structureSheafModule W).val.presheaf
        (genericPoint W)) := Module.compHom _ φ
  obtain ⟨e1⟩ := stalk_isomorphic_pushforward_of_finite_singleton_fiber i (genericPoint W) hfib
    (structureSheafModule W)
  obtain ⟨e3⟩ := nonempty_linearEquiv_residueField_of_surjective φ
    (i.stalkMap_surjective (genericPoint W)) (Field.toIsField (ToType W.functionField))
  let e2 := structureSheafStalkLinearEquiv W (genericPoint W)
  let e2' : (TopCat.Presheaf.stalk (C := Ab.{u}) (structureSheafModule W).val.presheaf
        (genericPoint W)) ≃ₗ[U.presheaf.stalk (i (genericPoint W))]
      (ToType (W.presheaf.stalk (genericPoint W))) :=
    { e2.toAddEquiv with map_smul' := fun r m => e2.map_smul (φ r) m }
  exact ⟨(e1.toLinearEquiv.symm.trans e2').trans e3.symm⟩

/-- **`G_x = κ(x)`.** The stalk at `x` of `i_{x,*} 𝒪_{W_x}` is the residue field `𝒪_{U,x} ⧸ 𝔪_x`,
as an `𝒪_{U,x}`-module. This is the identity the proof of [Stacks, Tag 0BJZ] states as
"we have `𝒢_x = κ(x)`". -/
theorem nonempty_stalkLinearEquiv_residueField_pointClosureStructureSheaf {U : Scheme.{u}}
    (x : U) :
    Nonempty (TopCat.Presheaf.stalk (C := Ab.{u})
        (pointClosureStructureSheaf x).val.presheaf x
      ≃ₗ[U.presheaf.stalk x]
        (U.presheaf.stalk x ⧸ IsLocalRing.maximalIdeal (U.presheaf.stalk x))) :=
  have : IsIntegral (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set U))).subscheme :=
    Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure x
  nonempty_stalkLinearEquiv_residueField_pushforward_unit _ x
    (Scheme.IdealSheafData.subschemeι_genericPoint_vanishingIdeal_closure x)

/-- **`i_{x,*} 𝒪_{W_x}` is coherent on a locally Noetherian scheme.** By
[Stacks, Tag 01Y6] for the closed immersion `i_x` this is coherence of `𝒪_{W_x}`, which holds
because `W_x` is locally Noetherian. -/
theorem isCoherent_pointClosureStructureSheaf {U : Scheme.{u}} [IsLocallyNoetherian U] (x : U) :
    (pointClosureStructureSheaf x).IsCoherent := by
  have : IsLocallyNoetherian (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set U))).subscheme :=
    Scheme.IdealSheafData.isLocallyNoetherian_subscheme _
  exact (ClosedImmersionCoherence.isCoherent_pushforward_iff _ _).mpr
    (CoherentTFAE.isCoherent_unit _)

/-- **A module with simple stalk at an associated point of `F` injects into `F` on stalks.** If
`G_x` is a simple `𝒪_{U,x}`-module — equivalently `G_x = κ(x)` — and `x` is associated to `F`,
then `G_x` injects into `F_x`.

A simple module over a local ring is its residue field, and the associated-point hypothesis gives
an injection `κ(x) → F_x` ([Stacks, Tag 02OJ], in the form
`isAssociatedPoint_iff_exists_injective_residueField` of the namespace
`Stacks.AlgebraicGeometry.AssociatedPointResidueField`). -/
theorem exists_injective_stalkLinearMap_of_isSimpleModule {U : Scheme.{u}} (G F : U.Modules)
    (x : U) (hG : IsSimpleModule (U.presheaf.stalk x) (G.presheaf.stalk x))
    (hx : Stacks.Divisors.IsAssociatedPoint F x) :
    ∃ ψ : TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x
            →ₗ[U.presheaf.stalk x] TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x,
      Function.Injective ψ := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hG
  obtain rfl := IsLocalRing.eq_maximalIdeal hI
  obtain ⟨φ, hφ⟩ :=
    (AssociatedPointResidueField.isAssociatedPoint_iff_exists_injective_residueField F x).mp hx
  exact ⟨φ ∘ₗ e.toLinearMap, hφ.comp e.injective⟩

/-- **`G_x = κ(x)` is a simple module.** The stalk at `x` of `i_{x,*} 𝒪_{W_x}` is the residue
field of the local ring `𝒪_{U,x}`, which is a simple module over it. -/
theorem isSimpleModule_stalk_pointClosureStructureSheaf {U : Scheme.{u}} (x : U) :
    IsSimpleModule (U.presheaf.stalk x)
      ((pointClosureStructureSheaf x).presheaf.stalk x) := by
  obtain ⟨e⟩ := nonempty_stalkLinearEquiv_residueField_pointClosureStructureSheaf x
  exact e.isSimpleModule_iff.mpr (isSimpleModule_iff_quot_maximal.mpr
    ⟨_, IsLocalRing.maximalIdeal.isMaximal _, ⟨LinearEquiv.refl _ _⟩⟩)

/-- **The spreading step of [Stacks, Tag 0BJZ]**, for a coherent `G` with simple stalk at `x`.
Let `F` be an `𝒪_U`-module and `x` a point associated to `F`. Then there are an open
neighbourhood `V` of `x`, a morphism `θ : G|_V ⟶ F|_V` and an injective `𝒪_{U,x}`-linear map `ψ`
of stalks at `x` which `θ` induces on germs.

This is the source's "by Cohomology of Schemes, Lemma 01Y4 there is an open `x ∈ V ⊂ U` and a map
`φ_V : 𝒢|_V → ℱ|_V` whose stalk at `x` is `φ_x`", with `φ_x` the injection of
`exists_injective_stalkLinearMap_of_isSimpleModule`. Tag 01Y4 applies because a coherent module
is of finite presentation. -/
theorem exists_hom_over_germ_eq_of_isSimpleModule {U : Scheme.{u}} (G F : U.Modules)
    [G.IsCoherent] (x : U) (hG : IsSimpleModule (U.presheaf.stalk x) (G.presheaf.stalk x))
    (hx : Stacks.Divisors.IsAssociatedPoint F x) :
    ∃ (V : U.Opens) (_ : x ∈ V) (θ : G.over V ⟶ F.over V)
      (ψ : TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x
            →ₗ[U.presheaf.stalk x] TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x),
      Function.Injective ψ ∧
        ∀ (V' : U.Opens) (hV' : V' ≤ V) (hxV' : x ∈ V') (g : Γ(G, V')),
          TopCat.Presheaf.germ (C := Ab.{u}) F.val.presheaf V' x hxV' (overApp θ hV' g)
            = ψ (TopCat.Presheaf.germ (C := Ab.{u}) G.val.presheaf V' x hxV' g) := by
  have : G.IsFinitePresentation := CoherentTFAE.isFinitePresentation_of_isCoherent' _
  obtain ⟨ψ, hψ⟩ := exists_injective_stalkLinearMap_of_isSimpleModule G F x hG hx
  obtain ⟨V, hxV, θ, hθ⟩ := Stacks.SheafOfModules.SheafHomStalk.exists_localHom_of_stalkLinearMap
    U.toTopCat U.sheaf G F x ψ
  exact ⟨V, hxV, θ, ψ, hψ, hθ⟩

/-- **Injectivity on stalks of a morphism that is an injection twisted by a unit near `x`.** Let
`φ : G ⟶ F`, let `f` be a global function with `x ∈ D(f)`, and suppose that on every open
`V ⊆ D(f)` containing `x` the germ of `φ` is an injective stalk map `ψ` applied to multiplication
by `f^k`. Then `φ` is injective on the stalk at `x`, since `f^k` is a unit there. -/
private theorem injective_stalk_of_germ_app_eq_smul_pow {U : Scheme.{u}} {G F : U.Modules}
    (φ : G ⟶ F) (f : Γ(U, ⊤)) (k : ℕ) {x : U} (hxf : x ∈ U.basicOpen f)
    (ψ : TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x
      →ₗ[U.presheaf.stalk x] TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)
    (hψ : Function.Injective ψ)
    (h : ∀ (V : U.Opens) (_ : V ≤ U.basicOpen f) (hxV : x ∈ V) (g : Γ(G, V)),
      TopCat.Presheaf.germ (C := Ab.{u}) F.val.presheaf V x hxV (φ.app V g)
        = ψ (U.presheaf.germ V x hxV (restrictTop f V) ^ k •
          TopCat.Presheaf.germ (C := Ab.{u}) G.val.presheaf V x hxV g)) :
    Function.Injective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf U.ringCatSheaf.obj).map φ.val)).hom := by
  rw [injective_iff_map_eq_zero]
  intro m hm
  obtain ⟨W, hxW, g, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := Ab.{u}) G.val.presheaf m
  have hxV : x ∈ W ⊓ U.basicOpen f := ⟨hxW, hxf⟩
  have step1 : TopCat.Presheaf.germ (C := Ab.{u})
        G.val.presheaf (W ⊓ U.basicOpen f) x hxV
        (G.val.presheaf.map (homOfLE (inf_le_left : W ⊓ U.basicOpen f ≤ W)).op g)
      = TopCat.Presheaf.germ (C := Ab.{u}) G.val.presheaf W x hxW g :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  rw [← step1] at hm ⊢
  have hu : IsUnit (U.presheaf.germ (W ⊓ U.basicOpen f) x hxV
      (restrictTop f (W ⊓ U.basicOpen f))) := by
    rw [restrictTop, TopCat.Presheaf.germ_res_apply]
    exact (U.mem_basicOpen_top f x).mp hxf
  set g' := G.val.presheaf.map (homOfLE (inf_le_left : W ⊓ U.basicOpen f ≤ W)).op g
  have hchain : ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf U.ringCatSheaf.obj).map φ.val)).hom
        (TopCat.Presheaf.germ (C := Ab.{u}) G.val.presheaf (W ⊓ U.basicOpen f) x hxV g')
      = ψ (U.presheaf.germ (W ⊓ U.basicOpen f) x hxV (restrictTop f (W ⊓ U.basicOpen f)) ^ k •
        TopCat.Presheaf.germ (C := Ab.{u}) G.val.presheaf (W ⊓ U.basicOpen f) x hxV g') :=
    (TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ _ _ _).trans
      (h (W ⊓ U.basicOpen f) inf_le_right hxV g')
  show TopCat.Presheaf.germ (C := Ab.{u}) G.val.presheaf (W ⊓ U.basicOpen f) x hxV g' = 0
  exact (hu.pow k).smul_eq_zero.mp (hψ ((hchain.symm.trans hm).trans (map_zero ψ).symm))

/-- **The comparison morphism of [Stacks, Tag 0BJZ]**, for a coherent `G` with simple stalk at
`x` and no associated point other than `x`. Let `U` be a Noetherian quasi-affine scheme, `F` a
quasi-coherent `𝒪_U`-module and `x` a point associated to `F`. Then there is a monomorphism
`G ⟶ F` of `𝒪_U`-modules.

The morphism on a neighbourhood of `x` supplied by
`exists_hom_over_germ_eq_of_isSimpleModule` is restricted to a principal open `D(f) ∋ x`
inside that neighbourhood — such an `f` exists because `U` is quasi-affine — and extended over
`U` by [Stacks, Tag 01YB] in the form
`Stacks.AlgebraicGeometry.PrincipalIdealExtension.exists_hom_app_eq_overApp_smul_pow_basicOpen`.
The extension computes on germs at `x` as the composite of multiplication by `f^k`, which is
invertible on the stalk because `f` does not vanish at `x`, with the injective stalk map, so it
is injective on the stalk at `x`; at every other point the hypothesis `Ass(G) ⊆ {x}` applies, so
[Stacks, Tag 0AVL] makes it a monomorphism. -/
theorem exists_mono_of_isSimpleModule {U : Scheme.{u}} [AlgebraicGeometry.IsNoetherian U]
    [U.IsQuasiAffine] (G F : U.Modules) [G.IsCoherent] [F.IsQuasicoherent] (x : U)
    (hG : IsSimpleModule (U.presheaf.stalk x) (G.presheaf.stalk x))
    (hGass : Stacks.Divisors.associatedPoints G ⊆ {x})
    (hx : Stacks.Divisors.IsAssociatedPoint F x) :
    ∃ φ : G ⟶ F, Mono φ := by
  have : G.IsQuasicoherent := (CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent G).1
  obtain ⟨V, hxV, θ, ψ, hψ, hθ⟩ := exists_hom_over_germ_eq_of_isSimpleModule G F x hG hx
  obtain ⟨_, ⟨f, _, rfl⟩, hxf, hfV⟩ := Opens.isBasis_iff_nbhd.mp
    (Scheme.IsQuasiAffine.isBasis_basicOpen U) hxV
  obtain ⟨k, φ, hφ⟩ := exists_hom_app_eq_overApp_smul_pow_basicOpen f G F (overRestrict hfV θ)
  refine ⟨φ, Stacks.Divisors.mono_of_stalk_injective_on_associatedPoints φ fun y => ?_⟩
  rcases eq_or_ne x y with rfl | hy
  · refine Or.inl (injective_stalk_of_germ_app_eq_smul_pow φ f k hxf ψ hψ fun V hV hxV g => ?_)
    refine Eq.trans (congrArg (fun s : Γ(F, V) =>
      TopCat.Presheaf.germ (C := Ab.{u}) F.val.presheaf V x hxV s)
      ((hφ hV _).trans (overApp_overRestrict hfV θ hV _))) ?_
    refine Eq.trans (hθ V (hV.trans hfV) hxV _) ?_
    refine congrArg ψ (Eq.trans (Stacks.ModuleStalkSpecialization.germ_smul
      G hxV (restrictTop f V ^ k) _) ?_)
    rw [map_pow]
    rfl
  · exact Or.inr fun hmem => hy (hGass hmem).symm

/-- **The comparison morphism of [Stacks, Tag 0BJZ].** Let `U` be a Noetherian quasi-affine
scheme, `F` a quasi-coherent `𝒪_U`-module and `x` a point associated to `F`. Then there is a
monomorphism `i_{x,*} 𝒪_{W_x} ⟶ F` of `𝒪_U`-modules.

This is `exists_mono_of_isSimpleModule` at `G = i_{x,*} 𝒪_{W_x}`: that module is coherent, its
stalk at `x` is the residue field `κ(x)` and hence simple, and `x` is its only associated point
by `AlgebraicGeometry.associatedPoints_pointClosureStructureSheaf_subset`. -/
theorem exists_mono_of_isAssociatedPoint {U : Scheme.{u}} [AlgebraicGeometry.IsNoetherian U]
    [U.IsQuasiAffine] (F : U.Modules) [F.IsQuasicoherent] (x : U)
    (hx : Stacks.Divisors.IsAssociatedPoint F x) :
    ∃ φ : pointClosureStructureSheaf x ⟶ F, Mono φ := by
  have := isCoherent_pointClosureStructureSheaf x
  exact exists_mono_of_isSimpleModule _ F x (isSimpleModule_stalk_pointClosureStructureSheaf x)
    (associatedPoints_pointClosureStructureSheaf_subset x) hx

/-- **[Stacks, Tag 0BJZ], (2) ⇒ (1) at an associated point, over a Noetherian quasi-affine open.**
Let `j : U ⟶ X` be an open immersion with `X` locally Noetherian, `U` Noetherian and quasi-affine,
let `F` be a quasi-coherent `𝒪_U`-module and let `x` be a point associated to `F`. If `j_* F` is
coherent then so is `j_* i_{x,*} 𝒪_{W_x}`.

This is `AlgebraicGeometry.isCoherent_pushforward_pointClosure_of_mono` with its monomorphism
hypothesis discharged by `exists_mono_of_isAssociatedPoint`. It is not the source's clause, which
puts no condition on `U` beyond being open in `X`; see the module documentation. -/
theorem isCoherent_pushforward_pointClosure_of_isAssociatedPoint {U X : Scheme.{u}}
    [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j] [AlgebraicGeometry.IsNoetherian U]
    [U.IsQuasiAffine] (x : U) (F : U.Modules) [F.IsQuasicoherent]
    (hx : Stacks.Divisors.IsAssociatedPoint F x)
    (hF : ((Scheme.Modules.pushforward j).obj F).IsCoherent) :
    ((Scheme.Modules.pushforward j).obj (pointClosureStructureSheaf x)).IsCoherent := by
  obtain ⟨φ, _⟩ := exists_mono_of_isAssociatedPoint F x hx
  exact isCoherent_pushforward_pointClosure_of_mono j x φ hF

end Stacks.AlgebraicGeometry.PointClosureComparison

end
