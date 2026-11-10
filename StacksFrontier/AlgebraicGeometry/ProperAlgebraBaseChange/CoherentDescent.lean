module

public import StacksFrontier.AlgebraicGeometry.AffineQcohUnit.Equivalence
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.FinitePushforwardCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.ProperAlgebraBaseChange.GradedRealization

/-!
# The module `F'` on the base change

`StacksFrontier/AlgebraicGeometry/ProperAlgebraBaseChange/GradedRealization.lean` makes the ungraded
realisation `⨁ₙ Fₙ` of a graded `𝓑`-module a *quasi-coherent* sheaf of modules over the sheaf of
rings `π_* 𝒪_{X'}`, for `π : X' = X ×_{Spec A} Spec B ⟶ X` the projection. That is exactly the
target of [Stacks, Tag 01SB]'s equivalence, so the quasi-inverse of that equivalence produces a
quasi-coherent module `F'` on `X'` whose direct image is `⨁ₙ Fₙ`. This file does that.

`F'` is the module [Stacks, Tag 0897]'s proof descends `⨁ₙ Fₙ` to. Its *coherence* is reduced
here to one statement about modules of sections; see the implementation notes.

## Main definitions

* `Stacks.ProperAlgebraBaseChange.ungradedQcoh`: `⨁ₙ Fₙ` as an object of the category of
  quasi-coherent `π_* 𝒪_{X'}`-modules.
* `Stacks.ProperAlgebraBaseChange.descendedModule`: **`F'`, the quasi-coherent `𝒪_{X'}`-module
  with `π_* F' = ⨁ₙ Fₙ`.**

## Main results

* `Stacks.ProperAlgebraBaseChange.isQuasicoherent_descendedModule`: `F'` is quasi-coherent.
* `Stacks.ProperAlgebraBaseChange.pushforwardDescendedModuleIso`: **`π_* F' ≅ ⨁ₙ Fₙ`** as
  `π_* 𝒪_{X'}`-modules, which is the counit of [Stacks, Tag 01SB]'s equivalence.
* `Stacks.ProperAlgebraBaseChange.isCoherent_descendedModule`: **`F'` is coherent as soon as it
  is of finite type** — the locally Noetherian half of [Stacks, Tag 01XZ] is discharged, `X'`
  being locally Noetherian by `Stacks.ProperAlgebraBaseChange.isLocallyNoetherian_scheme`.
* `Stacks.ProperAlgebraBaseChange.isFiniteType_descendedModule_of_finite_sections` and
  `isCoherent_descendedModule_of_finite_sections`: **the whole of what [Stacks, Tag 0897]
  part (1) asks of `F'`, reduced to one statement about modules of sections**: that
  `Γ(F', π⁻¹(V))` is a finite `Γ(X', π⁻¹(V))`-module for every affine open `V` of `X`.
* `Stacks.ProperAlgebraBaseChange.finite_sections_descendedModule_of_finite_sections_realisation`
  and `isCoherent_descendedModule_of_finite_sections_realisation`: **the same reduced further, to
  a statement about the graded data alone** — that the sections of the ungraded realisation
  `⨁ₙ Fₙ` over each affine open `V` of `X` are a finite module over the sections of the ungraded
  realisation of `𝓑`.

## Implementation notes

**Nothing is constructed by hand.** `Stacks.ProperAlgebraBaseChange.isEquivalence_pushforward_proj`
is [Stacks, Tag 01SB] at `π`, so `CategoryTheory.Functor.inv` of the direct-image functor between
the two categories of quasi-coherent modules is `F'`, and the counit of
`CategoryTheory.Functor.asEquivalence` is the identification of its direct image with `⨁ₙ Fₙ`.
The two categories are full subcategories cut out by quasi-coherence, so the underlying module
and the quasi-coherence of `F'` are the two components of one object of such a subcategory, and
the isomorphism of modules is the image of the counit under `ObjectProperty.ι`.

**The sheaf of rings needs no transport.** [Stacks, Tag 01SB] is stated over
`Stacks.AlgebraicGeometry.AffineQcohPushforward.pushforwardRing`, while the realisation is a
module over `Stacks.RelativeSpec.AlgebraSheaf.ringSheaf` of the pushforward algebra; those are
*equal*, which is
`Stacks.ProperAlgebraBaseChange.ringSheaf_pushforwardAlgebra_eq`, so the anonymous constructor
below takes the realisation as an object of the right category with no comparison map.

**What coherence still needs.** [Stacks, Tag 0897] part (1) asks for a *coherent* `F'`. `F'` is
quasi-coherent here, so by [Stacks, Tag 01XZ]
(`Stacks.AlgebraicGeometry.CoherenceCriteria.coherent_tfae`) what is left is that `X'` is locally
Noetherian and that `F'` is of finite type.

The first is now proved, in the setting of the tag: `isLocallyNoetherian_scheme` in
`StacksFrontier/AlgebraicGeometry/ProperAlgebraBaseChange/Basic.lean` derives it from `A`
Noetherian,
`B` of finite type over `A` and `f` proper, by the Hilbert basis theorem and the fact that a
scheme locally of finite type over a locally Noetherian scheme is locally Noetherian, applied to
the *proper* `f' : X' ⟶ Spec B` rather than to the affine `π`. So `isCoherent_descendedModule`
below reduces coherence of `F'` to its finite type outright.

The second is reduced here to a statement about **modules of sections**:
`isFiniteType_descendedModule_of_finite_sections` says that `F'` is of finite type as soon as
`Γ(F', π⁻¹(V))` is a finite `Γ(X', π⁻¹(V))`-module for every affine open `V` of `X`. That is the
shape in which the graded module's own finiteness hypothesis `Stacks.Coherent.IsFiniteTypeOnAffine`
is available, since `Γ(F', π⁻¹(V))` is `Γ(π_* F', V)` and `pushforwardDescendedModuleIso`
identifies `π_* F'` with the ungraded realisation `⨁ₙ Fₙ`. What is **not** written is that
transport, and it is not a rewrite: `Stacks.Coherent.IsFiniteTypeOnAffine` gives finitely many
homogeneous generators of the *presheaf* direct sum `⨁ₙ Γ(V, Fₙ)`, and the realisation is its
sheafification, so what is missing is that the two have the same sections over the quasi-compact
`V` — the degree-zero case of [Stacks, Tag 01FF]'s direct-sum companion
(`Stacks.Cohomology.DirectSum.preservesColimitsOfShape_discrete_Hfunctor`), together with the
identification of the coproduct injections with `Stacks.RightGradedModule.incl` under
`SheafOfModules.GradedModule.coprodIsoUngradedSheafModule`.

## References

* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AffineAlgebraEquivalence
open Stacks.AlgebraicGeometry.AffineQcohEquivalence
open Stacks.AlgebraicGeometry.AffineQcohPushforward

universe u

namespace Stacks.ProperAlgebraBaseChange

open Stacks.RelativeSpec

variable {X : Scheme.{u}} (𝓑 : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
  (hc : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : (𝓑.piece i).val.obj W) (b : (𝓑.piece j).val.obj W),
    HEq ((𝓑.mul i j).app W a b) ((𝓑.mul j i).app W b a))
  (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (f : X ⟶ Spec (.of A))
  (F : SheafOfModules.GradedModule 𝓑)
  (e : gradedAlgebraSheaf X 𝓑 hc ≅ (algebraPullback f).obj (specAlgebraSheaf A B))
  (hqc : ∀ n : ℤ, (F.piece n).IsQuasicoherent)

/-- The ungraded realisation `⨁ₙ Fₙ`, as an object of the category of quasi-coherent modules
over the sheaf of rings `π_* 𝒪_{X'}`: the category [Stacks, Tag 01SB]'s equivalence lands in. -/
def ungradedQcoh :
    (SheafOfModules.isQuasicoherent
      (pushforwardRing (proj A B f).base (scheme A B f).ringCatSheaf)).FullSubcategory :=
  ⟨ungradedModuleOverPushforwardProj 𝓑 hc A B f F e,
    isQuasicoherent_ungradedModuleOverPushforwardProj_of_pieces 𝓑 hc A B f F e hqc⟩

/-- **`F'`: the quasi-coherent `𝒪_{X'}`-module whose direct image along `π` is `⨁ₙ Fₙ`.**

This is the image of `⨁ₙ Fₙ` under the quasi-inverse of [Stacks, Tag 01SB] at the affine
projection `π : X ×_{Spec A} Spec B ⟶ X`. -/
def descendedModule : (scheme A B f).Modules :=
  haveI := isEquivalence_pushforward_proj A B f
  ((affineQuasicoherentPushforward (proj A B f)).inv.obj
    (ungradedQcoh 𝓑 hc A B f F e hqc)).obj

/-- **`F'` is quasi-coherent**: it is an object of the full subcategory of quasi-coherent
modules. -/
theorem isQuasicoherent_descendedModule :
    (descendedModule 𝓑 hc A B f F e hqc).IsQuasicoherent :=
  have := isEquivalence_pushforward_proj A B f
  ((affineQuasicoherentPushforward (proj A B f)).inv.obj
    (ungradedQcoh 𝓑 hc A B f F e hqc)).property

/-- **`π_* F' ≅ ⨁ₙ Fₙ`** as modules over `π_* 𝒪_{X'}`: the counit of [Stacks, Tag 01SB]'s
equivalence at `⨁ₙ Fₙ`. -/
def pushforwardDescendedModuleIso :
    (pushforwardModules (proj A B f).base (scheme A B f).ringCatSheaf).obj
        (descendedModule 𝓑 hc A B f F e hqc) ≅
      ungradedModuleOverPushforwardProj 𝓑 hc A B f F e :=
  haveI := isEquivalence_pushforward_proj A B f
  (ObjectProperty.ι _).mapIso
    ((affineQuasicoherentPushforward (proj A B f)).asEquivalence.counitIso.app
      (ungradedQcoh 𝓑 hc A B f F e hqc))

/-! ### Coherence of `F'` -/

section Coherence

open Stacks.AlgebraicGeometry.CoherentFinite
open Stacks.AlgebraicGeometry.CoherentTFAE

/-- **The sections of `F'` over `π⁻¹(V)` are a finite module as soon as the sections of the
ungraded realisation `⨁ₙ Fₙ` over `V` are.**

`Γ(F', π⁻¹(V))` *is* `Γ(π_* F', V)` — the direct image of a sheaf of modules along a continuous
map is precomposition with `Opens.map`, so the two are the same module, not merely isomorphic —
and `pushforwardDescendedModuleIso` identifies `π_* F'` with the realisation, as modules over
`π_* 𝒪_{X'}`. The ring the realisation's sections are a module over is
`Γ(𝓑.ungradedSheaf, V)`, and `ungradedSheafIsoPushforwardProj` identifies it with
`Γ(X', π⁻¹(V))`; finiteness is carried across that ring isomorphism and the module isomorphism
together by `Module.Finite.of_surjective` for the semilinear map.

This is the step that turns coherence of `F'` into a statement about the *graded* data alone:
no scheme over `X` and no descent appears in the hypothesis. -/
theorem finite_sections_descendedModule_of_finite_sections_realisation (V : X.Opens)
    (hfin : Module.Finite (𝓑.ungradedSheaf.obj.obj (Opposite.op V))
      ((F.ungradedSheafModule hc).val.obj (Opposite.op V))) :
    Module.Finite Γ(scheme A B f, proj A B f ⁻¹ᵁ V)
      Γ(descendedModule 𝓑 hc A B f F e hqc, proj A B f ⁻¹ᵁ V) := by
  have := hfin
  set ρ := ungradedSheafIsoPushforwardProj 𝓑 hc A B f e with hρdef
  set E := pushforwardDescendedModuleIso 𝓑 hc A B f F e hqc with hEdef
  have hρ : ∀ t : 𝓑.ungradedSheaf.obj.obj (Opposite.op V),
      (ρ.hom.hom.app (Opposite.op V)).hom ((ρ.inv.hom.app (Opposite.op V)).hom t) = t :=
    fun t => congrArg (fun φ : _ ⟶ _ => (φ.hom.app (Opposite.op V)).hom t) ρ.inv_hom_id
  have hE : ∀ y, (E.inv.val.app (Opposite.op V)).hom
      ((E.hom.val.app (Opposite.op V)).hom y) = y :=
    fun y => congrArg (fun φ : _ ⟶ _ => (φ.val.app (Opposite.op V)).hom y) E.hom_inv_id
  exact Module.Finite.of_surjective
    (M := ((F.ungradedSheafModule hc).val.obj (Opposite.op V)))
    (σ := (ρ.inv.hom.app (Opposite.op V)).hom)
    { toFun := fun x => (E.inv.val.app (Opposite.op V)).hom x
      map_add' := fun x y => map_add (E.inv.val.app (Opposite.op V)).hom x y
      map_smul' := fun t x => by
        have h := (E.inv.val.app (Opposite.op V)).hom.map_smul
          ((ρ.inv.hom.app (Opposite.op V)).hom t) x
        refine Eq.trans (congrArg (E.inv.val.app (Opposite.op V)).hom ?_) h
        change (t • x : ((F.ungradedSheafModule hc).val.obj (Opposite.op V)))
          = (ρ.hom.hom.app (Opposite.op V)).hom
              ((ρ.inv.hom.app (Opposite.op V)).hom t) • x
        rw [hρ] }
    fun y => ⟨(E.hom.val.app (Opposite.op V)).hom y, hE y⟩

/-- **`F'` is of finite type as soon as its sections over the preimage of every affine open of
`X` are a finite module.**

The preimages `π⁻¹(V)` of the affine opens `V` of `X` are affine — `π` is affine
([Stacks, Tag 01LX] part (1) at the base change, here the instance
`Stacks.ProperAlgebraBaseChange.isAffineHom_proj`) — and they cover `X'`, so condition (5) of
[Stacks, Tag 01XZ] can be checked on them; over an affine open the sections being a finite module
is exactly that condition, by [Stacks, Tag 01PB]
(`Stacks.AlgebraicGeometry.CoherentFinite.specSectionsEquiv`).

This is the reduction of finite type of `F'` to a statement about *modules of sections*, which is
the shape in which the graded module's own finiteness hypothesis
`Stacks.Coherent.IsFiniteTypeOnAffine` is available: `Γ(F', π⁻¹(V))` is `Γ(π_* F', V)`, which
`pushforwardDescendedModuleIso` identifies with the sections of the ungraded realisation
`⨁ₙ Fₙ` over `V`. -/
theorem isFiniteType_descendedModule_of_finite_sections
    (hsec : ∀ V : X.affineOpens,
      Module.Finite Γ(scheme A B f, proj A B f ⁻¹ᵁ (V : X.Opens))
        Γ(descendedModule 𝓑 hc A B f F e hqc, proj A B f ⁻¹ᵁ (V : X.Opens))) :
    (descendedModule 𝓑 hc A B f F e hqc).IsFiniteType :=
  have := isQuasicoherent_descendedModule 𝓑 hc A B f F e hqc
  isFiniteType_of_cover_isFiniteTildeOn _
    (fun V : X.affineOpens => proj A B f ⁻¹ᵁ (V : X.Opens))
    (Stacks.AlgebraicGeometry.FinitePushforwardCoherent.isOpenCover_preimage_affineOpens
      (proj A B f))
    (fun V => V.2.preimage (proj A B f)) fun V =>
      have := hsec V
      isFiniteTildeOn_of_finite_specModule _ _ (V.2.preimage (proj A B f))
        (Module.Finite.equiv (specSectionsEquiv _ (V.2.preimage (proj A B f))).symm)

/-- **`F'` is coherent as soon as it is of finite type.**

`F'` is quasi-coherent (`isQuasicoherent_descendedModule`) and `X'` is locally Noetherian in the
setting of [Stacks, Tag 0897] — `A` Noetherian, `B` of finite type over `A`, `f` proper
(`Stacks.ProperAlgebraBaseChange.isLocallyNoetherian_scheme`) — so this is (2) ⇒ (1) of
[Stacks, Tag 01XZ]. It is the half of the coherence of `F'` that the tree now settles; the other
half is the finite type, for which see `isFiniteType_descendedModule_of_finite_sections`. -/
theorem isCoherent_descendedModule [IsNoetherianRing A] [Algebra.FiniteType A B] [IsProper f]
    (hft : (descendedModule 𝓑 hc A B f F e hqc).IsFiniteType) :
    (descendedModule 𝓑 hc A B f F e hqc).IsCoherent :=
  have := isQuasicoherent_descendedModule 𝓑 hc A B f F e hqc
  have := hft
  Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType _

/-- **`F'` is coherent as soon as its sections over the preimage of every affine open of `X` are
a finite module.** The two halves above combined: this is everything [Stacks, Tag 0897] part (1)
asks of `F'`, reduced to one statement about modules of sections. -/
theorem isCoherent_descendedModule_of_finite_sections [IsNoetherianRing A]
    [Algebra.FiniteType A B] [IsProper f]
    (hsec : ∀ V : X.affineOpens,
      Module.Finite Γ(scheme A B f, proj A B f ⁻¹ᵁ (V : X.Opens))
        Γ(descendedModule 𝓑 hc A B f F e hqc, proj A B f ⁻¹ᵁ (V : X.Opens))) :
    (descendedModule 𝓑 hc A B f F e hqc).IsCoherent :=
  isCoherent_descendedModule 𝓑 hc A B f F e hqc
    (isFiniteType_descendedModule_of_finite_sections 𝓑 hc A B f F e hqc hsec)

/-- **`F'` is coherent as soon as, over every affine open `V` of `X`, the sections of the ungraded
realisation `⨁ₙ Fₙ` are a finite module over the sections of the ungraded realisation of `𝓑`.**

This is everything [Stacks, Tag 0897] part (1) asks of `F'`, reduced to a hypothesis about the
graded data `𝓑` and `F` alone: neither `X'` nor the descent nor the identification
`𝓑 ≅ f^* B̃` appears in it. What remains to be proved, and is **not** proved here, is that the
graded module's own finiteness hypothesis `Stacks.Coherent.IsFiniteTypeOnAffine` implies it. The
one gap in that implication is the passage from the *presheaf* direct sum `⨁ₙ Γ(V, Fₙ)`, which
`Stacks.Coherent.IsFiniteTypeOnAffine` describes, to its sheafification, which is the
realisation: the graded generators generate the former over `⨁ₘ Γ(V, 𝓑ₘ)` by
`Stacks.RightGradedModule.act_incl_incl`, and the sheafification unit is semilinear over
`⨁ₘ Γ(V, 𝓑ₘ) ⟶ Γ(V, 𝓑.ungradedSheaf)` by construction, so what is missing is that the unit is
*surjective* on sections over the quasi-compact `V`. -/
theorem isCoherent_descendedModule_of_finite_sections_realisation [IsNoetherianRing A]
    [Algebra.FiniteType A B] [IsProper f]
    (hfin : ∀ V : X.affineOpens,
      Module.Finite (𝓑.ungradedSheaf.obj.obj (Opposite.op (V : X.Opens)))
        ((F.ungradedSheafModule hc).val.obj (Opposite.op (V : X.Opens)))) :
    (descendedModule 𝓑 hc A B f F e hqc).IsCoherent :=
  isCoherent_descendedModule_of_finite_sections 𝓑 hc A B f F e hqc fun V =>
    finite_sections_descendedModule_of_finite_sections_realisation 𝓑 hc A B f F e hqc
      (V : X.Opens) (hfin V)

end Coherence

end Stacks.ProperAlgebraBaseChange

end
