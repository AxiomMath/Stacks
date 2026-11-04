module

public import StacksFrontier.AlgebraicGeometry.DerivedPushforward.IsoTransport
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.CoherentModuleAffineTransport
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.FirstLocalCohomologyFiniteness
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.TildeStalkPrime
public import StacksFrontier.RingTheory.LocalCohomology.FinitenessImmediateSpecialization
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyWithSupportComparison
public import StacksFrontier.Topology.Dimension.DimensionFunctionObstruction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Coherence of a direct image along an open immersion from Faltings' criterion

Let `g : W ⟶ T` be an open immersion of schemes with `T` isomorphic to the spectrum of a
Noetherian ring `A` carrying a dualizing complex, and let `ℱ` be a coherent `𝒪_W`-module whose
stalk at `x` has depth at least one as soon as some point outside the image of `g` is an
*immediate* specialization of `g(x)`.  Then `g_* ℱ` is coherent.

This is the route the proof of [Stacks, Tag 0EI3] takes, and the point of it is the hypotheses it
does **not** need: no universal catenarity, and no Serre condition on the formal fibres of the
local rings of `T`.  Those are the hypotheses of Kollár's criterion [Stacks, Tag 0AWB], which
tests coherence through the *completions* of the local rings of the reduced closures of the
associated points; Faltings' finiteness criterion [Stacks, Tag 0EFD] tests it through the
dualizing complex instead and asks for nothing else.

## Main definitions

* `Stacks.AlgebraicGeometry.FaltingsPushforward.pushforwardTransportObjIso` — the direct image
  along `g` carried to the direct image along `g'` by a commuting square of isomorphisms of the
  source and the target.

## Main results

* `…FaltingsPushforward.isCoherent_pushforward_of_transport` — coherence of a direct image
  descends along that square.
* `…FaltingsPushforward.isCoherent_pushforward_of_depth_immediate_spec` — the criterion at an
  open of `Spec A`.
* `…FaltingsPushforward.isCoherent_pushforward_of_depth_immediate_isoSpec` — **the criterion
  along an open immersion into a scheme identified with `Spec A`.**

## Implementation notes

The chain over `Spec A` is the source's, read backwards:

* a coherent module on an open `W ⊆ Spec A` is `M̃|_W` for a finite `A`-module `M`, and `W` is the
  complement of a vanishing locus `V(I)`
  (`AlgebraicGeometry.exists_ideal_eq_finiteModule_tilde_restrict_iso`, which is part (1) of
  [Stacks, Tag 0BK0]);
* coherence of the direct image of `M̃|_W` is finiteness of `H¹_{V(I)}(M)`
  (`Stacks.LocalCohomology.finite_localCohomologyModule_one_iff_isCoherent_pushforward`, the
  degree-zero clause of [Stacks, Tag 0BK0]);
* that finiteness is Faltings' criterion at `s = 1`
  (`Stacks.LocalCohomology.finite_localCohomologyWithSupportIn_le_one_of_depth_immediate`),
  after the two models of local cohomology are identified by
  `Stacks.LocalCohomology.localCohomologyWithSupportInIsoLocalCohomologyModule`.

**The hypotheses have to be transported, not merely quoted.** The finite module `M` is produced by
the first step rather than chosen, so the depth bound — which the caller states at the points of
`W` and the stalks of `ℱ` — has to be read off `M` at the primes of `A`.  A prime `𝔭 ∉ V(I)` is a
point of `W`, and the three equalities
`AlgebraicGeometry.Scheme.Modules.depth_stalk_congr`,
`AlgebraicGeometry.Scheme.Modules.depth_stalk_restrict` and
`AlgebraicGeometry.depth_stalk_tilde_eq_depth_localizedModule` take the depth of `ℱ` there to the
depth of `M_𝔭`.  The immediate specializations need no translation at all: the carrier of the
scheme `Spec A` and the type `PrimeSpectrum A` carry the same topology, so
`TopologicalSpace.IsImmediateSpecialization` at a pair of primes *is* the relation at the
corresponding pair of points, and `Stacks.LocalCohomology.immediateSpec_iff_covby` — which reads
it as the covering relation of the inclusion order — is not needed.

The passage from `T` to `Spec A` is the one of
`AlgebraicGeometry.exists_ideal_finiteModule_isCoherent_rightDerived_iff_affine`: the given
isomorphism `b : T ≅ Spec A` on the target and `AlgebraicGeometry.Scheme.Hom.isoOpensRange` on the
source, whose square commutes by `AlgebraicGeometry.Scheme.Hom.isoOpensRange_hom_ι`.  The
isomorphism is taken as an argument rather than built as `AlgebraicGeometry.Scheme.isoSpec`,
because the ring a caller has a dualizing complex over is `Γ(X, V)` for an affine open `V` of an
ambient scheme and not `Γ(V.toScheme, ⊤)`, and those two rings are isomorphic but not equal;
`AlgebraicGeometry.IsAffineOpen.isoSpec` names the first.

Coherence crosses the square by `pushforwardTransportObjIso`, which is
`Stacks.AlgebraicGeometry.DerivedPushforward.rightDerivedTransportIso` with no derived functor
in it: for the undirected direct image the three isomorphisms
`AlgebraicGeometry.Scheme.Modules.pushforwardComp` and
`AlgebraicGeometry.Scheme.Modules.pushforwardCongr` compose to the comparison directly, with no
exactness or preservation of injectives to check.  The depth bound crosses it by
`AlgebraicGeometry.Scheme.Modules.depth_stalk_pushforward_eq`, and the immediate specializations
by `TopologicalSpace.IsImmediateSpecialization.map_of_isOpenEmbedding` at the homeomorphism
underlying `b`.

## References

* [Stacks Project, Tag 0EFD](https://stacks.math.columbia.edu/tag/0EFD)
* [Stacks Project, Tag 0EI3](https://stacks.math.columbia.edu/tag/0EI3)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0AWB](https://stacks.math.columbia.edu/tag/0AWB)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace IsLocalRing
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.CoherentDevissage (isCoherent_of_iso)
open Stacks.AlgebraicGeometry.DerivedPushforward (pushforwardInvPushforwardObjIso)
open Stacks.AlgebraicGeometry.FiniteDirectImageCoherent (isCoherent_pushforward_of_isFinite)

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.FaltingsPushforward

/-! ### The direct image across a square of isomorphisms -/

variable {W T W' T' : Scheme.{u}}

/-- **The direct image transported along isomorphisms of source and target.** For a commuting
square `a.hom ≫ g' = g ≫ b.hom` with `a : W ≅ W'` and `b : T ≅ T'` isomorphisms, pushing `g_* ℱ`
forward along `b` is `g'_*` of the push forward of `ℱ` along `a`.

Both sides are compared to `(g ≫ b.hom)_* = (a.hom ≫ g')_*`, by
`AlgebraicGeometry.Scheme.Modules.pushforwardComp` on each leg and
`AlgebraicGeometry.Scheme.Modules.pushforwardCongr` on the square.  The derived analogue is
`Stacks.AlgebraicGeometry.DerivedPushforward.rightDerivedTransportObjIso`, which needs in
addition that each leg be exact and preserve injective objects; here there is nothing to
check. -/
public def pushforwardTransportObjIso (g : W ⟶ T) (g' : W' ⟶ T') (a : W ≅ W') (b : T ≅ T')
    (h : a.hom ≫ g' = g ≫ b.hom) (F : W.Modules) :
    (Scheme.Modules.pushforward b.hom).obj ((Scheme.Modules.pushforward g).obj F) ≅
      (Scheme.Modules.pushforward g').obj ((Scheme.Modules.pushforward a.hom).obj F) :=
  (Scheme.Modules.pushforwardComp g b.hom).app F ≪≫
    (Scheme.Modules.pushforwardCongr h.symm).app F ≪≫
    ((Scheme.Modules.pushforwardComp a.hom g').app F).symm

/-- **Coherence of a direct image descends along the transport.** If `g'_* (a_* ℱ)` is coherent
then so is `g_* ℱ`, the target `T` being locally Noetherian.

Push the hypothesis forward along `b.inv`, which is an isomorphism and hence a finite morphism, so
[Stacks, Tag 01Y6] keeps it coherent; `pushforwardTransportObjIso` identifies the result with
`g_* ℱ`. -/
public theorem isCoherent_pushforward_of_transport (g : W ⟶ T) (g' : W' ⟶ T') (a : W ≅ W')
    (b : T ≅ T') (h : a.hom ≫ g' = g ≫ b.hom) (F : W.Modules) [IsLocallyNoetherian T]
    (hF : ((Scheme.Modules.pushforward g').obj
      ((Scheme.Modules.pushforward a.hom).obj F)).IsCoherent) :
    ((Scheme.Modules.pushforward g).obj F).IsCoherent := by
  have := hF
  have h1 : ((Scheme.Modules.pushforward b.inv).obj ((Scheme.Modules.pushforward g').obj
      ((Scheme.Modules.pushforward a.hom).obj F))).IsCoherent :=
    isCoherent_pushforward_of_isFinite b.inv _
  have := h1
  exact isCoherent_of_iso
    ((pushforwardInvPushforwardObjIso b ((Scheme.Modules.pushforward g).obj F)).symm ≪≫
      (Scheme.Modules.pushforward b.inv).mapIso (pushforwardTransportObjIso g g' a b h F))

/-! ### Faltings' criterion at an open of a spectrum -/

/-- **The direct image of a coherent module from an open of `Spec A` is coherent as soon as the
depth bound holds at the immediate specializations.** Let `A` be a Noetherian ring with a
dualizing complex, let `V ⊆ Spec A` be open and let `G` be a coherent `𝒪_V`-module whose stalk at
`x` has depth at least one whenever some point outside `V` is an immediate specialization of `x`.
Then the direct image of `G` along the inclusion of `V` is coherent.

This is Faltings' criterion [Stacks, Tag 0EFD] at `s = 1`, in the form
`Stacks.LocalCohomology.finite_localCohomologyWithSupportIn_le_one_of_depth_immediate`, fed
through the two clauses of [Stacks, Tag 0BK0] that describe `G` and the coherence of its direct
image: `AlgebraicGeometry.exists_ideal_eq_finiteModule_tilde_restrict_iso` writes `G` as `M̃|_V`
for a finite module `M` with `V = Spec A ∖ V(I)`, and
`Stacks.LocalCohomology.finite_localCohomologyModule_one_iff_isCoherent_pushforward` turns the
coherence of the direct image into finiteness of `H¹_{V(I)}(M)`.  The depth bound is read off `M`
at the primes outside `V(I)` as described in this module's documentation. -/
@[sga "2 VIII 2.1" "special case"]
public theorem isCoherent_pushforward_of_depth_immediate_spec {A : CommRingCat.{u}}
    [IsNoetherianRing A] (omega : DerivedCategory (ModuleCat.{u} A))
    (homega : Dualizing.IsDualizingComplex omega) (V : (Spec A).Opens)
    (G : V.toScheme.Modules) [G.IsCoherent]
    (hdepth : ∀ (x : V.toScheme) (z : Spec A), z ∉ V →
      IsImmediateSpecialization (V.ι.base x) z →
      (1 : ℕ∞) ≤ Module.depth (V.toScheme.presheaf.stalk x)
        (maximalIdeal (V.toScheme.presheaf.stalk x)) (G.presheaf.stalk x)) :
    ((Scheme.Modules.pushforward V.ι).obj G).IsCoherent := by
  obtain ⟨I, hIV, M, hMfin, ⟨e⟩⟩ := exists_ideal_eq_finiteModule_tilde_restrict_iso V G
  subst hIV
  have := hMfin
  have hdepth' : ∀ p q : PrimeSpectrum (ToType A),
      p ∉ PrimeSpectrum.zeroLocus (I : Set (ToType A)) →
      q ∈ PrimeSpectrum.zeroLocus (I : Set (ToType A)) → IsImmediateSpecialization p q →
      (1 : ℕ∞) ≤ Module.depth (Localization.AtPrime p.asIdeal)
        (maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl (ToType M)) := by
    intro p q hp hq hpq
    have hx : (p : Spec A) ∈ zeroLocusCompl I := hp
    have key := hdepth ⟨(p : Spec A), hx⟩ (q : Spec A) (not_not.mpr hq) hpq
    rw [← Scheme.Modules.depth_stalk_congr e ⟨(p : Spec A), hx⟩,
      Scheme.Modules.depth_stalk_restrict (zeroLocusCompl I).ι (tilde M) ⟨(p : Spec A), hx⟩,
      depth_stalk_tilde_eq_depth_localizedModule M
        ((zeroLocusCompl I).ι.base ⟨(p : Spec A), hx⟩) p rfl] at key
    exact key
  have hfin := Stacks.LocalCohomology.finite_localCohomologyWithSupportIn_le_one_of_depth_immediate
    (ToType A) (PrimeSpectrum.zeroLocus (I : Set (ToType A)))
    (PrimeSpectrum.isClosed_zeroLocus _).stableUnderSpecialization (ToType M) omega homega
    hdepth' 1 le_rfl
  have hfin2 : Module.Finite (ToType A)
      (Stacks.LocalCohomology.localCohomologyModule (ToType A) I I.fg_of_isNoetherianRing M 1) :=
    Module.Finite.equiv
      (Stacks.LocalCohomology.localCohomologyWithSupportInIsoLocalCohomologyModule (ToType A) I
        I.fg_of_isNoetherianRing M 1).toLinearEquiv
  have hcoh := (Stacks.LocalCohomology.finite_localCohomologyModule_one_iff_isCoherent_pushforward
    (ToType A) I M).mp hfin2
  have : ((Scheme.Modules.pushforward (zeroLocusCompl I).ι).obj
      ((tilde M).restrict (zeroLocusCompl I).ι)).IsCoherent := hcoh
  exact isCoherent_of_iso ((Scheme.Modules.pushforward (zeroLocusCompl I).ι).mapIso e.symm)

/-! ### Faltings' criterion along an open immersion into an affine scheme -/

/-- The base map of an isomorphism of schemes is surjective. -/
private theorem exists_base_eq_of_iso {X Y : Scheme.{u}} (e : X ≅ Y) (y : Y) :
    ∃ x, e.hom.base x = y :=
  ⟨e.inv.base y, (Scheme.homeoOfIso e).apply_symm_apply y⟩

/-- **The direct image of a coherent module along an open immersion into a scheme identified with
`Spec A` is coherent as soon as the depth bound holds at the immediate specializations.** Let `A`
be a Noetherian ring with a dualizing complex, let `b : T ≅ Spec A`, let `g : W ⟶ T` be an open
immersion and let `ℱ` be a coherent `𝒪_W`-module whose stalk at `x` has depth at least one
whenever some point outside the image of `g` is an immediate specialization of `g(x)`.  Then
`g_* ℱ` is coherent.

The target is moved to `Spec A` by `b` and the source to the range of `g ≫ b.hom` by
`AlgebraicGeometry.Scheme.Hom.isoOpensRange`; the square commutes by
`AlgebraicGeometry.Scheme.Hom.isoOpensRange_hom_ι`, the coherence crosses it by
`isCoherent_pushforward_of_transport` and the depth bound by
`AlgebraicGeometry.Scheme.Modules.depth_stalk_pushforward_eq`, after which
`isCoherent_pushforward_of_depth_immediate_spec` applies.  The transported module is coherent
because an isomorphism is a finite morphism, so [Stacks, Tag 01Y6] applies to it. -/
public theorem isCoherent_pushforward_of_depth_immediate_isoSpec {A : CommRingCat.{u}}
    [IsNoetherianRing A] [IsLocallyNoetherian T] (g : W ⟶ T) [IsOpenImmersion g]
    (b : T ≅ Spec A) (omega : DerivedCategory (ModuleCat.{u} A))
    (homega : Dualizing.IsDualizingComplex omega) (F : W.Modules) [F.IsCoherent]
    (hdepth : ∀ (x : W) (z : T), z ∉ Set.range g.base →
      IsImmediateSpecialization (g.base x) z →
      (1 : ℕ∞) ≤ Module.depth (W.presheaf.stalk x) (maximalIdeal (W.presheaf.stalk x))
        (F.presheaf.stalk x)) :
    ((Scheme.Modules.pushforward g).obj F).IsCoherent := by
  have hsq : (Scheme.Hom.isoOpensRange (g ≫ b.hom)).hom ≫
      (Scheme.Hom.opensRange (g ≫ b.hom)).ι = g ≫ b.hom :=
    Scheme.Hom.isoOpensRange_hom_ι (g ≫ b.hom)
  refine isCoherent_pushforward_of_transport g (Scheme.Hom.opensRange (g ≫ b.hom)).ι
    (Scheme.Hom.isoOpensRange (g ≫ b.hom)) b hsq F ?_
  have hGcoh : ((Scheme.Modules.pushforward
      (Scheme.Hom.isoOpensRange (g ≫ b.hom)).hom).obj F).IsCoherent :=
    isCoherent_pushforward_of_isFinite (Scheme.Hom.isoOpensRange (g ≫ b.hom)).hom F
  have := hGcoh
  refine isCoherent_pushforward_of_depth_immediate_spec omega homega
    (Scheme.Hom.opensRange (g ≫ b.hom)) _ ?_
  intro y z' hz' himm
  obtain ⟨x, rfl⟩ := exists_base_eq_of_iso (Scheme.Hom.isoOpensRange (g ≫ b.hom)) y
  obtain ⟨t, rfl⟩ := exists_base_eq_of_iso b z'
  rw [Scheme.Modules.depth_stalk_pushforward_eq (Scheme.Hom.isoOpensRange (g ≫ b.hom)) F x]
  have hbase : (Scheme.Hom.opensRange (g ≫ b.hom)).ι.base
      ((Scheme.Hom.isoOpensRange (g ≫ b.hom)).hom.base x) = b.hom.base (g.base x) :=
    congrArg (fun f : W ⟶ Spec A => f.base x) hsq
  have hinv : ∀ t : T, b.inv.base (b.hom.base t) = t := fun t => by simp
  refine hdepth x t ?_ ?_
  · rintro ⟨w, rfl⟩
    exact hz' ⟨w, rfl⟩
  · have hemb : Topology.IsOpenEmbedding b.inv.base :=
      (Scheme.homeoOfIso b.symm).isOpenEmbedding
    have hmap := himm.map_of_isOpenEmbedding hemb
    rwa [hbase, hinv, hinv] at hmap

end Stacks.AlgebraicGeometry.FaltingsPushforward

end
