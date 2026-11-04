module

public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleSeparation
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.FiberRankIsomorphismInvariant
public import StacksFrontier.AlgebraicGeometry.Modules.ReducedFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Etale.FlatFiniteTypeModules
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.GenericFibreRankConstantBlowup
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.EtaleBase

/-!
# The generic-fibre rank over a distinguished open, for a module of finite type

Let `g : X ⟶ S` be flat, of finite presentation, with geometrically integral fibres, let `F` be a
quasi-coherent `𝒪_X`-module and let `U ⊆ S` be a quasi-compact open such that

* `F` is of **finite presentation on `g⁻¹(U)`** only, and
* `F` is flat over `S` at the generic point of the fibre over every point of `U`.

Then the two conclusions of
`AlgebraicGeometry.exists_finite_opens_constant_fiberRank` and
`AlgebraicGeometry.exists_admissibleBlowup_constant_fiberRank` still hold: `U` is the disjoint
union of finitely many quasi-compact opens on each of which the generic-fibre rank is constant,
and that decomposition is separated by a single `U`-admissible blowup of `S`.

This is the hypothesis under which [Stacks, Tag 0811] actually runs: there `F` is of finite type
on all of `X` and of finite presentation only over the distinguished open `U`, and the first
reduction of its proof — "thus we may assume `r` is constant" — uses finite presentation nowhere
outside `g⁻¹(U)`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.fiberRank_pullback_ι`: the fibre rank is unchanged by
  restriction along an open immersion.
* `AlgebraicGeometry.exists_finite_opens_constant_fiberRank_of_finitePresentation_preimage`: the
  decomposition `U = U_0 ⊔ … ⊔ U_c` by the value of the generic-fibre rank.
* `AlgebraicGeometry.exists_admissibleBlowup_constant_fiberRank_of_finitePresentation_preimage`:
  that decomposition separated by a single `U`-admissible blowup.

## Implementation notes

The proof is a restriction, not a repetition: the data `g`, `F`, `U` are replaced by their
restrictions to `U`, where finite presentation of the module *does* hold globally, and the
already-proved global statements are applied there. The restricted morphism is
`g ∣_ U : g⁻¹(U) ⟶ U`, the base change of `g` along the open immersion `U.ι`, so it inherits
flatness, finite presentation and geometric integrality, and `U` is quasi-compact and
quasi-separated as a scheme because it is a quasi-compact open of a quasi-separated space. The
restricted module is `(Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).obj F`, which is exactly the one the
finite-presentation hypothesis is about.

Three transports along the open immersions are needed, and are proved here:

* `Stacks.FiniteLocallyFree.Reduced.fiberRank_restrict`, the invariance of the fibre rank. The
  stalk of a restriction at a point is the stalk at its image, *semilinearly* over the induced
  isomorphism of local rings (`Scheme.Modules.restrictStalkNatIso`, whose scalar compatibility
  is a germ computation), and a semilinear equivalence of stalks base-changes to one of
  residue-field fibres, which have the same dimension.
* `AlgebraicGeometry.fibre_dense_morphismRestrict_iff`, that "generic point of the fibre" in the
  topological form `g⁻¹(g b) ⊆ closure {b}` transports both ways for points over `U`. The fibre
  of `g ∣_ U` is the trace of the fibre of `g` — a point of `X` over `U` lies in `g⁻¹(U)` — and
  the closure of a point of an open subspace is the trace of its closure.
* `AlgebraicGeometry.isFlatOverAt_morphismRestrict_iff`, that flatness over the base at a point
  is unchanged. It is `AlgebraicGeometry.isFlatOverAt_pullback_ι_iff` on the source composed
  with `AlgebraicGeometry.isFlatOverAt_comp_iff_of_etale` for the open immersion `U.ι` on the
  target, the two being joined by `AlgebraicGeometry.morphismRestrict_ι`.

The finitely many opens of `U` produced on the restriction are pushed forward to opens of `S` by
`U.ι ''ᵁ -`, which preserves suprema, carries `⊤` to `U`, and preserves disjointness and
quasi-compactness because `U.ι` is an injective continuous open map.

## References

* [Stacks Project, Tag 0811](https://stacks.math.columbia.edu/tag/0811)
* [Stacks Project, Tag 080P](https://stacks.math.columbia.edu/tag/080P)
* [Stacks Project, Tag 080Q](https://stacks.math.columbia.edu/tag/080Q)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.FiniteLocallyFree.Reduced
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- **The fibre rank is unchanged by pulling back to an open subscheme.** This is
`Stacks.FiniteLocallyFree.Reduced.fiberRank_restrict` for the inclusion of an open, in the
`Scheme.Modules.pullback` spelling of the restriction; the two spellings are identified by
`Scheme.Modules.restrictFunctorIsoPullback`, and the fibre rank is an isomorphism invariant. -/
theorem fiberRank_pullback_ι {X : Scheme.{u}} (U : X.Opens) (F : X.Modules) (x : U.toScheme) :
    ((Scheme.Modules.pullback U.ι).obj F).fiberRank x = F.fiberRank x.1 := by
  rw [← Scheme.Modules.fiberRank_eq_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app F) x]
  exact fiberRank_restrict U.ι F x

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- Two points of `g⁻¹(U)` have the same image under `g ∣_ U` iff they have the same image
under `g`. -/
private theorem morphismRestrict_base_eq_iff {X S : Scheme.{u}} (g : X ⟶ S) (U : S.Opens)
    (c d : (g ⁻¹ᵁ U).toScheme) :
    (g ∣_ U).base c = (g ∣_ U).base d ↔ g.base c.1 = g.base d.1 := by
  refine ⟨fun h => ?_, fun h => Subtype.ext ?_⟩
  · simpa only [morphismRestrict_base_coe] using congrArg Subtype.val h
  · simpa only [morphismRestrict_base_coe] using h

/-- **"Generic point of the fibre" transports both ways between a morphism and its restriction
over an open of the target.** A point of `X` lying over `U` lies in `g⁻¹(U)`, so the fibre of
`g ∣_ U` through `c` is the trace of the fibre of `g` through `c`; and the closure of `{c}` in
the open subspace `g⁻¹(U)` is the trace of the closure of `{c}` in `X`. -/
theorem fibre_dense_morphismRestrict_iff {X S : Scheme.{u}} (g : X ⟶ S) (U : S.Opens)
    (c : (g ⁻¹ᵁ U).toScheme) :
    ((g ∣_ U).base ⁻¹' {(g ∣_ U).base c} ⊆ closure {c}) ↔
      (g.base ⁻¹' {g.base c.1} ⊆ closure {c.1}) := by
  have hclosure : closure ({c} : Set (g ⁻¹ᵁ U).toScheme) =
      (g ⁻¹ᵁ U).ι.base ⁻¹' closure ({c.1} : Set X) := by
    rw [((g ⁻¹ᵁ U).ι.isOpenEmbedding).isInducing.closure_eq_preimage_closure_image,
      Set.image_singleton]
    rfl
  refine ⟨fun h x hx => ?_, fun h d hd => ?_⟩
  · have hxU : x ∈ g ⁻¹ᵁ U := show g.base x ∈ U from hx ▸ c.2
    rw [hclosure] at h
    exact h ((morphismRestrict_base_eq_iff g U ⟨x, hxU⟩ c).mpr hx)
  · rw [hclosure]
    exact h ((morphismRestrict_base_eq_iff g U d c).mp hd)

/-- **Flatness over the base at a point is unchanged by restricting over an open of the target.**
The composite `g⁻¹(U) ⟶ U ⟶ S` is `g⁻¹(U) ⟶ X ⟶ S`, so this is
`AlgebraicGeometry.isFlatOverAt_pullback_ι_iff` for the open immersion of the source followed by
`AlgebraicGeometry.isFlatOverAt_comp_iff_of_etale` for the open — hence étale — immersion `U.ι`
of the target. -/
theorem isFlatOverAt_morphismRestrict_iff {X S : Scheme.{u}} (g : X ⟶ S) (U : S.Opens)
    (F : X.Modules) [F.IsQuasicoherent] (c : (g ⁻¹ᵁ U).toScheme) :
    IsFlatOverAt (g ∣_ U).toLRSHom.toShHom ((Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).obj F) c ↔
      IsFlatOverAt g.toLRSHom.toShHom F c.1 := by
  have : ((Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).obj F).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback (g ⁻¹ᵁ U).ι F ‹_›
  have hcomp : IsFlatOverAt ((g ∣_ U) ≫ U.ι).toLRSHom.toShHom
      ((Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).obj F) c ↔
      IsFlatOverAt g.toLRSHom.toShHom F c.1 := by
    rw [morphismRestrict_ι]
    exact isFlatOverAt_pullback_ι_iff g (g ⁻¹ᵁ U) F c
  exact (isFlatOverAt_comp_iff_of_etale (g ∣_ U) U.ι
    ((Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).obj F) c).symm.trans hcomp

/-- **A point over `U` lies in the image of an open of `U` exactly when its restriction does.**
`U.ι` is injective, so the only point of `U` above `g(c)` is the image of `c` under `g ∣_ U`. -/
theorem mem_image_morphismRestrict_iff {X S : Scheme.{u}} (g : X ⟶ S) (U : S.Opens)
    (A : U.toScheme.Opens) (c : (g ⁻¹ᵁ U).toScheme) :
    g.base c.1 ∈ U.ι ''ᵁ A ↔ (g ∣_ U).base c ∈ A := by
  refine ⟨?_, fun h => ⟨(g ∣_ U).base c, h, morphismRestrict_base_coe g U c⟩⟩
  rintro ⟨w, hw, hwc⟩
  have hval : w = (g ∣_ U).base c :=
    Subtype.ext (hwc.trans (morphismRestrict_base_coe g U c).symm)
  exact hval ▸ hw

/-- **The decomposition of a distinguished open by the generic-fibre rank, for a module of
finite presentation only over that open.** Let `g : X ⟶ S` be flat, of finite presentation, with
geometrically integral fibres, let `F` be a quasi-coherent `𝒪_X`-module whose restriction to
`g⁻¹(U)` is of finite presentation, and let `U ⊆ S` be a quasi-compact open over which `F` is
flat over `S` at the generic point of every fibre. Then `U` is the supremum of a finite family
of pairwise disjoint quasi-compact opens `V i`, each carrying a rank `n i` such that every
generic point of a fibre over `V i` has fibre rank `n i`.

This is `AlgebraicGeometry.exists_finite_opens_constant_fiberRank` under the hypotheses that
[Stacks, Tag 0811] actually makes: finite presentation of `F` is used only over `U`. The proof
applies that theorem to the restricted data `g ∣_ U`, `F|_{g⁻¹(U)}` and the open `⊤` of `U`,
where the restricted module is of finite presentation by hypothesis, and pushes the resulting
opens of `U` forward along `U.ι`. -/
theorem exists_finite_opens_constant_fiberRank_of_finitePresentation_preimage
    {X S : Scheme.{u}} [QuasiSeparatedSpace S] (g : X ⟶ S)
    (hg : AlgebraicGeometry.FinitePresentation g) [Flat g] [GeometricallyIntegral g]
    (F : X.Modules) [F.IsQuasicoherent] (U : S.Opens) (hU : IsCompact (U : Set S))
    (hFU : ((Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).obj F).IsFinitePresentation)
    (hflat : ∀ b : X, g.base b ∈ U → g.base ⁻¹' {g.base b} ⊆ closure {b} →
      IsFlatOverAt g.toLRSHom.toShHom F b) :
    ∃ (ι : Type) (_ : Finite ι) (V : ι → S.Opens) (n : ι → ℕ),
      (Pairwise fun i j => Disjoint (V i) (V j)) ∧ (⨆ i, V i) = U ∧
        (∀ i, IsCompact (V i : Set S)) ∧
          ∀ i, ∀ b : X, g.base b ∈ V i → g.base ⁻¹' {g.base b} ⊆ closure {b} →
            F.fiberRank b = n i := by
  have : LocallyOfFinitePresentation g := hg.locallyOfFinitePresentation
  have : QuasiCompact g := hg.quasiCompact
  have : QuasiSeparated g := hg.quasiSeparated
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  have : QuasiSeparatedSpace U.toScheme :=
    QuasiSeparatedSpace.of_isOpenEmbedding U.ι.isOpenEmbedding
  have : ((Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).obj F).IsFinitePresentation := hFU
  obtain ⟨κ, hκ, W, n, hdisj, hsup, hcomp, hrank⟩ :=
    exists_finite_opens_constant_fiberRank (g ∣_ U)
      ⟨inferInstance, inferInstance, inferInstance⟩
      ((Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).obj F) ⊤
      (by simpa using isCompact_univ (X := U.toScheme))
      fun c _ hc => (isFlatOverAt_morphismRestrict_iff g U F c).mpr
        (hflat c.1 c.2 ((fibre_dense_morphismRestrict_iff g U c).mp hc))
  refine ⟨κ, hκ, fun i => U.ι ''ᵁ W i, n, fun i j hij => ?_, ?_, fun i => ?_, fun i b hb hbcl => ?_⟩
  · show Disjoint (U.ι ''ᵁ W i) (U.ι ''ᵁ W j)
    rw [← Opens.coe_disjoint]
    exact (Set.disjoint_image_iff U.ι.isOpenEmbedding.injective).mpr
      (Opens.coe_disjoint.mpr (hdisj hij))
  · rw [← Scheme.Hom.image_iSup, hsup, Scheme.Opens.ι_image_top]
  · exact (hcomp i).image U.ι.isOpenEmbedding.continuous
  · have hbU : b ∈ g ⁻¹ᵁ U :=
      show g.base b ∈ U from Scheme.Opens.ι_image_le U (W i) hb
    exact (Scheme.Modules.fiberRank_pullback_ι (g ⁻¹ᵁ U) F ⟨b, hbU⟩).symm.trans
      (hrank i ⟨b, hbU⟩ ((mem_image_morphismRestrict_iff g U (W i) ⟨b, hbU⟩).mp hb)
        ((fibre_dense_morphismRestrict_iff g U ⟨b, hbU⟩).mpr hbcl))

/-- **The generic-fibre rank may be assumed constant after a `U`-admissible blowup, for a module
of finite presentation only over `U`.** In the situation of
`AlgebraicGeometry.exists_finite_opens_constant_fiberRank_of_finitePresentation_preimage` there
is a `U`-admissible blowup `p : S' ⟶ S` whose source is the disjoint union of opens `W i` with
the inverse image of the `i`-th piece `V i` of `U` contained in `W i`.

This is `AlgebraicGeometry.exists_admissibleBlowup_constant_fiberRank` under the hypotheses of
[Stacks, Tag 0811], and is deduced from the decomposition exactly as that theorem is deduced
from its own predecessor: by
`Stacks.Blowup.exists_admissibleBlowup_pairwise_disjoint_open_cover`, the finite-family form of
[Stacks, Tag 080P]. -/
theorem exists_admissibleBlowup_constant_fiberRank_of_finitePresentation_preimage
    {X S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] (g : X ⟶ S)
    (hg : AlgebraicGeometry.FinitePresentation g) [Flat g] [GeometricallyIntegral g]
    (F : X.Modules) [F.IsQuasicoherent] (U : S.Opens) (hU : IsCompact (U : Set S))
    (hFU : ((Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).obj F).IsFinitePresentation)
    (hflat : ∀ b : X, g.base b ∈ U → g.base ⁻¹' {g.base b} ⊆ closure {b} →
      IsFlatOverAt g.toLRSHom.toShHom F b) :
    ∃ (ι : Type) (_ : Finite ι) (V : ι → S.Opens) (n : ι → ℕ),
      (⨆ i, V i) = U ∧
        (∀ i, ∀ b : X, g.base b ∈ V i → g.base ⁻¹' {g.base b} ⊆ closure {b} →
          F.fiberRank b = n i) ∧
          ∃ (S' : Scheme.{u}) (p : S' ⟶ S) (W : ι → S'.Opens),
            Stacks.Blowup.IsAdmissibleBlowup U p ∧
              (Pairwise fun i j => Disjoint (W i) (W j)) ∧ (⨆ i, W i) = ⊤ ∧
                ∀ i, p ⁻¹ᵁ V i ≤ W i := by
  obtain ⟨ι, hιfin, V, n, hdisj, hsup, hcomp, hrank⟩ :=
    exists_finite_opens_constant_fiberRank_of_finitePresentation_preimage g hg F U hU hFU hflat
  obtain ⟨S', p, W, hadm, hWdisj, hWsup, hWle⟩ :=
    Stacks.Blowup.exists_admissibleBlowup_pairwise_disjoint_open_cover S V hcomp hdisj
  exact ⟨ι, hιfin, V, n, hsup, hrank, S', p, W, hsup ▸ hadm, hWdisj, hWsup, hWle⟩

end AlgebraicGeometry

end
