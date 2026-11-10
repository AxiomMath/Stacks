module

public import StacksFrontier.AlgebraicGeometry.F6Rank89.ExtendRationalMap
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.DominateRationalMap
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupChainDominating
public import StacksCore.Tactic.StacksAttribute
import all
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.DominateRationalMap

/-!
# Dominating a rational map on a regular surface, with the inputs of Tag 0C5H discharged

`Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_resolving_partialMap` of
`ResolutionOfSurfaces/QuadraticTransformations/DominateRationalMap.lean` is [Stacks, Tag 0C5H]
granted three inputs: `descent`, the local splitting of [Stacks, Tag 0AGT]; `domination`,
[Stacks, Tag 0AHI]; and `reduction`, the enlargement of the domain of the rational map to a
cofinite open. On a regular Noetherian scheme of dimension two all three are available in this
development, and the resulting form of the tag is stated here.

## Main results

* `Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_resolving_partialMap_of_dim_two` —
  [Stacks, Tag 0C5H] for a regular Noetherian scheme of dimension two, with no granted inputs.

## Implementation notes

Enlarging the domain is the valuative extension of
[Stacks, Tag 0BX7](https://stacks.math.columbia.edu/tag/0BX7) across the codimension-one points
of the indeterminacy locus, which on a regular scheme have discrete valuation rings for local
rings; what is left has coheight two, hence is closed, and a closed subset of a Noetherian scheme
all of whose points are closed is a finite set of points. The chain dominating the modification
is `Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_factorization_of_isProper`, the library's
[Stacks, Tag 0AHI], which discharges `descent` and `domination` together.

The declaration in `DominateRationalMap.lean` keeps its three granted inputs: it is the form the
rest of the development was compiled against, and the statement below is an addition to it, not
a replacement. That file's two private glue lemmas, `pointBlowupChain_mono` and
`isIso_morphismRestrict_of_isIso_pullback_snd`, are reached through `import all` rather than
copied.

This file, and not `DominateRationalMap.lean`, is where
`PointBlowupChainDominating.lean` is imported: that module rests on
`PointBlowupDescent.lean`, which rests through `FactorizationBirationalMaps.lean` on
`DominateRationalMap.lean`, so importing it there would close an import cycle.

## References

* [Stacks Project, Tag 0C5H](https://stacks.math.columbia.edu/tag/0C5H)
* [Stacks Project, Tag 0AHI](https://stacks.math.columbia.edu/tag/0AHI)
* [Stacks Project, Tag 0BX7](https://stacks.math.columbia.edu/tag/0BX7)
* [Stacks Project, Tag 0C4V](https://stacks.math.columbia.edu/tag/0C4V)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace Stacks.ResolutionOfSurfaces

/-- A closed subset of a Noetherian scheme all of whose points are closed is finite: each of its
finitely many irreducible components is the closure of its generic point, hence a singleton. -/
private theorem finite_of_forall_isClosed_singleton {X : Scheme.{u}}
    [AlgebraicGeometry.IsNoetherian X] {C : Set X} (hC : IsClosed C)
    (hpt : ∀ x ∈ C, IsClosed ({x} : Set X)) : C.Finite := by
  obtain ⟨T, hTfin, hTclosed, hTirr, hTC⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hC
  rw [hTC] at hpt ⊢
  refine hTfin.sUnion fun D hD => ?_
  have hgen : IsGenericPoint (hTirr D hD).genericPoint D :=
    (hTirr D hD).isGenericPoint_genericPoint (hTclosed D hD)
  have hDeq : D = {(hTirr D hD).genericPoint} :=
    hgen.def.symm.trans (hpt _ (Set.mem_sUnion.mpr ⟨D, hD, hgen.mem⟩)).closure_eq
  exact (Set.finite_singleton _).subset hDeq.subset

/-- On a regular Noetherian scheme of dimension two over `S`, a partial map over `S` into a
scheme proper over `S` extends to a domain whose complement is a finite set of closed points
whose local rings have Krull dimension two. -/
@[ega "II 7.3.6" "special case"]
private theorem exists_extension_finite_compl {S X Y : Scheme.{u}} [X.Over S] [Y.Over S]
    [AlgebraicGeometry.IsNoetherian X] [IsProper (Y ↘ S)]
    (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    (hdim : topologicalKrullDim X = 2) (f : X.PartialMap Y) [f.IsOver S] :
    ∃ (g : X.PartialMap Y) (hfg : f.domain ≤ g.domain),
      g.hom ≫ (Y ↘ S) = g.domain.ι ≫ (X ↘ S) ∧
      X.homOfLE hfg ≫ g.hom = f.hom ∧
      ((g.domain : Set X)ᶜ).Finite ∧
      (∀ x : X, x ∉ (g.domain : Set X) → IsClosed ({x} : Set X)) ∧
      (∀ x : X, x ∉ (g.domain : Set X) → ringKrullDim (X.presheaf.stalk x) = 2) := by
  classical
  have hfbase : f.hom ≫ (Y ↘ S) = f.domain.ι ≫ (X ↘ S) :=
    Scheme.PartialMap.isOver_iff.mp ‹f.IsOver S›
  have hCclosed : IsClosed ((f.domain : Set X)ᶜ) := f.domain.2.isClosed_compl
  obtain ⟨T, hTfin, hTclosed, hTirr, hTC⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hCclosed
  let _ : Finite {D : Set X // D ∈ T} := hTfin.to_subtype
  let η : {D : Set X // D ∈ T} → X := fun D => (hTirr D.1 D.2).genericPoint
  have hFfinite : {x : X | x ∈ Set.range η ∧ ringKrullDim (X.presheaf.stalk x) = 1}.Finite :=
    (Set.finite_range η).subset fun _ hx => hx.1
  obtain ⟨f₁, hff₁, hf₁base, hfrestrict, hFdomain⟩ :=
    AlgebraicGeometry.Scheme.PartialMap.exists_extension_of_finset_ringKrullDim_eq_one f hfbase
      hreg hFfinite.toFinset fun _ hx => (hFfinite.mem_toFinset.mp hx).2
  -- Every point left out of the enlarged domain has coheight two.
  have hco2 : ∀ x : X, x ∉ (f₁.domain : Set X) → Order.coheight x = 2 := by
    intro x hxC₁
    have hxC : x ∈ (f.domain : Set X)ᶜ := fun hxU => hxC₁ (hff₁ hxU)
    rw [hTC] at hxC
    obtain ⟨D, hDT, hxD⟩ := Set.mem_sUnion.mp hxC
    have hyD : IsGenericPoint (η ⟨D, hDT⟩) D :=
      (hTirr D hDT).isGenericPoint_genericPoint (hTclosed D hDT)
    have hyU : η ⟨D, hDT⟩ ∈ (f.domain : Set X)ᶜ := by
      rw [hTC]
      exact Set.mem_sUnion.mpr ⟨D, hDT, hyD.mem⟩
    rcases coheight_eq_one_or_two_of_notMem_dense hdim.le f.dense_domain hyU with h1 | h2
    · have hyF : η ⟨D, hDT⟩ ∈ hFfinite.toFinset := hFfinite.mem_toFinset.mpr
        ⟨⟨⟨D, hDT⟩, rfl⟩, by rw [ringKrullDim_stalk_eq_coheight, h1]; rfl⟩
      have hxy : x ≤ η ⟨D, hDT⟩ := Scheme.le_iff_specializes.mpr (hyD.specializes hxD)
      have hne : x ≠ η ⟨D, hDT⟩ := fun heq => hxC₁ (heq ▸ hFdomain _ hyF)
      have hyx : ¬ η ⟨D, hDT⟩ ≤ x := fun hyx => hne (inseparable_iff_specializes_and.mpr
        ⟨Scheme.le_iff_specializes.mp hxy, Scheme.le_iff_specializes.mp hyx⟩).eq.symm
      refine le_antisymm
        (WithBot.coe_le_coe.mp ((coheight_le_topologicalKrullDim x).trans hdim.le)) ?_
      calc
        (2 : ℕ∞) = Order.coheight (η ⟨D, hDT⟩) + 1 := by rw [h1]; norm_num
        _ ≤ Order.coheight x := Order.coheight_add_one_le (lt_of_le_not_ge hxy hyx)
    · rw [eq_genericPoint_of_coheight_two hdim.le hyD h2 hxD]
      exact h2
  have hptclosed : ∀ x : X, x ∉ (f₁.domain : Set X) → IsClosed ({x} : Set X) :=
    fun x hx => isClosed_singleton_of_coheight_two hdim.le (hco2 x hx)
  refine ⟨f₁, hff₁, hf₁base, hfrestrict,
    finite_of_forall_isClosed_singleton f₁.domain.2.isClosed_compl hptclosed, hptclosed,
    fun x hx => ?_⟩
  rw [ringKrullDim_stalk_eq_coheight, hco2 x hx]
  norm_num

/-- **Stacks Project, Tag 0C5H.** Let `S` be a scheme, let `X` be a regular Noetherian scheme
over `S` of dimension two, and let `Y` be proper over `S`. Given an `S`-rational map from `X` to
`Y`, displayed on the dense open `f.domain`, there is a chain of blowups at closed points not
lying over `f.domain`, with composite `p : Z ⟶ X`, and an `S`-morphism `h : Z ⟶ Y` which agrees
with the rational map over `f.domain`. -/
@[stacks 0C5H]
public theorem exists_pointBlowupChain_resolving_partialMap_of_dim_two
    {S X Y : Scheme.{u}} [X.Over S] [Y.Over S] [AlgebraicGeometry.IsNoetherian X]
    [IsProper (Y ↘ S)] (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    (hdim : topologicalKrullDim X = 2) (f : X.PartialMap Y) [f.IsOver S] :
    ∃ (Z : Scheme.{u}) (p : Z ⟶ X) (h : Z ⟶ Y),
      PointBlowupChain X ((f.domain : Set X)ᶜ) Z p ∧
        h ≫ (Y ↘ S) = p ≫ (X ↘ S) ∧
          pullback.fst p f.domain.ι ≫ h = pullback.snd p f.domain.ι ≫ f.hom := by
  classical
  obtain ⟨f₁, hle, hgS, hgf, hfin, hTclosed, hTdim⟩ :=
    exists_extension_finite_compl (S := S) hreg hdim f
  have : f₁.IsOver S := ⟨hgS⟩
  -- The complement of the enlarged domain, as a finite set of closed points.
  have hVT : (f₁.domain : Set X) = (hfin.toFinset : Set X)ᶜ := by
    rw [Set.Finite.coe_toFinset, compl_compl]
  have hTclosed' : ∀ x ∈ hfin.toFinset, IsClosed ({x} : Set X) :=
    fun x hx => hTclosed x (hfin.mem_toFinset.mp hx)
  have hTdim' : ∀ x ∈ hfin.toFinset, ringKrullDim (X.presheaf.stalk x) = 2 :=
    fun x hx => hTdim x (hfin.mem_toFinset.mp hx)
  -- The graph modification of the rational map displayed on the enlarged domain.
  obtain ⟨X', p, f₂, hpproper, hf₂S, hpiso, hpagree⟩ :=
    Stacks.Divisors.exists_proper_modification_resolving_partialMap (S := S) f₁
  have hpiso' : IsIso (pullback.snd p f₁.domain.ι) := hpiso
  have hpagree' : pullback.fst p f₁.domain.ι ≫ f₂ = pullback.snd p f₁.domain.ι ≫ f₁.hom :=
    hpagree
  have : IsProper p := hpproper
  have : IsIso (p ∣_ f₁.domain) :=
    isIso_morphismRestrict_of_isIso_pullback_snd p f₁.domain hpiso'
  obtain ⟨Z, r, hchain, s, hs⟩ :=
    exists_pointBlowupChain_factorization_of_isProper hfin.toFinset f₁.domain hVT hTclosed'
      (fun x _ => hreg x) hTdim' p
  -- The centres lie outside the enlarged domain, hence outside the original one.
  have hsub : (hfin.toFinset : Set X) ⊆ (f.domain : Set X)ᶜ :=
    fun x hx hxU => hfin.mem_toFinset.mp hx (hle hxU)
  refine ⟨Z, r, s ≫ f₂, pointBlowupChain_mono hsub hchain, ?_, ?_⟩
  · rw [Category.assoc, hf₂S, ← Category.assoc, hs]
  · -- Compare the two morphisms out of `Z ×_X f.domain` through `X' ×_X f₁.domain`.
    have hcond : (pullback.fst r f.domain.ι ≫ s) ≫ p =
        (pullback.snd r f.domain.ι ≫ X.homOfLE hle) ≫ f₁.domain.ι := by
      rw [Category.assoc, hs, pullback.condition, Category.assoc, Scheme.homOfLE_ι]
    let m : pullback r f.domain.ι ⟶ pullback p f₁.domain.ι :=
      pullback.lift (pullback.fst r f.domain.ι ≫ s)
        (pullback.snd r f.domain.ι ≫ X.homOfLE hle) hcond
    have hmfst : m ≫ pullback.fst p f₁.domain.ι = pullback.fst r f.domain.ι ≫ s :=
      pullback.lift_fst _ _ _
    have hmsnd : m ≫ pullback.snd p f₁.domain.ι =
        pullback.snd r f.domain.ι ≫ X.homOfLE hle :=
      pullback.lift_snd _ _ _
    calc pullback.fst r f.domain.ι ≫ s ≫ f₂
        = (m ≫ pullback.fst p f₁.domain.ι) ≫ f₂ := by rw [hmfst, Category.assoc]
      _ = (m ≫ pullback.snd p f₁.domain.ι) ≫ f₁.hom := by
            rw [Category.assoc, Category.assoc, hpagree']
      _ = pullback.snd r f.domain.ι ≫ X.homOfLE hle ≫ f₁.hom := by
            rw [hmsnd, Category.assoc]
      _ = pullback.snd r f.domain.ι ≫ f.hom := by rw [hgf]

end Stacks.ResolutionOfSurfaces

end
