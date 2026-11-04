module

public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.ProjectiveSections05ID
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.AlgebraTranslationAt
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.AlgebraicFlatness
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.Existence
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.ShrinkingOverBase

/-!
# A complete dévissage of the global sections after elementary étale neighbourhoods

Let `f : X ⟶ S` be locally of finite type and let `F` be a quasi-coherent `𝒪_X`-module of finite
type. For every point `x` of `X` there are elementary étale neighbourhoods `(X', x')` of `(X, x)`
and `(S', s')` of `(S, f x)`, both **affine**, and a morphism `X' ⟶ S'` over `f` matching the
distinguished points, such that the `Γ(S', 𝒪_{S'})`-module `Γ(X', g^*F)` admits a complete
dévissage in the sense of Stacks 05HZ at the prime of `Γ(X', 𝒪_{X'})` belonging to `x'`.

This is Proposition 05HR followed by Remark 05I0. Proposition 05HR produces the square together
with a complete dévissage of `g^*F/X'/S'` at `x'` in the geometric sense of Stacks 05HI; the
schemes of a one-step dévissage are affine, so the square 05HR produces is already affine as soon
as that dévissage has a stage, and otherwise `g^*F` is zero and any pair of affine opens around
the two distinguished points serves. Remark 05I0 reads the geometric dévissage off as a dévissage
of the ring datum `Γ(X', g^*F)/Γ(X', 𝒪_{X'})/Γ(S', 𝒪_{S'})`.

Together with Lemma 05IB this is the dévissage half of the route to Tag 05ID, whose remaining
input is injectivity of the maps `α i` of the dévissage. Over a local base that injectivity is a
consequence of flatness (`Module.CompleteDevissage.injective_alpha_of_flat`); over a general base
it follows from Lemma 05IA after inverting an element outside the prime, which replaces `S'` by a
standard open neighbourhood of `s'`. Tag 05ID itself is
`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_projective_sections_of_isFlatOverAt` in
`StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.ProjectiveSectionsFlatAtPoint`.

## Main results

* `AlgebraicGeometry.exists_affine_elementaryEtaleNeighborhood_completeDevissageAt_globalSections`:
  the affine square of elementary étale neighbourhoods carrying a complete dévissage of the
  global sections at the prime belonging to the distinguished point of the upper neighbourhood.
* `Module.NonemptyCompleteDevissageAt.projective_of_injective_alpha`: a module with a complete
  dévissage at a prime whose maps `α i` are injective is projective over the base.

## Implementation notes

The conclusion is stated for the rings of global sections `Γ(S', 𝒪_{S'})`, `Γ(X', 𝒪_{X'})` and
`Γ(X', g^*F)`, as Remark 05I0 is, with the algebra structure induced by the vertical morphism and
the finiteness conditions a dévissage presupposes bound as `let`s in the statement.

The prime is named outright, as the image of the distinguished point of `X'` under
`AlgebraicGeometry.Scheme.isoSpec`, rather than existentially quantified: what Lemma 05IB does
with the dévissage depends on which prime it sits at.

## References

* [Stacks Project, Tag 05HR](https://stacks.math.columbia.edu/tag/05HR)
* [Stacks Project, Tag 05HZ](https://stacks.math.columbia.edu/tag/05HZ)
* [Stacks Project, Tag 05I0](https://stacks.math.columbia.edu/tag/05I0)
* [Stacks Project, Tag 05IB](https://stacks.math.columbia.edu/tag/05IB)
* [Stacks Project, Tag 05ID](https://stacks.math.columbia.edu/tag/05ID)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u v w

namespace AlgebraicGeometry

/-- Restricting an elementary étale neighbourhood to an open subscheme through a point above the
distinguished point leaves the extension of residue fields trivial. -/
theorem isIso_residueFieldMap_opens_comp {S : Scheme.{u}} {s : S} (U : EtaleNeighborhood S s)
    (hU : U.IsElementary) (W : U.scheme.Opens) (p : W.toScheme) (hp : W.ι p = U.point) :
    IsIso ((W.ι ≫ U.toBase).residueFieldMap p) := by
  rw [Scheme.residueFieldMap_comp]
  exact IsIso.comp_isIso' ((U.toBase.isIso_residueFieldMap_congr hp).mpr
    ((U.isElementary_iff).mp hU)) inferInstance

/-- **Stacks Project, Tag 05HR followed by Remark 05I0.** A quasi-coherent module of finite type
on a scheme locally of finite type over `S` acquires, at any chosen point, a complete dévissage
of its global sections over the global sections of the base after affine elementary étale
neighbourhoods of that point and of its image.

The dévissage sits at the prime of `Γ(X', 𝒪_{X'})` belonging to the distinguished point of the
upper neighbourhood, namely the image of that point under `Scheme.isoSpec`. -/
theorem exists_affine_elementaryEtaleNeighborhood_completeDevissageAt_globalSections
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (x : X) :
    ∃ (V : EtaleNeighborhood S (f x)) (U : EtaleNeighborhood X x) (h : U.scheme ⟶ V.scheme)
      (_ : V.IsElementary) (_ : U.IsElementary)
      (_ : h ≫ V.toBase = U.toBase ≫ f) (_ : h U.point = V.point)
      (hUaff : IsAffine U.scheme) (_ : IsAffine V.scheme)
      (hft : LocallyOfFiniteType h)
      (_ : ((Scheme.Modules.pullback U.toBase).obj F).IsQuasicoherent)
      (_ : ((Scheme.Modules.pullback U.toBase).obj F).IsFiniteType),
      letI := hUaff
      letI : Algebra Γ(V.scheme, ⊤) Γ(U.scheme, ⊤) := h.appTop.hom.toAlgebra
      letI : Algebra.FiniteType Γ(V.scheme, ⊤) Γ(U.scheme, ⊤) :=
        HasRingHomProperty.appTop (P := @LocallyOfFiniteType) h hft
      letI : Module.Finite Γ(U.scheme, ⊤)
          Γ((Scheme.Modules.pullback U.toBase).obj F, ⊤) :=
        Stacks.AlgebraicGeometry.CoherentFinite.finite_sections _ (isAffineOpen_top U.scheme)
      letI := (U.scheme.isoSpec.hom U.point).isPrime
      Nonempty (Module.CompleteDevissageAt Γ(V.scheme, ⊤) Γ(U.scheme, ⊤)
        Γ((Scheme.Modules.pullback U.toBase).obj F, ⊤)
        (U.scheme.isoSpec.hom U.point).asIdeal) := by
  obtain ⟨U, V, h, hU, hV, hsq, hpt, hft, hq, hfin, ⟨D⟩⟩ :=
    hasEtaleNeighborhoodCompleteDevissageAt f F x
  have : LocallyOfFiniteType h := hft
  have : ((Scheme.Modules.pullback U.toBase).obj F).IsQuasicoherent := hq
  have : ((Scheme.Modules.pullback U.toBase).obj F).IsFiniteType := hfin
  cases D with
  | empty hz =>
    obtain ⟨W', hW'aff, hW'mem, -⟩ :=
      exists_isAffineOpen_mem_and_subset (X := V.scheme) (x := V.point) (U := ⊤) (by simp)
    have hmem : U.point ∈ h ⁻¹ᵁ W' := by
      show h U.point ∈ W'
      rw [hpt]; exact hW'mem
    obtain ⟨W, hWaff, hWmem, hWsub⟩ :=
      exists_isAffineOpen_mem_and_subset (X := U.scheme) (x := U.point) hmem
    have hWle : W ≤ h ⁻¹ᵁ W' := hWsub
    have hι : h.resLE W' W hWle ≫ W'.ι = W.ι ≫ h := Scheme.Hom.resLE_comp_ι h hWle
    have hz₁ : IsZero ((Scheme.Modules.pullback (W.ι ≫ U.toBase)).obj F) :=
      IsZero.of_iso ((Scheme.Modules.pullback W.ι).map_isZero hz)
        ((Scheme.Modules.pullbackComp W.ι U.toBase).app F).symm
    have hq₁ : ((Scheme.Modules.pullback (W.ι ≫ U.toBase)).obj F).IsQuasicoherent :=
      inferInstance
    have hf₁ : ((Scheme.Modules.pullback (W.ι ≫ U.toBase)).obj F).IsFiniteType :=
      SheafOfModules.pullback_isFiniteType (W.ι ≫ U.toBase).toLRSHom.toShHom F
    have : IsAffine W.toScheme := hWaff
    have : IsAffine W'.toScheme := hW'aff
    have hft₁ : LocallyOfFiniteType (h.resLE W' W hWle) := inferInstance
    refine ⟨{ scheme := W'.toScheme
              point := ⟨V.point, hW'mem⟩
              toBase := W'.ι ≫ V.toBase
              map_point := V.map_point },
      { scheme := W.toScheme
        point := ⟨U.point, hWmem⟩
        toBase := W.ι ≫ U.toBase
        map_point := U.map_point }, h.resLE W' W hWle,
      ?_, ?_, ?_, ?_, hWaff, hW'aff, hft₁, hq₁, hf₁, ?_⟩
    · rw [EtaleNeighborhood.isElementary_iff]
      exact isIso_residueFieldMap_opens_comp V hV W' ⟨V.point, hW'mem⟩ rfl
    · rw [EtaleNeighborhood.isElementary_iff]
      exact isIso_residueFieldMap_opens_comp U hU W ⟨U.point, hWmem⟩ rfl
    · show h.resLE W' W hWle ≫ W'.ι ≫ V.toBase = (W.ι ≫ U.toBase) ≫ f
      rw [← Category.assoc, hι, Category.assoc, Category.assoc, ← hsq]
    · refine Subtype.ext ?_
      show (h.resLE W' W hWle (⟨U.point, hWmem⟩ : W.toScheme)).1 = V.point
      rw [Scheme.Hom.coe_resLE_apply]
      exact hpt
    · exact Module.nonempty_completeDevissageAt_of_completeDevissageAt _
        (W.toScheme.isoSpec.hom ⟨U.point, hWmem⟩).isPrime rfl (.empty hz₁)
  | nonempty data =>
    have hUaff : IsAffine U.scheme :=
      isAffine_source_of_devissageChain data.toNonemptyCompleteDevissage.chain
    have hVaff : IsAffine V.scheme :=
      isAffine_of_devissageChain data.toNonemptyCompleteDevissage.chain
    refine ⟨V, U, h, hV, hU, hsq.symm, hpt, hUaff, hVaff, hft, hq, hfin, ?_⟩
    exact Module.nonempty_completeDevissageAt_of_completeDevissageAt _
      (U.scheme.isoSpec.hom U.point).isPrime rfl (.nonempty data)

end AlgebraicGeometry

namespace Module.NonemptyCompleteDevissageAt

/-- **Stacks Project, Tag 05IB, the projectivity conclusion at a prime**, with injectivity of the
maps `alpha i` as a hypothesis. A module with a complete dévissage at a prime whose maps
`alpha i` are injective is projective over the base, the dévissage exhibiting it as a direct sum
of finite free modules over the smooth stage algebras. -/
public theorem projective_of_injective_alpha {R : Type u} {S : Type v} {N : Type w} [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.FiniteType R S] [AddCommGroup N] [Module S N]
    [Module.Finite S N] {q : Ideal S} [q.IsPrime] [Module R N] [IsScalarTower R S N]
    (E : Module.NonemptyCompleteDevissageAt R S N q)
    (hinj : ∀ i, letI : Module (E.toCompleteDevissage.B i) (E.toCompleteDevissage.M i) :=
        Module.compHom (E.toCompleteDevissage.M i) (E.toCompleteDevissage.toLeft i).toRingHom
      Function.Injective (E.toCompleteDevissage.alpha i)) :
    Module.Projective R N :=
  E.toCompleteDevissage.projective_of_injective_alpha hinj

end Module.NonemptyCompleteDevissageAt

end
