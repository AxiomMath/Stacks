module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalProperty
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigFlat
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.LocallySurjectiveTransfer

/-!
# Covering criteria for rig-flat morphisms of formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
formal algebraic spaces over `S`. Stacks 0GGY lists four equivalent conditions on `f`:

1. `f` is rig-flat;
2. for every commutative square whose verticals are affine charts of `X` and `Y` that are
   representable by algebraic spaces and étale, the top morphism comes from a rig-flat map of
   adic Noetherian topological rings;
3. there is a covering `{Yⱼ ⟶ Y}` as in Definition 0AIM and, for each `j`, a covering
   `{Xⱼᵢ ⟶ Yⱼ ×_Y X}` as in Definition 0AIM, such that each `Xⱼᵢ ⟶ Yⱼ` comes from a rig-flat
   map of adic Noetherian topological rings;
4. there is a covering `{Xᵢ ⟶ X}` as in Definition 0AIM together with factorizations
   `Xᵢ ⟶ Yᵢ ⟶ Y` in which each `Yᵢ` is an affine formal algebraic space, each `Yᵢ ⟶ Y` is
   representable by algebraic spaces and étale, and each `Xᵢ ⟶ Yᵢ` comes from a rig-flat map
   of adic Noetherian topological rings.

Conditions (1) and (2) are the same condition: clause (2) is verbatim the definition of
rig-flatness, `AlgebraicGeometry.FormalSpace.IsRigFlat` (Stacks 0GGX). This file proves the
implication **(3) ⟹ (4)**, which is the one step of Stacks 0GGY that is a construction rather
than a descent: the two given coverings are composed into a single covering of `X`, and the
charts of the target covering are the factoring affine formal algebraic spaces.

## Main definitions

* `AlgebraicGeometry.FormalSpace.IsRigFlatOnCharts`: a morphism of affine formal algebraic
  spaces comes from a rig-flat map of adic Noetherian topological rings. This is the tail of
  `AlgebraicGeometry.FormalSpace.IsRigFlat`, read on a single chart morphism.
* `AlgebraicGeometry.FormalSpace.HasRigFlatTargetCovering` and
  `AlgebraicGeometry.FormalSpace.HasRigFlatSourceCovering`: conditions (3) and (4).

The morphisms and the coverings appearing in Definition 0AIM are not defined here. They are
`AlgebraicGeometry.FormalSpace.IsRepresentableEtale` and
`AlgebraicGeometry.FormalSpace.IsAffineEtaleCover` of
`StacksFrontier/AlgebraicGeometry/FormalSpace/LocalProperty.lean`, which is where the general
form of Stacks 0ANG lives; this file uses them as they stand.

## Main results

* `AlgebraicGeometry.FormalSpace.hasRigFlatSourceCovering_of_hasRigFlatTargetCovering`:
  **Stacks 0GGY, (3) ⟹ (4)**.

## Implementation notes

The covering of `X` witnessing condition (4) is the family `{Xⱼᵢ ⟶ Yⱼ ×_Y X ⟶ X}` indexed by
the sigma type of the two index types of condition (3). Three things have to be checked of it.
Its members are affine and its charts are rig-flat by hypothesis. Its maps to `X` are
representable by algebraic spaces and étale because `Yⱼ ×_Y X ⟶ X` is a base change of
`Yⱼ ⟶ Y` and because those two properties are stable under composition; both stabilities are
`AlgebraicGeometry.FormalSpace.IsRepresentableEtale.comp` and
`AlgebraicGeometry.FormalSpace.isRepresentableEtale_pullback_snd` of
`StacksFrontier/AlgebraicGeometry/FormalSpace/LocalProperty.lean`, which rest in turn on the
base-change and descent statements for the relative étale property in
`StacksFrontier/AlgebraicGeometry/FormalSpace/EtaleCover.lean`. It is jointly surjective because
the family `{Yⱼ ×_Y X ⟶ X}` is, being a base change of the jointly surjective family
`{Yⱼ ⟶ Y}`, and because the family `{Xⱼᵢ ⟶ Yⱼ ×_Y X}` is for each `j`; the first of these is
`CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_pullback_snd`.

The factorization required by condition (4) is `Xⱼᵢ ⟶ Yⱼ ×_Y X ⟶ Yⱼ ⟶ Y`, and the square it
has to fit into is the defining square of the fibre product, so no further input is needed.

### The reverse implications

The implications (4) ⟹ (1) and (3) ⟹ (1) are not proved here, and nothing in this file carries
their part of the tag. Stacks 0GGY obtains them from rig-flatness being a local property of
arrows of `WAdm^Noeth` (Stacks 0GGU, which this library has as
`Rig.rigFlat_isLocalNoetherian`) together with the étale-local transfer lemma for
chart-defined properties of morphisms of formal algebraic spaces — Formal Spaces Lemma 87.21.3
(Stacks 0ANG) in its Noetherian variant (Stacks 0ANI). That transfer lemma is absent from this
library, as the module documentation of
`StacksFrontier.AlgebraicGeometry.FormalSpace.RigFlatComposition` also records: it is what
produces a chart of an intermediate space, by refining the given coverings, cutting down to a
finite subfamily using quasi-compactness, and descending the property along the resulting
faithfully flat étale maps. Only the ring-level half of the input is available.

## References

* [Stacks Project, Tag 0GGY](https://stacks.math.columbia.edu/tag/0GGY)
* [Stacks Project, Tag 0GGX](https://stacks.math.columbia.edu/tag/0GGX)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Rig-flatness on charts and the two covering conditions

The morphisms and the coverings of Definition 0AIM are `IsRepresentableEtale` and
`IsAffineEtaleCover` of `StacksFrontier/AlgebraicGeometry/FormalSpace/LocalProperty.lean`. -/

/-- A morphism of fppf sheaves *comes from a rig-flat map of adic Noetherian topological
rings*: for every presentation of its source and target as formal spectra of adic Noetherian
topological rings over `S`, every continuous homomorphism realizing the morphism is rig-flat
in the sense of Stacks 0GGP. This is the tail of
`AlgebraicGeometry.FormalSpace.IsRigFlat` read on a single chart morphism, so clause (2) of
Stacks 0GGY says exactly that every chart morphism of `f` satisfies it. -/
abbrev IsRigFlatOnCharts {U V : FppfSheaf B S hS} (t : U ⟶ V) : Prop :=
  ∀ (A C : Type u)
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
      [IsNoetherianRing A]
    [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
      [IsNoetherianRing C],
    TopologicalRing.IsAdic A → TopologicalRing.IsAdic C →
    ∀ (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
      (E : QuotientSystem B S hS C) (eU : U ≅ formalSpectrum E)
      (eV : V ≅ formalSpectrum D) (g : ContinuousHom D E),
      t = eU.hom ≫ formalSpectrumMap hA g ≫ eV.inv →
        Rig.RingHom.IsRigFlat g.toRingHom

/-- **Condition (3) of Stacks 0GGY.** There is a covering of the target as in Definition 0AIM
and, over each of its members, a covering of the corresponding fibre product as in Definition
0AIM, such that every resulting morphism of charts comes from a rig-flat map of adic
Noetherian topological rings. -/
abbrev HasRigFlatTargetCovering {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∃ (J : Type (u + 1)) (V : J → FppfSheaf B S hS) (v : ∀ j, V j ⟶ Y),
    IsAffineEtaleCover B S hS V v ∧
      ∀ j, ∃ (I : Type (u + 1)) (U : I → FppfSheaf B S hS)
        (w : ∀ i, U i ⟶ pullback (v j) f),
        IsAffineEtaleCover B S hS U w ∧
          ∀ i, IsRigFlatOnCharts B S hS (w i ≫ pullback.fst (v j) f)

/-- **Condition (4) of Stacks 0GGY.** There is a covering of the source as in Definition 0AIM
each of whose members maps to the target through an affine formal algebraic space that is
representable étale over it, by a morphism coming from a rig-flat map of adic Noetherian
topological rings. -/
abbrev HasRigFlatSourceCovering {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∃ (I : Type (u + 1)) (U : I → FppfSheaf B S hS) (a : ∀ i, U i ⟶ X),
    IsAffineEtaleCover B S hS U a ∧
      ∀ i, ∃ (V : FppfSheaf B S hS) (b : V ⟶ Y) (t : U i ⟶ V),
        IsAffineFormalAlgebraicSpace B S hS V ∧ IsRepresentableEtale B S hS b ∧
          a i ≫ f = t ≫ b ∧ IsRigFlatOnCharts B S hS t

/-! ### Condition (3) implies condition (4) -/

/-- **Stacks 0GGY, (3) ⟹ (4).** A target covering witnessing rig-flatness on charts yields a
source covering witnessing it: the two coverings of condition (3) compose into one covering of
the source, and each of its members factors through the chart of the target covering it lies
over. -/
@[stacks 0GGY "(3) ⟹ (4)"]
theorem hasRigFlatSourceCovering_of_hasRigFlatTargetCovering
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) (h : HasRigFlatTargetCovering B S hS f) :
    HasRigFlatSourceCovering B S hS f := by
  classical
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨J, V, v, ⟨hVaff, hVet, hVsurj⟩, hstage⟩ := h
  choose I U w hUcov hflat using hstage
  refine ⟨(Σ j, I j), fun p ↦ U p.1 p.2, fun p ↦ w p.1 p.2 ≫ pullback.snd (v p.1) f,
    ⟨fun p ↦ (hUcov p.1).1 p.2, fun p ↦ ((hUcov p.1).2.1 p.2).comp B S hS
      (isRepresentableEtale_pullback_snd B S hS (v p.1) f (hVet p.1)), ?_⟩, ?_⟩
  · -- The assembled family is jointly surjective: the base change of `{Vⱼ ⟶ Y}` along `f` is,
    -- and so is each `{Uⱼᵢ ⟶ Vⱼ ×_Y X}`.
    set e : (∐ fun p : Σ j, I j ↦ U p.1 p.2) ⟶ (∐ fun j ↦ pullback (v j) f) :=
      Sigma.desc fun p ↦ w p.1 p.2 ≫ Sigma.ι (fun j ↦ pullback (v j) f) p.1 with he
    have hEpi : Epi e := by
      refine ⟨fun α β hαβ ↦ Sigma.hom_ext _ _ fun j ↦ ?_⟩
      have _ : Epi (Sigma.desc (w j)) :=
        (Sheaf.isLocallySurjective_iff_epi _).mp (hUcov j).2.2
      refine (cancel_epi (Sigma.desc (w j))).1 (Sigma.hom_ext _ _ fun i ↦ ?_)
      simpa [he] using congrArg (Sigma.ι (fun p : Σ j, I j ↦ U p.1 p.2) ⟨j, i⟩ ≫ ·) hαβ
    have hfac : (Sigma.desc fun p : Σ j, I j ↦ w p.1 p.2 ≫ pullback.snd (v p.1) f) =
        e ≫ Sigma.desc fun j ↦ pullback.snd (v j) f :=
      Sigma.hom_ext _ _ fun p ↦ by simp [he]
    rw [hfac, Sheaf.isLocallySurjective_iff_epi]
    have _ : Epi (Sigma.desc fun j ↦ pullback.snd (v j) f) :=
      (Sheaf.isLocallySurjective_iff_epi _).mp
        (Sheaf.isLocallySurjective_sigmaDesc_pullback_snd f v hVsurj)
    infer_instance
  · intro p
    refine ⟨V p.1, v p.1, w p.1 p.2 ≫ pullback.fst (v p.1) f, hVaff p.1, hVet p.1, ?_,
      hflat p.1 p.2⟩
    rw [Category.assoc, Category.assoc, pullback.condition]

end AlgebraicGeometry.FormalSpace

end
