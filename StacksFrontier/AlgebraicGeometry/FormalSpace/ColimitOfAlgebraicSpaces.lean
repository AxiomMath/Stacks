module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedSurjective

/-!
# Directed colimits of algebraic spaces along thickenings

Let `S` be a scheme contained in a big fppf site `B` and let `(Xᵢ)` be a directed system of
algebraic spaces over `S` whose transition morphisms are representable thickenings.
**Stacks 0AIU** says that the colimit of such a system, formed among fppf sheaves, is a formal
algebraic space over `S`.

## Main results

* `AlgebraicGeometry.FormalSpace.isRepresentableEtale_of_stageSquares`: a morphism of fppf
  sheaves is representable étale as soon as it becomes so after base change along a family of
  morphisms into its target through which every scheme-valued point of that target factors.
* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_colimit_thickenings`:
  **Stacks 0AIU**, granting the étale charts of the system as a hypothesis.
* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_isAlgebraicSpace_of_affineFormal`:
  the hypotheses of the previous statement are satisfiable, on the constant diagram over
  `PUnit`.

## Implementation notes

The geometric input of the Stacks proof is not available in this library. There an affine étale
chart of one stage `X_λ` is transported to every later stage along the thickenings, by the
topological invariance of the étale site (**Stacks 05ZH**); the transported charts stay affine
(**Stacks 07VT**), their colimit is an affine formal algebraic space, and it is étale over the
colimit because a morphism from an affine scheme to the colimit factors through a stage, a step
the source omits. Neither 05ZH nor 07VT is carried here, so the chart system is a hypothesis:
`G` is the system of chart diagrams, `α` maps it to the system of stages, `haff` says that each
chart diagram colimits to an affine formal algebraic space, `hαet` that each chart morphism is
representable étale, `hsq` that the charts base change from the colimit, `hcov` that they cover
each stage, and `hfac` is the omitted factorization of a scheme-valued point of the colimit
through a stage. The library does carry the affine analogue of `hfac`,
`AlgebraicGeometry.exists_factor_through_thickening` (**Stacks 0AIA**), for a quasi-compact
source and a presented affine formal algebraic space.

What is proved from that input is the passage from the stages to the colimit: `hsq` and `hfac`
make the induced morphism out of each chart colimit representable étale
(`isRepresentableEtale_of_stageSquares`), `hcov` makes the resulting family jointly surjective,
and the atlas so assembled is the one Definition 0AIM asks for. The algebraic-space hypothesis
on the stages and the thickening hypothesis on the transition morphisms are kept in the
statement, where the source puts them, but they are consumed by the chart hypothesis and so go
unused; that is why they are written `_halg` and `_hthick`.

The set-theoretic condition of Stacks 0AIS on the colimit is a hypothesis rather than a
conclusion, for the same reason as in
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_etaleCover`: it does not follow from
the remaining data.

## References

* [Stacks Project, Tag 0AIA](https://stacks.math.columbia.edu/tag/0AIA)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AIU](https://stacks.math.columbia.edu/tag/0AIU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An isomorphism of presheaves on the big fppf site of `S` is a representable thickening: a
represented base change of it is an isomorphism of the site, and an isomorphism of schemes is a
surjective closed immersion. -/
theorem isRepresentableThickeningULift_of_isIso
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (f : F ⟶ G) [IsIso f] :
    Space.IsRepresentableThickeningULift.{u + 1} B S hS f := by
  refine ⟨Functor.relativelyRepresentable.of_isIso _ _, ?_⟩
  intro A C g fst snd hpb
  have h1 : IsIso ((uliftYoneda.{u + 1}).map snd) := hpb.isIso_snd_of_isIso
  have h2 : IsIso snd :=
    Functor.FullyFaithful.isIso_of_isIso_map (ULiftYoneda.fullyFaithful _) snd
  show Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map snd)
  have h3 : IsIso ((BigFppfOver.toScheme B S hS).map snd) := inferInstance
  exact ⟨inferInstance, ((BigFppfOver.toScheme B S hS).map snd).surjective⟩

/-- An isomorphism of fppf sheaves is representable étale. -/
theorem isRepresentableEtale_of_isIso {X Y : FppfSheaf B S hS} (f : X ⟶ Y) [IsIso f] :
    IsRepresentableEtale B S hS f := by
  have hiso : IsIso f.hom := inferInstance
  have hpb : ∀ (U : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj U ⟶ Y.obj),
      IsPullback (𝟙 ((uliftYoneda.{u + 1}).obj U)) (ξ ≫ inv f.hom) ξ f.hom :=
    fun U ξ ↦ IsPullback.of_horiz_isIso ⟨by simp⟩
  have hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom := by
    intro U ξ
    exact Space.isAlgebraicSpaceULift_of_iso B S hS (hpb U ξ).isoPullback
      (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS U)
  refine ⟨hrep, ?_⟩
  intro U ξ
  have hfst : (hpb U ξ).isoPullback.hom ≫ pullback.fst ξ f.hom =
      𝟙 ((uliftYoneda.{u + 1}).obj U) :=
    (hpb U ξ).isoPullback_hom_fst
  have hfstiso : IsIso (pullback.fst ξ f.hom) := by
    have heq : pullback.fst ξ f.hom = (hpb U ξ).isoPullback.inv := by
      rw [← cancel_epi (hpb U ξ).isoPullback.hom, hfst, Iso.hom_inv_id]
    rw [heq]
    infer_instance
  exact isEtaleULift_of_isIso B S hS (pullback.fst ξ f.hom)

/-- A morphism of fppf sheaves is representable étale as soon as it becomes so after base change
along a family of morphisms into its target through which every scheme-valued point of that
target factors: such a point is carried into one member of the family, and the base change of
the morphism along the point is then the base change along that point of the corresponding
member of the family. -/
theorem isRepresentableEtale_of_stageSquares {Λ : Type*}
    {X Z : FppfSheaf B S hS} {Y W : Λ → FppfSheaf B S hS} (ζ : X ⟶ Z)
    (p : ∀ i, Y i ⟶ X) (a : ∀ i, Y i ⟶ W i) (ψ : ∀ i, W i ⟶ Z)
    (ha : ∀ i, IsRepresentableEtale B S hS (a i))
    (hsq : ∀ i, IsPullback (p i) (a i) ζ (ψ i))
    (hfac : ∀ (U : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj U ⟶ Z.obj),
      ∃ (i : Λ) (ξ' : (uliftYoneda.{u + 1}).obj U ⟶ (W i).obj), ξ = ξ' ≫ (ψ i).hom) :
    IsRepresentableEtale B S hS ζ := by
  classical
  have key : ∀ (U : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj U ⟶ Z.obj),
      ∃ (i : Λ) (ξ' : (uliftYoneda.{u + 1}).obj U ⟶ (W i).obj)
        (e : pullback ξ' (a i).hom ≅ pullback ξ ζ.hom),
        e.hom ≫ pullback.fst ξ ζ.hom = pullback.fst ξ' (a i).hom := by
    intro U ξ
    obtain ⟨i, ξ', hξ⟩ := hfac U ξ
    have hsqP : IsPullback (p i).hom (a i).hom ζ.hom (ψ i).hom :=
      (hsq i).map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    have hcomp : IsPullback (pullback.fst ξ' (a i).hom)
        (pullback.snd ξ' (a i).hom ≫ (p i).hom) (ξ' ≫ (ψ i).hom) ζ.hom :=
      (IsPullback.of_hasPullback ξ' (a i).hom).paste_vert hsqP.flip
    rw [← hξ] at hcomp
    exact ⟨i, ξ', hcomp.isoPullback, hcomp.isoPullback_hom_fst⟩
  have hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS ζ.hom := by
    intro U ξ
    obtain ⟨i, ξ', e, -⟩ := key U ξ
    exact Space.isAlgebraicSpaceULift_of_iso B S hS e ((ha i).1 U ξ')
  refine ⟨hrep, ?_⟩
  intro U ξ
  obtain ⟨i, ξ', e, hfst⟩ := key U ξ
  have h1 : Space.IsEtaleULift.{u + 1} B S hS (e.hom ≫ pullback.fst ξ ζ.hom) := by
    rw [hfst]
    exact (ha i).2 U ξ'
  have h2 := isEtaleULift_precomp_iso B S hS e.symm (e.hom ≫ pullback.fst ξ ζ.hom) h1
  simpa using h2

/-- **Stacks 0AIU**, granting the étale charts of the system. Let `E` be a directed system of
fppf sheaves over `S` whose stages are algebraic spaces and whose transition morphisms are
representable thickenings. A sheaf `Z` isomorphic to its colimit, satisfying the set-theoretic
condition of Stacks 0AIS and admitting a system of affine étale charts as in the Stacks proof,
is a formal algebraic space over `S`.

The charts are the hypotheses `G`, `α`, `haff`, `hαet`, `hsq` and `hcov`, and `hfac` says that a
scheme-valued point of the colimit factors through a stage. What is proved is that the colimit
of each chart diagram is representable étale over `Z` and that these colimits cover `Z`, so that
they form an atlas as in Definition 0AIM. -/
@[stacks 0AIU "granting the chart system that the topological invariance of the étale site \
(Stacks 05ZH) and the affineness of a thickening of an affine scheme (Stacks 07VT) produce from \
an affine étale chart of one stage, neither of which this library carries: the chart diagrams, \
their colimits being affine formal algebraic spaces, their being representable étale over and \
covering each stage, and the factorization of a scheme-valued point of the colimit through a \
stage — the step the source omits — are the hypotheses `G`, `α`, `haff`, `hαet`, `hsq`, `hcov` \
and `hfac`. What is proved is the passage from the stages to the colimit: that those colimits \
are an atlas of the colimit sheaf in the sense of Definition 0AIM. The set-theoretic condition \
of Stacks 0AIS on the colimit is the hypothesis `hZset`, as it is for Stacks 0AJ1"]
theorem isFormalAlgebraicSpace_of_colimit_thickenings
    (Λ : Type (u + 1)) [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (E : Λ ⥤ FppfSheaf B S hS)
    (_halg : ∀ i : Λ, Space.IsAlgebraicSpaceULift.{u + 1} B S hS (E.obj i).obj)
    (_hthick : ∀ ⦃i j : Λ⦄ (g : i ⟶ j),
      Space.IsRepresentableThickeningULift.{u + 1} B S hS (E.map g).hom)
    (I : Type (u + 1)) (G : I → (Λ ⥤ FppfSheaf B S hS)) (α : ∀ k, G k ⟶ E)
    (haff : ∀ k, IsAffineFormalAlgebraicSpace B S hS (colimit (G k)))
    (hαet : ∀ (k : I) (i : Λ), IsRepresentableEtale B S hS ((α k).app i))
    (hsq : ∀ (k : I) (i : Λ),
      IsPullback (colimit.ι (G k) i) ((α k).app i) (colimMap (α k)) (colimit.ι E i))
    (hcov : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      ∀ i : Λ, Sheaf.IsLocallySurjective (Sigma.desc (fun k ↦ (α k).app i)))
    (hfac : ∀ (U : BigFppfOver B S hS)
      (ξ : (uliftYoneda.{u + 1}).obj U ⟶ (colimit E).obj),
      ∃ (i : Λ) (ξ' : (uliftYoneda.{u + 1}).obj U ⟶ (E.obj i).obj),
        ξ = ξ' ≫ (colimit.ι E i).hom)
    (Z : FppfSheaf B S hS) (hZset : SatisfiesSetTheoreticCondition B S hS Z)
    (hZ : Nonempty (Z ≅ colimit E)) :
    IsFormalAlgebraicSpace B S hS Z := by
  classical
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨eZ⟩ := hZ
  refine ⟨hZset, I, (fun k ↦ colimit (G k)), (fun k ↦ colimMap (α k) ≫ eZ.inv), haff, ?_, ?_⟩
  · -- the colimit of each chart diagram is representable étale over `Z`
    intro k
    refine isRepresentableEtale_of_stageSquares B S hS (colimMap (α k) ≫ eZ.inv)
      (fun i ↦ colimit.ι (G k) i) (fun i ↦ (α k).app i)
      (fun i ↦ colimit.ι E i ≫ eZ.inv) (hαet k) (fun i ↦ ?_) (fun U ξ ↦ ?_)
    · exact (hsq k i).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) eZ.symm
        (by simp) (by simp) (by simp) (by simp)
    · obtain ⟨i, ξ', hξ⟩ := hfac U (ξ ≫ eZ.hom.hom)
      refine ⟨i, ξ', ?_⟩
      have h : (colimit.ι E i ≫ eZ.inv).hom = (colimit.ι E i).hom ≫ eZ.inv.hom := rfl
      rw [h, ← Category.assoc, ← hξ]
      simp
  · -- the chart colimits cover `Z`
    rw [Sheaf.isLocallySurjective_iff_epi]
    refine ⟨?_⟩
    intro T k l hkl
    have hζkl : ∀ m : I, (colimMap (α m) ≫ eZ.inv) ≫ k = (colimMap (α m) ≫ eZ.inv) ≫ l := by
      intro m
      have h := congrArg (fun t ↦ Sigma.ι (fun m : I ↦ colimit (G m)) m ≫ t) hkl
      simpa using h
    have hcolim : eZ.inv ≫ k = eZ.inv ≫ l := by
      refine colimit.hom_ext (fun i ↦ ?_)
      have hepi : Epi (Sigma.desc (fun m ↦ (α m).app i)) :=
        (Sheaf.isLocallySurjective_iff_epi _).mp (hcov i)
      refine (cancel_epi (Sigma.desc (fun m ↦ (α m).app i))).1 (Sigma.hom_ext _ _ (fun m ↦ ?_))
      have hm := hζkl m
      simp only [Category.assoc] at hm
      have hm2 := congrArg (fun t ↦ colimit.ι (G m) i ≫ t) hm
      simp only [ι_colimMap_assoc] at hm2
      simpa using hm2
    exact (cancel_epi eZ.inv).1 hcolim

/-- The hypotheses of `isFormalAlgebraicSpace_of_colimit_thickenings` are satisfiable: an fppf
sheaf which is at once an algebraic space and an affine formal algebraic space is a formal
algebraic space, by the constant diagram over `PUnit`, whose transition morphism is the identity
and whose single chart is the sheaf itself. -/
theorem isFormalAlgebraicSpace_of_isAlgebraicSpace_of_affineFormal (Y : FppfSheaf B S hS)
    (hY : Space.IsAlgebraicSpaceULift.{u + 1} B S hS Y.obj)
    (hYaff : IsAffineFormalAlgebraicSpace B S hS Y) :
    IsFormalAlgebraicSpace B S hS Y := by
  classical
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  let E : PUnit.{u + 2} ⥤ FppfSheaf B S hS := (Functor.const PUnit.{u + 2}).obj Y
  obtain ⟨one, honeApp⟩ :
      ∃ one : E ⟶ E, ∀ i : PUnit.{u + 2}, one.app i = 𝟙 (E.obj i) :=
    ⟨{ app := fun _ ↦ 𝟙 Y, naturality := fun _ _ _ ↦ rfl }, fun _ ↦ rfl⟩
  have hterm : IsTerminal (PUnit.unit : PUnit.{u + 2}) :=
    IsTerminal.ofUniqueHom (fun _ ↦ homOfLE (le_refl _)) (fun _ _ ↦ rfl)
  have hιiso : IsIso (colimit.ι E PUnit.unit) := isIso_ι_of_isTerminal hterm E
  let eY : Y ≅ colimit E := asIso (colimit.ι E PUnit.unit)
  have hone : colimMap one = 𝟙 (colimit E) := by
    refine colimit.hom_ext (fun i ↦ ?_)
    rw [ι_colimMap, honeApp, Category.id_comp, Category.comp_id]
  have haff : ∀ _k : PUnit.{u + 2}, IsAffineFormalAlgebraicSpace B S hS (colimit E) := by
    intro _k
    obtain ⟨hset, Ω, pre, hne, hdir, D, hD, ⟨eD⟩⟩ := hYaff
    refine ⟨?_, Ω, pre, hne, hdir, D, hD, ⟨eY.symm ≪≫ eD⟩⟩
    obtain ⟨U, R, hU, hR, hUrep, hRrep, f, hf, g, hg⟩ := hset
    have hsq : IsPullback (pullback.fst f f) (pullback.snd f f) (f ≫ eY.hom) (f ≫ eY.hom) :=
      (IsPullback.of_hasPullback f f).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) eY
        (by simp) (by simp) (by simp) (by simp)
    exact ⟨U, R, hU, hR, hUrep, hRrep, f ≫ eY.hom, epi_comp f eY.hom,
      g ≫ hsq.isoPullback.hom, epi_comp g hsq.isoPullback.hom⟩
  refine isFormalAlgebraicSpace_of_colimit_thickenings B S hS PUnit.{u + 2} E
    (fun _ ↦ hY) (fun _ _ g ↦ ?_) PUnit.{u + 2} (fun _ ↦ E) (fun _ ↦ one) haff
    (fun _ i ↦ ?_) (fun _ i ↦ ?_) (fun i ↦ ?_) (fun U ξ ↦ ?_) Y hYaff.1 ⟨eY⟩
  · -- the transition morphisms of the constant diagram are isomorphisms
    have h0 : IsIso (E.map g) := by
      show IsIso (𝟙 Y)
      infer_instance
    exact isRepresentableThickeningULift_of_isIso B S hS (E.map g).hom
  · -- the single chart morphism is the identity
    rw [honeApp]
    exact isRepresentableEtale_of_isIso B S hS (𝟙 (E.obj i))
  · -- the chart square
    have h1 : IsIso (one.app i) := by
      rw [honeApp]
      infer_instance
    have h2 : IsIso (colimMap one) := by
      rw [hone]
      infer_instance
    exact IsPullback.of_vert_isIso ⟨ι_colimMap one i⟩
  · -- the single chart covers each stage
    rw [Sheaf.isLocallySurjective_iff_epi]
    refine (IsSplitEpi.mk' ⟨Sigma.ι (fun _ : PUnit.{u + 2} ↦ E.obj i) PUnit.unit, ?_⟩).epi
    simp [honeApp]
  · -- a point of the colimit factors through the single stage
    exact ⟨PUnit.unit, ξ ≫ inv (colimit.ι E PUnit.unit).hom, by simp⟩

end AlgebraicGeometry.FormalSpace

end
