module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleCompletionChartLift
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFiniteTypeExample
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleCover
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
public import StacksFrontier.CategoryTheory.Sites.JointlyLocallySurjective
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.LocallySurjectiveTransfer

/-!
# A sheaf representable étale over `Spf A` is covered by formal spectra of étale completions

Let `S` be a scheme contained in a big fppf site `B`, let `A` be a weakly admissible topological
ring carrying the `I`-adic topology, presented over `S` by a quotient system `D`, and let
`φ : E ⟶ Spf A` be a morphism of fppf sheaves which is representable by algebraic spaces and
étale. Then `E` is covered, jointly surjectively as a sheaf, by formal spectra `Spf C^∧` of the
completions of étale `A`-algebras `C`, mapping to `E` over `Spf A`.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_completion_cover_of_isRepresentableEtale`: the
  statement above.

## Implementation notes

The family is indexed by all étale charts of the stages: an affine object `V` of the site with an
étale morphism to a quotient stage `Spec (A ⧸ Iᵐ⁺¹)` and a section of `E` over `V` lying over that
stage. Each such chart extends to `Spf C^∧` for an étale lift `C` of its coordinate ring
(`AlgebraicGeometry.FormalSpace.exists_completion_lift_of_etale_chart`).

Joint surjectivity is checked on sections. A section `s` of `E` over an affine object `T` lies
over a stage `Spec (A ⧸ Iᵐ⁺¹)` (Stacks 0AIA, `T` being quasi-compact), hence is a point of the
algebraic space `Spec (A ⧸ Iᵐ⁺¹) ×_{Spf A} E`. An atlas `U` of that algebraic space is étale over
the stage, and after the surjective étale base change `T ×_E U ⟶ T` the section factors through
`U`; on the affine open cover of `U` it then lies in the image of the charts it consists of. A
general object of the site is covered by affine ones.

## References

* [Stacks Project, Tag 0AIA](https://stacks.math.columbia.edu/tag/0AIA)
* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
* [Stacks Project, Tag 04D1](https://stacks.math.columbia.edu/tag/04D1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The sieve of the arrows along which a section of `F` lies in the image of a member of a
family of morphisms into `F`, restricted along a morphism, is the sieve of the restricted
section. -/
theorem sieveOfSection_jointRange_pullback {ι : Type (u + 1)} {G : ι → FppfSheaf B S hS}
    {F : FppfSheaf B S hS} (c : ∀ i, G i ⟶ F) {T T' : BigFppfOver B S hS} (f : T' ⟶ T)
    (s : F.obj.obj (op T)) :
    ((Sheaf.jointRange c).sieveOfSection s).pullback f =
      (Sheaf.jointRange c).sieveOfSection (F.obj.map f.op s) := by
  ext Y g
  change F.obj.map (g ≫ f).op s ∈ _ ↔ F.obj.map g.op (F.obj.map f.op s) ∈ _
  rw [op_comp, Functor.map_comp_apply]


variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A]

omit [IsLinearTopology A A] in
attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **The local surjectivity onto a section over an affine object.** Let `φ : E ⟶ Spf A` be
representable étale, with `A` carrying the `I`-adic topology, and let `w` be a family of
morphisms into `E` such that every étale chart of a stage — a morphism `e : h_V ⟶ E` from an
affine object `V` over an étale `p : V ⟶ Spec (A ⧸ Iᵐ⁺¹)` — lies in the image of a member of
`w`. Then every section of `E` over an affine object lies, locally, in the image of a member of
`w`. -/
theorem sieveOfSection_jointRange_mem_of_isAffine
    (hA : TopologicalRing.IsWeaklyPreAdmissible A) {I : Ideal A} (hIadic : _root_.IsAdic I)
    (D : QuotientSystem B S hS A) {E : FppfSheaf B S hS} (φ : E ⟶ formalSpectrum D)
    (hφ : IsRepresentableEtale B S hS φ) {ι : Type (u + 1)} {G : ι → FppfSheaf B S hS}
    (w : ∀ k, G k ⟶ E)
    (hw : ∀ (m : ℕ) (V : BigFppfOver B S hS)
      (p : V ⟶ (BigAffineFppf.inclusion B S hS).obj (D.stage (adicStage hIadic m))),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
      Etale ((BigFppfOver.toScheme B S hS).map p) →
      ∀ e : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ E,
      e ≫ φ = (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map p ≫
        formalSpectrumInclusion D (OrderDual.toDual (adicStage hIadic m)) →
      ∃ (k : ι) (t : (G k).obj.obj (op V)),
        (w k).hom.app (op V) t = Sheaf.sectionEquiv (BigFppfOver.topology B S hS) e)
    (T : BigFppfOver B S hS) (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (s : E.obj.obj (op T)) :
    (Sheaf.jointRange w).sieveOfSection s ∈ BigFppfOver.topology B S hS T := by
  classical
  let Jt := BigFppfOver.topology B S hS
  let G := BigFppfOver.toScheme B S hS
  let Y := Sheaf.sheafifiedYoneda Jt
  let P : ℕ → BigFppfOver B S hS := fun m =>
    (BigAffineFppf.inclusion B S hS).obj (D.stage (adicStage hIadic m))
  let incl : ∀ m, Y.obj (P m) ⟶ formalSpectrum D := fun m =>
    formalSpectrumInclusion D (OrderDual.toDual (adicStage hIadic m))
  -- the section lies over a stage
  obtain ⟨J₁, p₁, hp₁⟩ := exists_factorsThroughStage_of_compactSpace hA D T inferInstance
    ((Sheaf.sectionEquiv Jt).symm s ≫ φ)
  obtain ⟨m, hm⟩ := exists_adicStage_le hIadic J₁
  let p : T ⟶ P m := p₁ ≫ (BigAffineFppf.inclusion B S hS).map (D.transition hm)
  have hp : Y.map p ≫ incl m = (Sheaf.sectionEquiv Jt).symm s ≫ φ := by
    have hw' := colimit.w (formalSpectrumDiagram D)
      (homOfLE (show OrderDual.toDual J₁ ≤ OrderDual.toDual (adicStage hIadic m) from hm))
    refine Eq.trans ?_ hp₁
    change Y.map (p₁ ≫ (BigAffineFppf.inclusion B S hS).map (D.transition hm)) ≫ incl m = _
    rw [Functor.map_comp, Category.assoc]
    exact congrArg (fun c => Y.map p₁ ≫ c) hw'
  -- the stage base change of `φ`, and an atlas of it
  let ξ : (uliftYoneda.{u + 1}).obj (P m) ⟶ (formalSpectrum D).obj :=
    uliftYonedaEquiv.symm (Sheaf.sectionEquiv Jt (incl m))
  obtain ⟨U, a, hsurj, het⟩ := (hφ.1 (P m) ξ).exists_atlas
  let pU : U ⟶ P m := (uliftYoneda.{u + 1}).preimage (a ≫ pullback.fst ξ φ.hom)
  have hpU : (uliftYoneda.{u + 1}).map pU = a ≫ pullback.fst ξ φ.hom := Functor.map_preimage _ _
  have hpUet : Etale (G.map pU) := by
    have h := hφ.2 (P m) ξ U a het
    change (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) G).relative
      (uliftYoneda.{u + 1}) (a ≫ pullback.fst ξ φ.hom) at h
    rw [← hpU] at h
    exact (MorphismProperty.of_relative_map h :
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) G) pU)
  -- the section as a point of the stage base change, and its base change along the atlas
  have hcomp : (uliftYoneda.{u + 1}).map p ≫ ξ = uliftYonedaEquiv.symm s ≫ φ.hom := by
    refine ((uliftYonedaEquiv_symm_map p.op _).symm).trans ?_
    rw [uliftYonedaEquiv_symm_comp]
    congr 1
    rw [← Sheaf.sectionEquiv_map_comp, hp, Sheaf.sectionEquiv_comp, Equiv.apply_symm_apply]
  let gT : (uliftYoneda.{u + 1}).obj T ⟶ pullback ξ φ.hom := pullback.lift _ _ hcomp
  let q := hsurj.rep.snd gT
  let fst' := hsurj.rep.fst' gT
  have hsq : (uliftYoneda.{u + 1}).map fst' ≫ a = (uliftYoneda.{u + 1}).map q ≫ gT :=
    (hsurj.rep.isPullback' gT).w
  let ζ : E.obj.obj (op U) := uliftYonedaEquiv (a ≫ pullback.snd ξ φ.hom)
  have hsec : E.obj.map q.op s = E.obj.map fst'.op ζ := by
    have h := congrArg (fun c => c ≫ pullback.snd ξ φ.hom) hsq
    simp only [Category.assoc, gT, pullback.lift_snd] at h
    rw [uliftYonedaEquiv_naturality, Quiver.Hom.unop_op, h,
      show (uliftYoneda.{u + 1}).map q ≫ uliftYonedaEquiv.symm s =
        uliftYonedaEquiv.symm (E.obj.map q.op s) from (uliftYonedaEquiv_symm_map q.op s).symm,
      Equiv.apply_symm_apply]
  -- the section of the atlas lies in the image of the charts of its affine open cover
  have hU : (Sheaf.jointRange w).sieveOfSection ζ ∈ Jt U := by
    obtain ⟨Ij, Uj, πj, hUj, hπj, hcov⟩ := BigFppfOver.exists_affine_open_cover B S hS U
    refine Jt.superset_covering ?_ hcov
    rw [Sieve.generate_le_iff]
    rintro _ _ ⟨j⟩
    change E.obj.map (πj j).op ζ ∈ (Sheaf.jointRange w).obj (op (Uj j))
    rw [Sheaf.mem_jointRange_obj_iff]
    have het' : Etale (G.map (πj j ≫ pU)) := by
      have := hπj j
      rw [Functor.map_comp]
      infer_instance
    obtain ⟨k, t, ht⟩ := hw m (Uj j) (πj j ≫ pU) (hUj j) het'
      ((Sheaf.sectionEquiv Jt).symm (E.obj.map (πj j).op ζ)) (by
        apply (Sheaf.sectionEquiv Jt).injective
        have hζ : φ.hom.app (op U) ζ = (formalSpectrum D).obj.map pU.op
            (Sheaf.sectionEquiv Jt (incl m)) := by
          change uliftYonedaEquiv ((a ≫ pullback.snd ξ φ.hom) ≫ φ.hom) = _
          rw [Category.assoc, ← pullback.condition, ← Category.assoc, ← hpU]
          exact (congrArg uliftYonedaEquiv (uliftYonedaEquiv_symm_map pU.op _).symm).trans
            (Equiv.apply_symm_apply _ _)
        refine (Sheaf.sectionEquiv_comp Jt _ φ).trans ?_
        refine Eq.trans ?_ (Sheaf.sectionEquiv_map_comp Jt (πj j ≫ pU) (incl m)).symm
        rw [Equiv.apply_symm_apply, NatTrans.naturality_apply, hζ, op_comp,
          Functor.map_comp_apply])
    exact ⟨k, t, ht.trans (Equiv.apply_symm_apply _ _)⟩
  have hmain : ((Sheaf.jointRange w).sieveOfSection s).pullback q ∈
      Jt (hsurj.rep.pullback gT) := by
    rw [sieveOfSection_jointRange_pullback, hsec, ← sieveOfSection_jointRange_pullback]
    exact Jt.pullback_stable fst' hU
  refine Jt.transitive (Space.sieve_generate_singleton_mem_topology_over B S hS q
    (hsurj.property_snd gT) (het.property_snd gT)) _ ?_
  rintro Z f ⟨Z', c, q', hq', rfl⟩
  cases hq'
  rw [Sieve.pullback_comp]
  exact Jt.pullback_stable c hmain

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **A sheaf representable étale over `Spf A` is covered by formal spectra of completions of
étale `A`-algebras.** Let `A` be a weakly admissible topological ring carrying the `I`-adic
topology, presented over `S` by a quotient system `D` whose atlas of quotient spectra lies in the
site, and let `φ : E ⟶ Spf A` be representable by algebraic spaces and étale. Then there are
étale ring maps `f k : A → C k`, quotient systems on the completions `C k ^∧` with continuous
maps from `D` realising the canonical maps, and morphisms `w k : Spf (C k ^∧) ⟶ E` over `Spf A`
which are jointly surjective as morphisms of sheaves. -/
theorem exists_completion_cover_of_isRepresentableEtale
    (hA : TopologicalRing.IsWeaklyAdmissible A) {I : Ideal A} (_hI : I.FG)
    (hIadic : _root_.IsAdic I)
    (D : QuotientSystem B S hS A) (hD : D.HasLargeSite)
    {E : FppfSheaf B S hS} (φ : E ⟶ formalSpectrum D) (hφ : IsRepresentableEtale B S hS φ) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    ∃ (K : Type (u + 1)) (C : K → Type u) (_ : ∀ k, CommRing (C k)) (f : ∀ k, A →+* C k)
      (_ : ∀ k, (f k).Etale)
      (Q : ∀ k, QuotientSystem B S hS (TopologicalRing.CompletionOver (f k)))
      (g : ∀ k, ContinuousHom D (Q k))
      (_ : ∀ k, (g k).toRingHom = TopologicalRing.CompletionOver.canonicalMap (f k))
      (w : ∀ k, formalSpectrum (Q k) ⟶ E),
      (∀ k, w k ≫ φ = formalSpectrumMap hA (g k)) ∧ Sheaf.IsLocallySurjective (Sigma.desc w) := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  let Jt := BigFppfOver.topology B S hS
  let Y := Sheaf.sheafifiedYoneda Jt
  -- the étale charts of the stages
  let K : Type (u + 1) := Σ (m : ℕ) (V : BigFppfOver B S hS),
    { pe : (V ⟶ (BigAffineFppf.inclusion B S hS).obj (D.stage (adicStage hIadic m))) ×
        (Y.obj V ⟶ E) //
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
        Etale ((BigFppfOver.toScheme B S hS).map pe.1) ∧
        pe.2 ≫ φ = Y.map pe.1 ≫
          formalSpectrumInclusion D (OrderDual.toDual (adicStage hIadic m)) }
  have hlift : ∀ c : K, ∃ (C : Type u) (_ : CommRing C) (f : A →+* C) (_ : f.Etale)
      (Q : QuotientSystem B S hS (TopologicalRing.CompletionOver f))
      (g : ContinuousHom D Q) (_ : g.toRingHom = TopologicalRing.CompletionOver.canonicalMap f)
      (w : formalSpectrum Q ⟶ E) (σ : Y.obj c.2.1 ⟶ formalSpectrum Q),
      w ≫ φ = formalSpectrumMap hA g ∧ σ ≫ w = c.2.2.1.2 := fun c =>
    exists_completion_lift_of_etale_chart hA hIadic D hD φ
      (formallyEtale_hom_of_isRepresentableEtale φ hφ) c.1 c.2.1 c.2.2.1.1
      c.2.2.2.1 c.2.2.2.2.1 c.2.2.1.2 c.2.2.2.2.2
  choose C instC f hf Q g hg w σ hw hσ using hlift
  refine ⟨K, C, instC, f, hf, Q, g, hg, w, hw, ?_⟩
  rw [Sheaf.isLocallySurjective_sigmaDesc_iff]
  intro T s
  refine ⟨(Sheaf.jointRange w).sieveOfSection s, ?_, fun _ _ hh =>
    (Sheaf.mem_jointRange_obj_iff w _).1 hh⟩
  -- the affine case
  have haff : ∀ (T' : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj T') →
      ∀ s' : E.obj.obj (op T'), (Sheaf.jointRange w).sieveOfSection s' ∈ Jt T' := by
    intro T' hT' s'
    refine sieveOfSection_jointRange_mem_of_isAffine B S hS hA.1 hIadic D φ hφ w ?_ T' hT' s'
    intro m V p hV hp e he
    refine ⟨⟨m, V, ⟨(p, e), hV, hp, he⟩⟩, Sheaf.sectionEquiv Jt (σ ⟨m, V, ⟨(p, e), hV, hp, he⟩⟩),
      ?_⟩
    rw [← Sheaf.sectionEquiv_comp, hσ]
  -- a general object is covered by affine ones
  obtain ⟨Ia, Ta, πa, hTa, -, hcov⟩ := BigFppfOver.exists_affine_open_cover B S hS T
  refine Jt.transitive hcov _ ?_
  rintro Z h ⟨Z', c, _, ⟨i⟩, rfl⟩
  rw [Sieve.pullback_comp, sieveOfSection_jointRange_pullback]
  exact Jt.pullback_stable c (haff (Ta i) (hTa i) _)

end AlgebraicGeometry.FormalSpace

end
