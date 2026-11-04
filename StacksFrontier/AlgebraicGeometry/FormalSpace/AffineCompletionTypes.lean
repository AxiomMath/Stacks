module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionAlongIdeal
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFormalSpectrum
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubspaceLocalTypes
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.Topology.Algebra.AdicLimitTopology

/-!
# The local types of the completion of an affine scheme along a closed subset

Let `S` be a scheme contained in a big fppf site `B`, let `X = Spec A` be an affine scheme over
`S` lying in that site and let `T ⊆ |X|` be a closed subset. **Stacks 0GBA** determines the type
of the affine formal algebraic space `X_{/T}`: it is adic\* when the complement of `T` is
quasi-compact, and Noetherian when `A` is a Noetherian ring.

Both clauses reduce to clause (2), which identifies `X_{/T}` with `Spf (A^∧)` when `T = V(I)`
for a finitely generated ideal `I`: a closed subset with quasi-compact complement is the zero
locus of a finitely generated ideal, and over a Noetherian ring every ideal is finitely
generated. The affine formal algebraic space `Spf (A^∧)` is then the completion `X^∧_{V(I)}`
along the closed subscheme of `I`, whose type is **Stacks 0GXX**: adic\* by clause (3), and
Noetherian by clause (4), both of which are available in
`StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubspaceLocalTypes`.

## Main results

* `AlgebraicGeometry.FormalSpace.isClassical_of_iso`: the classical condition of Stacks 0AID
  depends on an affine formal algebraic space only up to isomorphism. Its Noetherian and
  adic\* siblings `AlgebraicGeometry.FormalSpace.isNoetherian_of_iso` and
  `AlgebraicGeometry.FormalSpace.isAdicStar_of_iso` are in
  `StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubspaceLocalTypes`, which needs them
  itself.
* `AlgebraicGeometry.FormalSpace.adicCompletionLimitTopology_eq_adicModuleTopology`: for a
  finitely generated ideal the inverse-limit topology on the adic completion is the adic
  topology of the completion as a module.
* `AlgebraicGeometry.FormalSpace.nonempty_completionAlongIdealIsoCompletionSheaf`: for a
  finitely generated ideal, the completion along its closed subscheme is the completion along
  its zero locus.
* `AlgebraicGeometry.FormalSpace.isAdicStar_completionSheaf`: **Stacks 0GBA (1)**.
* `AlgebraicGeometry.FormalSpace.isNoetherian_completionSheaf`: **Stacks 0GBA (3)**.

## Implementation notes

The two descriptions of the completion that have to be matched up carry *different* topologies
on the `I`-adic completion `A^∧` of `A`. Stacks 0GXX
(`AlgebraicGeometry.FormalSpace.completionAlongIdeal`) presents `A^∧` with the topology of the
inverse limit of its discrete quotients, while clause (2) of Stacks 0GBA
(`AlgebraicGeometry.FormalSpace.isIso_completionComparison`) presents it with the adic topology
of `A^∧` as an `A`-module. For a finitely generated `I` the two are the same topology, since the
kernel of the `n`-th projection of `A^∧` is then exactly `I ^ n A^∧`; that is
`adicCompletionLimitTopology_eq_adicModuleTopology`, and
`exists_adicQuotientSystem_of_fg` transports the quotient system of 0GXX along it, which is
what lets the comparison of clause (2) be applied to a completion whose type is known.

Isomorphism invariance of the affine types is proved from the bottom up in
`StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubspaceLocalTypes`: a presentation by
affine thickenings, a presenting topological ring, and the set-theoretic condition of Stacks
0AIS all transport along an isomorphism of sheaves. For the set-theoretic condition the only
point is that the kernel pair of a surjection changes along the isomorphism by a canonical
isomorphism of fibre products, which is
`AlgebraicGeometry.FormalSpace.pullbackCompIso`. Only the classical clause is proved here.

The passage from a closed subset to an ideal is `PrimeSpectrum.isCompact_isOpen_iff_ideal` for
clause (1) — the complement is a quasi-compact open, hence the complement of the zero locus of
a finitely generated ideal — and, for clause (3), the vanishing ideal of the closed subset,
which is finitely generated because `A` is Noetherian. The dictionary between a set of points of
the represented presheaf and a subset of the scheme is the comparison bijection
`AlgebraicGeometry.Space.pointsToScheme` of Stacks 03BV, which is a homeomorphism for the point
topology of Stacks 03BX.

## References

* [Stacks Project, Tag 0GBA](https://stacks.math.columbia.edu/tag/0GBA)
* [Stacks Project, Tag 0GXX](https://stacks.math.columbia.edu/tag/0GXX)
* [Stacks Project, Tag 0AID](https://stacks.math.columbia.edu/tag/0AID)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0316](https://stacks.math.columbia.edu/tag/0316)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

/-! ### Isomorphism invariance of the affine types -/

section Iso

attribute [local instance] sheaf_hasColimits

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Composing the two legs of a fibre product of a morphism with itself with a monomorphism
does not change the fibre product. -/
def pullbackCompIso {X Y Z : FppfSheaf B S hS}
    (f : X ⟶ Z) (m : Z ⟶ Y) [Mono m] : pullback f f ≅ pullback (f ≫ m) (f ≫ m) where
  hom := pullback.lift (pullback.fst f f) (pullback.snd f f) (by
    rw [← Category.assoc, ← Category.assoc, pullback.condition])
  inv := pullback.lift (pullback.fst (f ≫ m) (f ≫ m)) (pullback.snd (f ≫ m) (f ≫ m)) (by
    have h := pullback.condition (f := f ≫ m) (g := f ≫ m)
    rw [← Category.assoc, ← Category.assoc] at h
    exact (cancel_mono m).mp h)
  hom_inv_id := by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.id_comp]

/-- **Stacks 0AIS**, isomorphism invariance: the set-theoretic condition depends on a sheaf
only up to isomorphism. -/
theorem satisfiesSetTheoreticCondition_of_iso {X Y : FppfSheaf B S hS} (e : X ≅ Y)
    (hX : SatisfiesSetTheoreticCondition B S hS X) :
    SatisfiesSetTheoreticCondition B S hS Y := by
  obtain ⟨U, R, hU, hR, ⟨eU⟩, ⟨eR⟩, f, hf, g, hg⟩ := hX
  let := hf
  let := hg
  refine ⟨U, R, hU, hR, ⟨eU⟩, ⟨eR⟩, f ≫ e.hom, inferInstance,
    g ≫ (pullbackCompIso B S hS f e.hom).hom, inferInstance⟩

/-- An affine formal algebraic space is one up to isomorphism: the presentation by affine
thickenings is transported by composing its comparison isomorphism. -/
theorem isAffineFormalAlgebraicSpace_of_iso {X Y : FppfSheaf B S hS} (e : X ≅ Y)
    (hX : IsAffineFormalAlgebraicSpace B S hS X) :
    IsAffineFormalAlgebraicSpace B S hS Y := by
  obtain ⟨hset, I, pre, hne, hdir, D, hD, ⟨eX⟩⟩ := hX
  exact ⟨satisfiesSetTheoreticCondition_of_iso B S hS e hset, I, pre, hne, hdir, D, hD,
    ⟨e.symm ≪≫ eX⟩⟩

/-- A sheaf isomorphic to one with a surjective presentation by affine thickenings has one
too: the presentation is transported by composing its comparison isomorphism. -/
theorem hasSomeSurjectivePresentation_of_iso {X Y : FppfSheaf B S hS} (e : X ≅ Y)
    (hX : HasSomeSurjectivePresentation B S hS X) :
    HasSomeSurjectivePresentation B S hS Y := by
  obtain ⟨hAff, I, pre, hne, hdir, D, hD, ⟨eX⟩, hsurj⟩ := hX
  exact ⟨isAffineFormalAlgebraicSpace_of_iso B S hS e hAff, I, pre, hne, hdir, D, hD,
    ⟨e.symm ≪≫ eX⟩, hsurj⟩

/-- A weakly admissible topological ring presenting a sheaf presents every sheaf isomorphic
to it, by the same diagram of quotients. -/
theorem isPresentingRing_of_iso (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] {X Y : FppfSheaf B S hS} (e : X ≅ Y)
    (hX : IsPresentingRing B S hS A X) : IsPresentingRing B S hS A Y :=
  ⟨hX.1, hX.2.elim fun P ↦ ⟨{ P with colimitIso := e.symm ≪≫ P.colimitIso }⟩⟩

/-- **Stacks 0AID (5)**, isomorphism invariance: an affine formal algebraic space isomorphic
to a Noetherian one is Noetherian. -/
theorem isNoetherian_of_iso {X Y : FppfSheaf B S hS} (e : X ≅ Y)
    (hX : IsNoetherian B S hS X) : IsNoetherian B S hS Y := by
  obtain ⟨hpres, A, instCR, instTS, instTR, instLT, hpr, hN, hA⟩ := hX
  let := instCR
  let := instTS
  let := instTR
  let := instLT
  exact ⟨hasSomeSurjectivePresentation_of_iso B S hS e hpres, A, instCR, instTS, instTR,
    instLT, isPresentingRing_of_iso B S hS A e hpr, hN, hA⟩

/-- **Stacks 0AID (4)**, isomorphism invariance: an affine formal algebraic space isomorphic
to an adic\* one is adic\*. -/
theorem isAdicStar_of_iso {X Y : FppfSheaf B S hS} (e : X ≅ Y)
    (hX : IsAdicStar B S hS X) : IsAdicStar B S hS Y := by
  obtain ⟨hpres, A, instCR, instTS, instTR, instLT, hpr, hA, hI⟩ := hX
  let := instCR
  let := instTS
  let := instTR
  let := instLT
  exact ⟨hasSomeSurjectivePresentation_of_iso B S hS e hpres, A, instCR, instTS, instTR,
    instLT, isPresentingRing_of_iso B S hS A e hpr, hA, hI⟩

/-- **Stacks 0AID (1)**, isomorphism invariance: an affine formal algebraic space isomorphic
to a classical one is classical. -/
theorem isClassical_of_iso {X Y : FppfSheaf B S hS} (e : X ≅ Y)
    (hX : IsClassical B S hS X) : IsClassical B S hS Y := by
  obtain ⟨hpres, A, instCR, instTS, instTR, instLT, hpr, hA⟩ := hX
  let := instCR
  let := instTS
  let := instTR
  let := instLT
  exact ⟨hasSomeSurjectivePresentation_of_iso B S hS e hpres, A, instCR, instTS, instTR,
    instLT, isPresentingRing_of_iso B S hS A e hpr, hA⟩

end Iso

/-! ### The two topologies on an adic completion -/

section Topology

variable {A : Type u} [CommRing A]

/-- The inverse-limit topology on the `I`-adic completion of `A` is the infimum of the
topologies induced from its discrete quotients. -/
private theorem adicCompletionLimitTopology_eq_iInf (I : Ideal A) :
    adicCompletionLimitTopology A I =
      ⨅ n : ℕ, TopologicalSpace.induced
        (fun x : AdicCompletion I A ↦ AdicCompletion.eval I A n x) ⊥ := by
  have h1 : adicCompletionLimitTopology A I =
      TopologicalSpace.induced
        (Subtype.val : AdicCompletion I A → ∀ n : ℕ, A ⧸ (I ^ n • (⊤ : Submodule A A)))
        (⨅ n : ℕ, TopologicalSpace.induced
          (fun h : ∀ n : ℕ, A ⧸ (I ^ n • (⊤ : Submodule A A)) ↦ h n) ⊥) := rfl
  rw [h1, induced_iInf]
  exact iInf_congr fun _ ↦ induced_compose

/-- For a finitely generated ideal `I` the inverse-limit topology on the `I`-adic completion
of `A` is the `I`-adic topology of `A^∧` as an `A`-module: the kernel of the `n`-th projection
is exactly `I ^ n A^∧`. -/
theorem adicCompletionLimitTopology_eq_adicModuleTopology (I : Ideal A) (hI : I.FG) :
    adicCompletionLimitTopology A I = I.adicModuleTopology (AdicCompletion I A) := by
  have hker : ∀ n : ℕ,
      (I ^ n • (⊤ : Submodule A (AdicCompletion I A))) =
        LinearMap.ker (AdicCompletion.eval I A n) := fun _ ↦
    AdicCompletion.pow_smul_top_eq_ker_eval hI
  rw [adicCompletionLimitTopology_eq_iInf I]
  refine Stacks.AdicLimit.iInf_induced_eq_adicModuleTopology I
    (fun n ↦ AdicCompletion.eval I A n) (fun i j hij ↦ ?_) (fun n ↦ ⟨n, (hker n).le⟩)
    (fun k ↦ ⟨k, (hker k).ge⟩)
  rw [← hker i, ← hker j]
  exact Submodule.smul_mono_left (Ideal.pow_le_pow_right hij)

end Topology

/-! ### The adic completion as an object of `WAdm^{Noeth}` for the module topology -/

section ModuleTopology

variable {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG)

include hI

/-- A property of topologies on the `I`-adic completion that holds for the inverse-limit topology
holds for the `I`-adic topology of `A^∧` as an `A`-module. -/
private theorem adicModuleTopology_of_adicCompletionLimitTopology
    {P : TopologicalSpace (AdicCompletion I A) → Prop}
    (h : P (adicCompletionLimitTopology A I)) : P (I.adicModuleTopology (AdicCompletion I A)) :=
  adicCompletionLimitTopology_eq_adicModuleTopology I hI ▸ h

/-- For a finitely generated ideal `I`, the `I`-adic completion of `A` with the `I`-adic topology
of `A^∧` as an `A`-module is a topological ring. -/
theorem isTopologicalRing_adicModuleTopology :
    @IsTopologicalRing (AdicCompletion I A) (I.adicModuleTopology (AdicCompletion I A)) _ :=
  adicModuleTopology_of_adicCompletionLimitTopology I hI
    (P := fun t ↦ @IsTopologicalRing (AdicCompletion I A) t _)
    (isTopologicalRing_adicCompletion A I)

/-- For a finitely generated ideal `I`, the module topology on the `I`-adic completion is
linear. -/
theorem isLinearTopology_adicModuleTopology :
    letI := I.adicModuleTopology (AdicCompletion I A)
    IsLinearTopology (AdicCompletion I A) (AdicCompletion I A) :=
  adicModuleTopology_of_adicCompletionLimitTopology I hI
    (P := fun t ↦ letI := t; IsLinearTopology (AdicCompletion I A) (AdicCompletion I A))
    (isLinearTopology_adicCompletion A I)

/-- For a finitely generated ideal `I`, the `I`-adic completion of `A` with its module topology
is an adic topological ring. -/
theorem isAdic_adicModuleTopology :
    letI := I.adicModuleTopology (AdicCompletion I A)
    letI := isTopologicalRing_adicModuleTopology I hI
    TopologicalRing.IsAdic (AdicCompletion I A) :=
  adicModuleTopology_of_adicCompletionLimitTopology I hI
    (P := fun t ↦ ∀ h₁ : @IsTopologicalRing (AdicCompletion I A) t _,
      @TopologicalRing.IsAdic (AdicCompletion I A) _ t h₁)
    (fun _ ↦ isAdic_adicCompletion (A := A) I hI) _

/-- For a finitely generated ideal `I`, the extension of `I` to the `I`-adic completion is an
ideal of definition for the module topology. -/
theorem isIdealOfDefinition_map_adicModuleTopology :
    letI := I.adicModuleTopology (AdicCompletion I A)
    TopologicalRing.IsIdealOfDefinition (I.map (algebraMap A (AdicCompletion I A))) :=
  adicModuleTopology_of_adicCompletionLimitTopology I hI
    (P := fun t ↦ @TopologicalRing.IsIdealOfDefinition (AdicCompletion I A) _ t
      (I.map (algebraMap A (AdicCompletion I A))))
    (isIdealOfDefinition_map_adicCompletion I hI)

/-- For a finitely generated ideal `I`, the extension of `I` to the `I`-adic completion defines
the module topology. -/
theorem isAdic_map_adicModuleTopology :
    letI := I.adicModuleTopology (AdicCompletion I A)
    _root_.IsAdic (I.map (algebraMap A (AdicCompletion I A))) :=
  adicModuleTopology_of_adicCompletionLimitTopology I hI
    (P := fun t ↦ letI := t; _root_.IsAdic (I.map (algebraMap A (AdicCompletion I A))))
    (isAdic_map_adicCompletion I hI)

end ModuleTopology

/-! ### Transporting the quotient system of Stacks 0GXX -/

section Transport

attribute [local instance] sheaf_hasColimits

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A : Type u} [CommRing A] (hA : B.Contains (Spec (.of A))) (f : Spec (.of A) ⟶ S)

private theorem exists_quotientSystem_of_topology_eq (I : Ideal A)
    {t : TopologicalSpace (AdicCompletion I A)}
    (ht : adicCompletionLimitTopology A I = t) :
    ∃ D : @QuotientSystem B S hS (AdicCompletion I A) _ t,
      (∀ J : { K : Ideal (AdicCompletion I A) //
          @TopologicalRing.IsWeakIdealOfDefinition _ _ t K },
        D.overS J = Spec.map (CommRingCat.ofHom
          ((Ideal.Quotient.mk J.1).comp (algebraMap A (AdicCompletion I A)))) ≫ f) ∧
      Nonempty (completionAlongIdeal B S hS f hA I ≅
        @formalSpectrum B S hS (AdicCompletion I A) _ t D) := by
  subst ht
  refine ⟨adicCompletionQuotientSystem B S hS f hA I, fun J ↦ ?_,
    ⟨completionAlongIdealIsoFormalSpectrum B S hS f hA I⟩⟩
  show Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A (AdicCompletion I A))) ≫ f = _
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

/-- For a finitely generated ideal `I`, the completion of `Spec A` along the closed subscheme
of `I` is the completion of `Spec A` along the closed subset `V(I)`: both are `Spf (A^∧)` for
the `I`-adic completion of `A`, by **Stacks 0GXX** and **Stacks 0GBA (2)**. -/
theorem nonempty_completionAlongIdealIsoCompletionSheaf (I : Ideal A) (hI : I.FG) :
    Nonempty (completionAlongIdeal B S hS f hA I ≅
      Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS hA f))
        (zeroLocusPoints B S hS hA f I)) := by
  let : TopologicalSpace (AdicCompletion I A) := I.adicModuleTopology (AdicCompletion I A)
  obtain ⟨D, hD, ⟨e⟩⟩ := exists_quotientSystem_of_topology_eq B S hS hA f I
    (adicCompletionLimitTopology_eq_adicModuleTopology I hI)
  let := isIso_completionComparison B S hS hA f I hI D hD
  exact ⟨e ≪≫ asIso (completionComparison B S hS hA f I D hD)⟩

include hA in
/-- For a finitely generated ideal `I`, the `I`-adic completion of `A`, with the `I`-adic topology
of `A^∧` as an `A`-module, is presented over `S` by a quotient system whose structure morphisms
are induced by `Spec A ⟶ S`: this is the input of the comparison morphism of Stacks 0GBA (2),
`AlgebraicGeometry.FormalSpace.completionComparison`. -/
theorem exists_adicQuotientSystem_compatible (I : Ideal A) (hI : I.FG) :
    ∃ D : AdicQuotientSystem B S hS I, QuotientSystemCompatible B S hS f I D := by
  obtain ⟨D, hD, -⟩ := exists_quotientSystem_of_topology_eq B S hS hA f I
    (adicCompletionLimitTopology_eq_adicModuleTopology I hI)
  exact ⟨D, hD⟩

end Transport

/-! ### Cutting out a closed subset of an affine scheme by an ideal -/

section ClosedSubset

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A : Type u} [CommRing A] (hA : B.Contains (Spec (.of A))) (f : Spec (.of A) ⟶ S)

private theorem continuous_pointsToScheme (U : BigFppfOver B S hS) :
    @Continuous _ _ (Space.pointTopology B S hS (yoneda.obj U)) _
      (Space.pointsToScheme B S hS U) := by
  rw [continuous_def]
  intro V hV
  rw [Space.isOpen_pointTopology_yoneda_iff_isOpen_image,
    Set.image_preimage_eq _ (Space.surjective_pointsToScheme B S hS U)]
  exact hV

/-- The points of `Spec A` supported on `V(I)` are exactly the preimage of `V(I)` under the
comparison bijection of Stacks 03BV. -/
theorem zeroLocusPoints_eq_preimage_pointsToScheme (I : Ideal A) :
    zeroLocusPoints B S hS hA f I =
      Space.pointsToScheme B S hS (affineOver B S hS hA f) ⁻¹'
        PrimeSpectrum.zeroLocus (I : Set A) := by
  ext x
  obtain ⟨p, rfl⟩ := Quot.exists_rep x
  refine ⟨fun h ↦ h p rfl, fun h q hq ↦ ?_⟩
  have hqp : Space.pointsToScheme B S hS (affineOver B S hS hA f)
      (q.class B S hS (yoneda.obj (affineOver B S hS hA f))) =
      Space.pointsToScheme B S hS (affineOver B S hS hA f)
        (Quot.mk _ p) := congrArg _ hq
  rw [Space.pointsToScheme_class] at hqp
  rw [hqp]
  exact h

/-- A closed set of points of the presheaf represented by `Spec A` is the zero locus of an
ideal, namely the vanishing ideal of the corresponding closed subset of `Spec A`. -/
theorem exists_zeroLocusPoints_eq_of_isClosed
    (T : Set (Space.points B S hS (yoneda.obj (affineOver B S hS hA f))))
    (hT : @IsClosed _
      (Space.pointTopology B S hS (yoneda.obj (affineOver B S hS hA f))) T) :
    ∃ I : Ideal A, T = zeroLocusPoints B S hS hA f I := by
  refine ⟨PrimeSpectrum.vanishingIdeal
    (Space.pointsToScheme B S hS (affineOver B S hS hA f) '' T), ?_⟩
  have himg : IsClosed (Space.pointsToScheme B S hS (affineOver B S hS hA f) '' T) :=
    (Space.isClosed_pointTopology_yoneda_iff_isClosed_image B S hS
      (affineOver B S hS hA f) T).mp hT
  have hZ : PrimeSpectrum.zeroLocus
      ((PrimeSpectrum.vanishingIdeal
        (Space.pointsToScheme B S hS (affineOver B S hS hA f) '' T) : Ideal A) : Set A) =
      Space.pointsToScheme B S hS (affineOver B S hS hA f) '' T := by
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    exact himg.closure_eq
  rw [zeroLocusPoints_eq_preimage_pointsToScheme, hZ,
    Set.preimage_image_eq T (Space.injective_pointsToScheme B S hS _)]

/-- A closed set of points of the presheaf represented by `Spec A` whose complement is
quasi-compact is the zero locus of a *finitely generated* ideal: the complement corresponds to
a quasi-compact open subset of `Spec A`. -/
theorem exists_fg_zeroLocusPoints_eq_of_isClosed_of_isCompact_compl
    (T : Set (Space.points B S hS (yoneda.obj (affineOver B S hS hA f))))
    (hT : @IsClosed _
      (Space.pointTopology B S hS (yoneda.obj (affineOver B S hS hA f))) T)
    (hqc : @IsCompact _
      (Space.pointTopology B S hS (yoneda.obj (affineOver B S hS hA f))) Tᶜ) :
    ∃ I : Ideal A, I.FG ∧ T = zeroLocusPoints B S hS hA f I := by
  let : TopologicalSpace (Space.points B S hS (yoneda.obj (affineOver B S hS hA f))) :=
    Space.pointTopology B S hS (yoneda.obj (affineOver B S hS hA f))
  have hopen : IsOpen (Space.pointsToScheme B S hS (affineOver B S hS hA f) '' Tᶜ) :=
    (Space.isOpen_pointTopology_yoneda_iff_isOpen_image B S hS
      (affineOver B S hS hA f) Tᶜ).mp hT.isOpen_compl
  have hcpt : IsCompact (Space.pointsToScheme B S hS (affineOver B S hS hA f) '' Tᶜ) :=
    hqc.image (continuous_pointsToScheme B S hS (affineOver B S hS hA f))
  obtain ⟨I, hIfg, hI⟩ := PrimeSpectrum.isCompact_isOpen_iff_ideal.mp ⟨hcpt, hopen⟩
  refine ⟨I, hIfg, ?_⟩
  rw [zeroLocusPoints_eq_preimage_pointsToScheme]
  refine Set.ext fun x ↦ ?_
  have h := Set.ext_iff.mp hI (Space.pointsToScheme B S hS (affineOver B S hS hA f) x)
  refine ⟨fun hx ↦ by_contra fun hn ↦ ?_, fun hx ↦ by_contra fun hn ↦ ?_⟩
  · obtain ⟨y, hy, hxy⟩ := h.mp hn
    exact hy (Space.injective_pointsToScheme B S hS _ hxy ▸ hx)
  · exact h.mpr (Set.mem_image_of_mem _ hn) hx

/-! ### The two clauses of Stacks 0GBA -/

/-- **Stacks 0GBA (1).** Let `X = Spec A` be an affine scheme over `S` in the big fppf site and
let `T ⊆ |X|` be a closed subset whose complement is quasi-compact, that is a constructible
closed subset. Then the completion `X_{/T}` is an adic\* affine formal algebraic space. -/
@[stacks 0GBA "adic*"]
theorem isAdicStar_completionSheaf
    (T : Set (Space.points B S hS (yoneda.obj (affineOver B S hS hA f))))
    (hT : @IsClosed _
      (Space.pointTopology B S hS (yoneda.obj (affineOver B S hS hA f))) T)
    (hqc : @IsCompact _
      (Space.pointTopology B S hS (yoneda.obj (affineOver B S hS hA f))) Tᶜ) :
    IsAdicStar B S hS
      (Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS hA f)) T) := by
  obtain ⟨I, hIfg, rfl⟩ :=
    exists_fg_zeroLocusPoints_eq_of_isClosed_of_isCompact_compl B S hS hA f T hT hqc
  obtain ⟨e⟩ := nonempty_completionAlongIdealIsoCompletionSheaf B S hS hA f I hIfg
  exact isAdicStar_of_iso B S hS e (isAdicStar_completionAlongIdeal B S hS f hA I hIfg)

/-- **Stacks 0GBA (3).** Let `X = Spec A` be a Noetherian affine scheme over `S` in the big
fppf site and let `T ⊆ |X|` be a closed subset. Then the completion `X_{/T}` is a Noetherian
affine formal algebraic space. -/
@[stacks 0GBA "Noetherian"]
theorem isNoetherian_completionSheaf [IsNoetherianRing A]
    (T : Set (Space.points B S hS (yoneda.obj (affineOver B S hS hA f))))
    (hT : @IsClosed _
      (Space.pointTopology B S hS (yoneda.obj (affineOver B S hS hA f))) T) :
    IsNoetherian B S hS
      (Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS hA f)) T) := by
  obtain ⟨I, rfl⟩ := exists_zeroLocusPoints_eq_of_isClosed B S hS hA f T hT
  obtain ⟨e⟩ :=
    nonempty_completionAlongIdealIsoCompletionSheaf B S hS hA f I I.fg_of_isNoetherianRing
  exact isNoetherian_of_iso B S hS e (isNoetherian_completionAlongIdeal B S hS f hA I)

end ClosedSubset

end AlgebraicGeometry.FormalSpace

end
