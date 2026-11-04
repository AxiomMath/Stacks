module

public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.BaseChangeJointApproximation
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.BaseChangeSpecChart
public import StacksFrontier.RingTheory.Flat.ElementaryEtaleLocalizationComp

/-!
# The étale algebra of a neighbourhood of a base change, read over the tensor product

This is the third step of the proof of Stacks Tag 0CAW: the étale algebra the first two steps
produce, read as an étale algebra **over `B ⊗_{C, σ} R^∧` itself**.

Step one of that proof
(`StacksDraft.ArtinApproximation.exists_elementaryEtaleNeighborhood_algebraization`) replaces the
given `φ : 𝒪_{X, x} → 𝒪^∧_{Y_σ, y_σ}` by an elementary étale neighbourhood `(W, w)` of
`(Y_σ, y_σ)` together with a morphism `F : W ⟶ X`, and step two
(`StacksDraft.ArtinApproximation.exists_isAffineOpen_etale_appLE`) reads that neighbourhood as an
étale **ring** map on an affine chart: `Γ(Y_σ, U_Z) → Γ(W, U_W)`. But `Γ(Y_σ, U_Z)` is a ring of
sections, and the next step of the source's proof — descending the étale algebra along the
presentation of `B ⊗_{C, σ} R^∧` as a filtered colimit of the `B ⊗_C R'`
(`Stacks.Smoothing.exists_colimitPresentation_tensorProduct_of_indSmooth` feeding
`Algebra.Etale.exists_etale_stage_of_isColimit_of_smallCategory`) — is a statement about the
tensor product. So the chart ring has to be identified with the tensor product first, and the
étale algebra carried across. That identification is
`AlgebraicGeometry.exists_ringEquiv_tensorProduct_sections_pullback_fst`, and this file performs
the transport.

## Main results

* `Ideal.ResidueField.map_bijective_comp_ringEquiv`: bijectivity of a residue-field extension is
  unchanged by precomposing with a ring isomorphism.
* `StacksDraft.ArtinApproximation.exists_etale_tensorProduct_chart`: **step three.** For an étale
  `p : W ⟶ Y ×_T Spec Λ` which is residually trivial at `w`, a morphism `F : W ⟶ X`, and affine
  charts `W_T` of `T` and `V_Y` of `Y` around the images of a point `y_σ` lying over the closed
  point of `Spec Λ`, there is an affine chart `U_W ∋ w` of `W` and a ring map
  `ι : Λ ⊗_{Γ(T, W_T)} Γ(Y, V_Y) → Γ(W, U_W)` which is the two restriction maps on the two
  tensor factors, is étale, is residually trivial at the prime of `w`, exhibits `𝒪_{W, w}` as the
  localization of `Γ(W, U_W)` there, and receives the restriction of `F` on sections. Read at
  `Λ = 𝒪^∧_{S, s}` this is the source's "there exists an étale ring map `B ⊗_{C, σ} R^∧ → B'`
  inducing an isomorphism of residue fields and an `R`-algebra map `A → B'`", with
  `B' = Γ(W, U_W)`.
* `StacksDraft.ArtinApproximation.exists_etale_tensorProduct_chart_comm`: the same statement with
  the two tensor factors exchanged, so that the étale ring map is one out of
  `Γ(Y, V_Y) ⊗_{Γ(T, W_T)} Λ`. This is the order in which
  `Stacks.Smoothing.exists_smooth_stage_etale_map_tensorProduct_of_indSmooth`, the next step of
  the source's proof, consumes the étale algebra.

## Implementation notes

*What is and is not proved.* This is a step of the proof of Tag 0CAW, not one of its clauses, and
nothing here is registered for it. Clauses (4) and (5) of Tag 0CAW are **not** proved by it. Of
the remaining steps of the source's proof, the factorization `C → R' → R^∧` through a smooth
`R`-algebra is `Stacks.Smoothing.exists_colimitPresentation_smooth_of_indSmooth`, in the stronger
form of a colimit presentation, and the descent of the étale algebra of this file *together with
the map* `A → B'` to such a stage is
`Stacks.Smoothing.exists_smooth_stage_etale_map_tensorProduct_of_indSmooth`; the ind-smoothness
of `R^∧` over the chart ring `R` that the descent consumes — the G-ring hypothesis of Tag 0CAW
being on `R_𝔭` and not on `R` — is
`Stacks.Smoothing.indSmooth_adicCompletion_maximalIdeal_of_isLocalization`. The final
application of Tag 0CAU, in the ring-level form
`StacksDraft.ArtinApproximation.exists_etaleApproximation`, to `R' → R^∧` rather than to
`C → R^∧`, is now carried out as
`StacksDraft.ArtinApproximation.exists_etaleApproximation_of_ringHom_completion`, which produces
the `D` of the source — étale over `R` at a prime over `𝔭` with the same residue field, with an
`R`-algebra map `R' → D` whose composite into `D^∧ = R^∧` agrees with `ρ` modulo `𝔪^N`. The
*machinery* of the globalization — the passage from an étale algebra over an affine chart of a
scheme, with a prime over the chart prime, to an elementary étale neighbourhood of that scheme,
together with the morphism to a second scheme that a ring map on a chart of it determines, and
the identification of the neighbourhood's map of local rings with `Localization.localRingHom` —
is available as `AlgebraicGeometry.IsAffineOpen.etaleNeighborhoodOfChart` and its companions
(`StacksFrontier/AlgebraicGeometry/Morphisms/EtaleNeighbourhood/ChartEtaleNeighborhood.lean`); it is
stated for an arbitrary scheme and point, so it serves the `V` side at `(S, s)` and the `W` side
at `(Y ×_{T, τ} V, (y, v))` alike. What is **not** carried out is the *assembly* at this tag's
own data: the composition of steps one to six above, which is what actually hands that machinery
the ring `D` and the ring `B'' ⊗_{R'} D` together with their primes, and in particular the point
`(y, v)` of `Y ×_{T, τ} V` with its two projection identities; and the chase of clause (5)
through the replacement of `B'` by the base change of `B''`. Note that the `D` has to be built
from the *stage* `R'` and not from `C`: a `V` and `τ` chosen without reference to `φ` can make
clause (5) unsatisfiable, which is why the scheme-level
`StacksDraft.ArtinApproximation.exists_elementaryEtaleNeighborhood_baseApproximation` — 0CAU at
`C → R^∧` — is not the step that finishes the tag.

*What clause (4) actually asks for, and what of it is available.* The source sets
`W = Spec(B ⊗_C D)` *after* the replacement of `C` by `R'` and of `B` by `B''`, so in its own
notation `W` is literally `Y ×_{T, τ} V` and clause (4) is the identity neighbourhood. Undone,
the replacement having replaced `Y` by `Spec B''` and `T` by `Spec R'`, the obligation is that

  `Spec(B'' ⊗_{R'} D) ⟶ Spec(B ⊗_C D)` is an elementary étale neighbourhood at `w`,

`B'' ⊗_{R'} D` being the base change `(B ⊗_C D) ⊗_{B ⊗_C R'} B''` of the descended étale algebra
along `B ⊗_C R' → B ⊗_C D`. The cancellation to the source's own name for the ring **needs no new
declaration**: `Stacks.Etale.ColimitSpreadOut.isPushout_tensorProduct`
(`StacksFrontier/RingTheory/Etale/ColimitBaseChange.lean`) read at `R := C`, `S := B`, `B := R'`,
`C := D` — with exactly the algebra structure
`Algebra.TensorProduct.map (AlgHom.id C B) (IsScalarTower.toAlgHom C R' D)` that the descent step
supplies — gives `Algebra.IsPushout R' (B ⊗_C R') D (B ⊗_C D)`, and
`Algebra.IsPushout.cancelBaseChangeAlg` applied to its `Algebra.IsPushout.symm` is then
`(B ⊗_C D) ⊗_{B ⊗_C R'} B'' ≃ₐ[D] D ⊗_{R'} B''`. Anything stated separately for it would
duplicate that lemma. Of the two halves of that obligation:

* *Étaleness is free.* With the algebra structure `B ⊗_C R' → B ⊗_C D` given as
  `Algebra.TensorProduct.map (AlgHom.id C B) (IsScalarTower.toAlgHom C R' D)`, the instance
  `Algebra.Etale (B ⊗_C D) ((B ⊗_C D) ⊗_{B ⊗_C R'} B'')` is `infer_instance` from Mathlib's
  `Algebra.Etale.baseChange`. No declaration is added for it here; one would duplicate that
  instance.
* *Residual triviality is available, both halves.* Given a prime of `B''` over the prime of
  `B ⊗_C R'` with trivial residue extension, triviality at a prime of the base change over the
  prime of `B ⊗_C D` is
  `Ideal.exists_isPrime_comap_eq_and_residueField_map_bijective_tensorProduct`
  (`StacksFrontier/RingTheory/Flat/ElementaryEtaleBaseChange.lean`), which produces the prime of `W`
  as well; and the prime of `B''` it consumes is
  `Ideal.exists_isPrime_comap_eq_and_residueField_map_bijective_of_descent_algEquiv`
  (`StacksFrontier/RingTheory/Flat/ElementaryEtaleStageDescent.lean`), the two composed being
  `Ideal.exists_isPrime_comap_eq_and_residueField_map_bijective_baseChange_of_descent`.

  *What that took, and what it did not.* The prime of `B''` is simply the contraction of the prime
  of `B'`; the whole question is whether its residue extension over `B ⊗_C R'` is trivial, and
  **it is, with no enlargement of the stage `R'`,** because
  `κ(𝔭_{B ⊗_C R'}) → κ(𝔭_{B ⊗_C Λ})` is *already* bijective:
  `Ideal.ResidueField.map_bijective_tensorProduct_map_id` derives that from residual triviality of
  `ρ : R' → Λ` alone, and `ρ` is residually trivial at `𝔪_Λ` because `R → R' → Λ` factors the
  residually trivial `R → Λ = R^∧` (`Ideal.ResidueField.map_bijective_of_comp_bijective`, applied
  to `κ(𝔭_R) = κ(𝔪_{R^∧})`). Then `κ(𝔭_{B ⊗_C R'}) ⊆ κ(𝔭_{B''}) ⊆ κ(𝔭_{B'}) = κ(𝔭_{B ⊗_C Λ})`
  with the two ends equal, so every inclusion is an equality.

  This does **not** contradict the counterexample recorded here before: with `E = B ⊗_C R'` a
  field `k`, `B ⊗_C Λ` a field `K ⊇ k(√a) ⊋ k` and `B'' = k(√a)`, the base change
  `B' = K ⊗_k k(√a) ≅ K × K` is residually trivial over `K` at either prime while
  `κ(𝔭_{B''}) = k(√a) ≠ k`. That is a correct proof that the datum does **not** follow from the
  descent square together with residual triviality on the `Λ` side; it has `κ(𝔭_E) = k ⊊ K`, so
  the extra hypothesis used above — `κ(𝔭_{R'}) = κ(𝔪_Λ)`, which forces
  `κ(𝔭_E) = κ(𝔭_{B ⊗_C Λ})` — fails for it. What closes the gap is that hypothesis, which the
  actual data of Tag 0CAW supplies and an abstract descent square does not. No later stage of the
  colimit presentation, and no filtered colimit of residue fields, is needed.

  The obligation that remains before anything can be registered for Tag 0CAW on clause (4)'s
  account is therefore not this datum but the *assembly*. Of that assembly, `D` is provided by
  `StacksDraft.ArtinApproximation.exists_etaleApproximation_of_ringHom_completion` and the
  cancellation is proved as recorded above, and the globalization machinery is available as
  `AlgebraicGeometry.IsAffineOpen.etaleNeighborhoodOfChart` and its companions; what is still
  missing is the *feeding* of that machinery — which needs, among other things, the prime of
  `B ⊗_C D` that the point `w` of the source lives at, and that
  `Ideal.exists_isPrime_comap_eq_and_residueField_map_bijective_baseChange_of_descent` takes as
  its input `qF` rather than producing — and clause (5).

*What clause (5) still needs.* The identification `D^∧ = R^∧` that the source's congruence is
read through is now available: `D` is an étale extension of the chart ring `R` at a prime over
`𝔭` with the same residue field, and for such data the comparison map of completed local rings
is bijective by
`StacksDraft.ArtinApproximation.bijective_completionComparison`
(`StacksFrontier/AlgebraicGeometry/Morphisms/EtaleNeighbourhood/CompletionComparisonEtale.lean`),
which is `bijective_localCompletionComparison` with the base no longer local — `R` is a chart
ring and `𝔭` a prime of it, not a maximal ideal. What remains of clause (5) is the chase of the
congruence through the replacement of `B'` by the base change of `B''`, and the globalization.

*Why the two tensor factors are pinned down.* Without them the conclusion would be the existence
of *some* étale ring map out of *some* ring isomorphic to the tensor product, which says nothing:
the whole point is that the `Λ`-algebra and the `Γ(Y, V_Y)`-algebra structures of `Γ(W, U_W)` are
the geometric ones. So `ι (l ⊗ 1)` and `ι (1 ⊗ s)` are computed, as the restrictions on sections
of `p ≫ pr₂` and of `p ≫ pr₁`; the first is read through
`AlgebraicGeometry.Scheme.ΓSpecIso`, since `Λ` is not literally `Γ(Spec Λ, ⊤)`.

*Why the prime is produced rather than asked for.* The source of the residue field extension is
the prime of the tensor product contracted from the prime of `w`. Stating it as the literal
`comap` would force the ideal appearing in the `Ideal.ResidueField` *type* to be rewritten during
the proof; producing it existentially, with the equation to the `comap` as data, keeps every
rewrite outside a type.

*The order of the tensor factors* is `Λ ⊗ Γ(Y, V_Y)`, inherited from
`AlgebraicGeometry.sectionsTensorEquiv`, which puts the base-change factor on the left. The
descent step of the source's proof wants the other order, `B ⊗_C Λ`, so
`exists_etale_tensorProduct_chart_comm` restates the conclusion through
`Algebra.TensorProduct.comm`. That restatement has no content of its own: étaleness crosses a
ring isomorphism by `RingHom.Etale.of_bijective` and composition, the residue field extension by
`Ideal.ResidueField.map_bijective_comp_ringEquiv` above, and the localization of the stalk does
not mention the tensor product at all.

## References

* [Stacks Project, Tag 0CAW](https://stacks.math.columbia.edu/tag/0CAW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing TensorProduct

universe u

/-- **Bijectivity of a residue field extension is unchanged by precomposing with a ring
isomorphism.** If `f : B → C` carries the prime `J` of `B` back from the prime `K` of `C` with
bijective residue field extension, and `χ : A ≃+* B` carries the prime `I` of `A` back from `J`,
then `f ∘ χ` carries `I` back from `K` with bijective residue field extension.

The composite of the two residue field extensions is the residue field extension of the
composite (`Ideal.ResidueField.map_comp`), and an isomorphism is surjective, hence surjective on
stalks, so its own residue field extension is bijective
(`RingHom.SurjectiveOnStalks.residueFieldMap_bijective`). -/
theorem Ideal.ResidueField.map_bijective_comp_ringEquiv {A B C : Type*} [CommRing A] [CommRing B]
    [CommRing C] (χ : A ≃+* B) {I : Ideal A} [I.IsPrime] {J : Ideal B} [J.IsPrime] {K : Ideal C}
    [K.IsPrime] (f : B →+* C) (hIJ : I = J.comap (χ : A →+* B)) (hJK : J = K.comap f)
    (hbij : Function.Bijective (Ideal.ResidueField.map J K f hJK))
    (hIK : I = K.comap (f.comp (χ : A →+* B))) :
    Function.Bijective (Ideal.ResidueField.map I K (f.comp (χ : A →+* B)) hIK) := by
  rw [← Ideal.ResidueField.map_comp I J K (χ : A →+* B) f hIJ hJK]
  exact hbij.comp (χ.surjectiveOnStalks.residueFieldMap_bijective _ _ hIJ)

namespace StacksDraft.ArtinApproximation

attribute [local instance] PrimeSpectrum.isPrime

/-- Precomposing an étale ring map with a ring isomorphism keeps it étale, and keeps the residue
field extension at the contracted prime bijective. -/
private theorem etale_bijective_comp_ringEquiv {A B C : Type u} [CommRing A] [CommRing B]
    [CommRing C] (χ : A ≃+* B) {f : B →+* C} (hf : f.Etale) {J : Ideal B} [J.IsPrime]
    {K : Ideal C} [K.IsPrime] (hJK : J = K.comap f)
    (hbij : Function.Bijective (Ideal.ResidueField.map J K f hJK)) :
    (f.comp (χ : A →+* B)).Etale ∧
      ∃ hIK : J.comap (χ : A →+* B) = K.comap (f.comp (χ : A →+* B)),
        Function.Bijective (Ideal.ResidueField.map (J.comap (χ : A →+* B)) K
          (f.comp (χ : A →+* B)) hIK) := by
  have hIK : J.comap (χ : A →+* B) = K.comap (f.comp (χ : A →+* B)) := by
    rw [hJK]; exact Ideal.comap_comap _ _
  have hχ : (χ : A →+* B).Etale := RingHom.Etale.of_bijective χ.bijective
  exact ⟨RingHom.Etale.stableUnderComposition _ _ hχ hf,
    hIK, Ideal.ResidueField.map_bijective_comp_ringEquiv χ f rfl hJK hbij hIK⟩

/-- **Step three of the proof of Stacks Tag 0CAW: the étale algebra of an étale neighbourhood of a
base change, read over the tensor product.** Let `g : Y ⟶ T` be a morphism of schemes, let
`b : Spec Λ ⟶ T` with `Λ` a local ring, let `p : W ⟶ Y ×_T Spec Λ` be étale with
`IsIso (p.residueFieldMap w)` at a point `w` over a point `y_σ`, and let `F : W ⟶ X` carry `w` to
`x`. Choose an affine open `W_T` of `T` containing the image of the closed point of `Spec Λ`, an
affine open `V_Y` of `Y` over `W_T` containing the image of `y_σ`, and any open `U_X ∋ x` of `X`,
and let `Λ` and `Γ(Y, V_Y)` carry the `Γ(T, W_T)`-algebra structures the two restriction maps on
sections give them. Then there are an affine open `U_W ∋ w` of `W` inside `F ⁻¹ᵁ U_X` and a ring
map

`ι : Λ ⊗_{Γ(T, W_T)} Γ(Y, V_Y) → Γ(W, U_W)`

such that

* `ι` is the restriction map on sections of `p ≫ pr₂` on the left factor and of `p ≫ pr₁` on the
  right factor;
* `ι` is **étale**;
* the prime of `w` contracts along `ι` to a prime whose residue field extension is **bijective**;
* `𝒪_{W, w}` is the **localization** of `Γ(W, U_W)` at the prime of `w`, by an isomorphism
  carrying germs to the canonical maps and carrying the map of local rings induced by `F` to the
  localization of the restriction map of `F` on sections.

Read at `Λ = 𝒪^∧_{S, s}`, with `b` the morphism `σ` determines, this is the source's first
display: "there exists an étale ring map `B ⊗_{C, σ} R^∧ → B'` inducing an isomorphism
`κ(𝔭_{B ⊗_{C, σ} R^∧}) → κ(𝔭_{B'})` and an `R`-algebra map `A → B'`", with `C = Γ(T, W_T)`,
`B = Γ(Y, V_Y)`, `A = Γ(X, U_X)` and `B' = Γ(W, U_W)`. The approximation of `φ` itself is not
restated: it is already carried by
`StacksDraft.ArtinApproximation.exists_elementaryEtaleNeighborhood_algebraization`, which is what
produces `p` and `F`.

The hypothesis `ht` that `W_T` contains the image of the closed point is implied by `hy` and
`hVYW`, since `g (pr₁ y_σ) = b (pr₂ y_σ)` and `pr₂ y_σ` is the closed point in the application;
it is taken as data because it is what the `Γ(T, W_T)`-algebra structure of `Λ` is stated
through, and a caller holding `pr₂ y_σ = closedPoint Λ` discharges it in one line.

Nothing here is registered for Tag 0CAW, and clauses (4) and (5) of that tag are not proved by
it; see the module docstring. -/
theorem exists_etale_tensorProduct_chart
    {T X Y W : Scheme.{u}} (g : Y ⟶ T) {Λ : CommRingCat.{u}} [IsLocalRing Λ] (b : Spec Λ ⟶ T)
    (p : W ⟶ (pullback g b : Scheme.{u})) [Etale p] (F : W ⟶ X)
    (w : W) {yσ : (pullback g b : Scheme.{u})} (hz : p w = yσ)
    (hres : IsIso (p.residueFieldMap w))
    {x : X} (hx : F w = x) {UX : X.Opens} (hxU : x ∈ UX)
    {WT : T.Opens} (hWT : IsAffineOpen WT) (ht : b (closedPoint Λ) ∈ WT)
    {VY : Y.Opens} (hVY : IsAffineOpen VY) (hVYW : VY ≤ g ⁻¹ᵁ WT)
    (hy : pullback.fst g b yσ ∈ VY)
    [Algebra Γ(T, WT) Λ] [Algebra Γ(T, WT) Γ(Y, VY)]
    (hΛ : ∀ t : Γ(T, WT), algebraMap Γ(T, WT) Λ t =
      (Scheme.ΓSpecIso Λ).hom.hom
        ((b.appLE WT ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem b ht).ge).hom t))
    (hB : ∀ t : Γ(T, WT),
      algebraMap Γ(T, WT) Γ(Y, VY) t = (g.appLE WT VY hVYW).hom t) :
    ∃ (UW : W.Opens) (hUW : IsAffineOpen UW) (hw : w ∈ UW) (hWX : UW ≤ F ⁻¹ᵁ UX)
      (hWY : UW ≤ (p ≫ pullback.fst g b) ⁻¹ᵁ VY)
      (ι : Λ ⊗[Γ(T, WT)] Γ(Y, VY) →+* Γ(W, UW)),
      (∀ l : Λ, ι (l ⊗ₜ 1) =
          ((p ≫ pullback.snd g b).appLE ⊤ UW le_top).hom
            ((Scheme.ΓSpecIso Λ).inv.hom l)) ∧
        (∀ s : Γ(Y, VY), ι (1 ⊗ₜ s) = ((p ≫ pullback.fst g b).appLE VY UW hWY).hom s) ∧
          ι.Etale ∧
          ∃ (P : Ideal (Λ ⊗[Γ(T, WT)] Γ(Y, VY))) (_ : P.IsPrime)
            (hP : P = (hUW.primeIdealOf ⟨w, hw⟩).asIdeal.comap ι),
            Function.Bijective
                (Ideal.ResidueField.map P (hUW.primeIdealOf ⟨w, hw⟩).asIdeal ι hP) ∧
              ∃ e : W.presheaf.stalk w ≃+*
                  Localization.AtPrime (hUW.primeIdealOf ⟨w, hw⟩).asIdeal,
                (∀ c : Γ(W, UW), e ((W.presheaf.germ UW w hw).hom c) =
                    algebraMap Γ(W, UW)
                      (Localization.AtPrime (hUW.primeIdealOf ⟨w, hw⟩).asIdeal) c) ∧
                  (∀ a : Γ(X, UX), e (F.stalkHomAt hx ((X.presheaf.germ UX x hxU).hom a)) =
                    algebraMap Γ(W, UW)
                      (Localization.AtPrime (hUW.primeIdealOf ⟨w, hw⟩).asIdeal)
                      ((F.appLE UX UW hWX).hom a)) := by
  have hUZ : IsAffineOpen (pullback.fst g b ⁻¹ᵁ VY) :=
    isAffineOpen_preimage_pullback_fst_of_closedPoint_mem g b hWT ht hVY hVYW
  have hzU : yσ ∈ pullback.fst g b ⁻¹ᵁ VY := hy
  -- The identification of the chart ring with the tensor product, with its two legs.
  obtain ⟨χ, hχl, hχr⟩ :=
    exists_ringEquiv_tensorProduct_sections_pullback_fst g b hWT ht hVY hVYW hΛ hB
  -- Step two, on that chart.
  obtain ⟨UW, hUW, hw, hWZ, hWX, hetale, hcomap, hbij, e, hge, -, hFa⟩ :=
    exists_isAffineOpen_etale_appLE p F w hz hx hres hUZ hzU hxU
  obtain ⟨hE, hcomap', hbij'⟩ := etale_bijective_comp_ringEquiv χ hetale hcomap hbij
  refine ⟨UW, hUW, hw, hWX, hWZ,
    (p.appLE (pullback.fst g b ⁻¹ᵁ VY) UW hWZ).hom.comp
      (χ : Λ ⊗[Γ(T, WT)] Γ(Y, VY) →+* _), fun l => ?_, fun s => ?_, hE,
    (hUZ.primeIdealOf ⟨yσ, hzU⟩).asIdeal.comap (χ : Λ ⊗[Γ(T, WT)] Γ(Y, VY) →+* _),
    Ideal.comap_isPrime _ _, hcomap', ?_, e, hge, hFa⟩
  · -- The left tensor factor: the restriction map on sections of `p ≫ pr₂`.
    have h := congrArg
      (fun φ : Γ(Spec Λ, ⊤) ⟶ Γ(W, UW) => φ.hom ((Scheme.ΓSpecIso Λ).inv.hom l))
      (Scheme.Hom.appLE_comp_appLE p (pullback.snd g b) ⊤ (pullback.fst g b ⁻¹ᵁ VY) UW
        le_top hWZ)
    rw [RingHom.comp_apply, RingEquiv.coe_toRingHom, hχl l, ← h, CommRingCat.hom_comp,
      RingHom.comp_apply]
  · -- The right tensor factor: the restriction map on sections of `p ≫ pr₁`.
    have h := congrArg (fun φ : Γ(Y, VY) ⟶ Γ(W, UW) => φ.hom s)
      (Scheme.Hom.appLE_comp_appLE p (pullback.fst g b) VY (pullback.fst g b ⁻¹ᵁ VY) UW
        le_rfl hWZ)
    rw [RingHom.comp_apply, RingEquiv.coe_toRingHom, hχr s, ← h, CommRingCat.hom_comp,
      RingHom.comp_apply]
  · exact hbij'

/-- **Step three of the proof of Stacks Tag 0CAW, with the tensor factors in the order the descent
step consumes.** This is `StacksDraft.ArtinApproximation.exists_etale_tensorProduct_chart` read
through `Algebra.TensorProduct.comm`, so that the étale ring map is one out of
`Γ(Y, V_Y) ⊗_{Γ(T, W_T)} Λ` rather than out of `Λ ⊗_{Γ(T, W_T)} Γ(Y, V_Y)`. Nothing new is
proved: the order of the factors in the preceding theorem is the one
`AlgebraicGeometry.sectionsTensorEquiv` produces, with the base-change factor on the left, while
`Stacks.Smoothing.exists_smooth_stage_etale_map_tensorProduct_of_indSmooth` — the next step of
the source's proof — asks for an étale algebra over `B ⊗[C] Λ`, with the base-change factor on
the right. So the two legs are exchanged, étaleness is carried across by composition with a
bijection, and the residue field extension by
`Ideal.ResidueField.map_bijective_comp_ringEquiv`.

As with the preceding theorem, nothing here is registered for Tag 0CAW and clauses (4) and (5)
of that tag are not proved by it; see the module docstring. -/
theorem exists_etale_tensorProduct_chart_comm
    {T X Y W : Scheme.{u}} (g : Y ⟶ T) {Λ : CommRingCat.{u}} [IsLocalRing Λ] (b : Spec Λ ⟶ T)
    (p : W ⟶ (pullback g b : Scheme.{u})) [Etale p] (F : W ⟶ X)
    (w : W) {yσ : (pullback g b : Scheme.{u})} (hz : p w = yσ)
    (hres : IsIso (p.residueFieldMap w))
    {x : X} (hx : F w = x) {UX : X.Opens} (hxU : x ∈ UX)
    {WT : T.Opens} (hWT : IsAffineOpen WT) (ht : b (closedPoint Λ) ∈ WT)
    {VY : Y.Opens} (hVY : IsAffineOpen VY) (hVYW : VY ≤ g ⁻¹ᵁ WT)
    (hy : pullback.fst g b yσ ∈ VY)
    [Algebra Γ(T, WT) Λ] [Algebra Γ(T, WT) Γ(Y, VY)]
    (hΛ : ∀ t : Γ(T, WT), algebraMap Γ(T, WT) Λ t =
      (Scheme.ΓSpecIso Λ).hom.hom
        ((b.appLE WT ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem b ht).ge).hom t))
    (hB : ∀ t : Γ(T, WT),
      algebraMap Γ(T, WT) Γ(Y, VY) t = (g.appLE WT VY hVYW).hom t) :
    ∃ (UW : W.Opens) (hUW : IsAffineOpen UW) (hw : w ∈ UW) (hWX : UW ≤ F ⁻¹ᵁ UX)
      (hWY : UW ≤ (p ≫ pullback.fst g b) ⁻¹ᵁ VY)
      (ι : Γ(Y, VY) ⊗[Γ(T, WT)] Λ →+* Γ(W, UW)),
      (∀ l : Λ, ι (1 ⊗ₜ l) =
          ((p ≫ pullback.snd g b).appLE ⊤ UW le_top).hom
            ((Scheme.ΓSpecIso Λ).inv.hom l)) ∧
        (∀ s : Γ(Y, VY), ι (s ⊗ₜ 1) = ((p ≫ pullback.fst g b).appLE VY UW hWY).hom s) ∧
          ι.Etale ∧
          ∃ (P : Ideal (Γ(Y, VY) ⊗[Γ(T, WT)] Λ)) (_ : P.IsPrime)
            (hP : P = (hUW.primeIdealOf ⟨w, hw⟩).asIdeal.comap ι),
            Function.Bijective
                (Ideal.ResidueField.map P (hUW.primeIdealOf ⟨w, hw⟩).asIdeal ι hP) ∧
              ∃ e : W.presheaf.stalk w ≃+*
                  Localization.AtPrime (hUW.primeIdealOf ⟨w, hw⟩).asIdeal,
                (∀ c : Γ(W, UW), e ((W.presheaf.germ UW w hw).hom c) =
                    algebraMap Γ(W, UW)
                      (Localization.AtPrime (hUW.primeIdealOf ⟨w, hw⟩).asIdeal) c) ∧
                  (∀ a : Γ(X, UX), e (F.stalkHomAt hx ((X.presheaf.germ UX x hxU).hom a)) =
                    algebraMap Γ(W, UW)
                      (Localization.AtPrime (hUW.primeIdealOf ⟨w, hw⟩).asIdeal)
                      ((F.appLE UX UW hWX).hom a)) := by
  obtain ⟨UW, hUW, hw, hWX, hWY, ι, hl, hr, hetale, P, hPprime, hP, hbij, e, hge, hFa⟩ :=
    exists_etale_tensorProduct_chart g b p F w hz hres hx hxU hWT ht hVY hVYW hy hΛ hB
  let χ : Γ(Y, VY) ⊗[Γ(T, WT)] Λ ≃+* Λ ⊗[Γ(T, WT)] Γ(Y, VY) :=
    (Algebra.TensorProduct.comm Γ(T, WT) Γ(Y, VY) Λ).toRingEquiv
  have hcomm : ∀ (s : Γ(Y, VY)) (l : Λ), χ (s ⊗ₜ l) = l ⊗ₜ s :=
    fun s l => Algebra.TensorProduct.comm_tmul _ s l
  obtain ⟨hE, hcomap, hbij'⟩ := etale_bijective_comp_ringEquiv χ hetale hP hbij
  refine ⟨UW, hUW, hw, hWX, hWY,
    ι.comp (χ : Γ(Y, VY) ⊗[Γ(T, WT)] Λ →+* Λ ⊗[Γ(T, WT)] Γ(Y, VY)),
    fun l => ?_, fun s => ?_,
    hE, P.comap (χ : Γ(Y, VY) ⊗[Γ(T, WT)] Λ →+* Λ ⊗[Γ(T, WT)] Γ(Y, VY)), inferInstance, hcomap,
    ?_, e, hge, hFa⟩
  · exact (congrArg ι (hcomm 1 l)).trans (hl l)
  · exact (congrArg ι (hcomm s 1)).trans (hr s)
  · exact hbij'

end StacksDraft.ArtinApproximation

end
