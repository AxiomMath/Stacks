module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.ChartIdealSheaf
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.FlatBaseChangeAlgebraization
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.GeneralBaseAssembly

/-!
# Towards the local solution of Stacks 088B over an affine open of the base

`CompletionProper/GeneralBaseAssembly.lean` reduces the whole of the first paragraph of the proof
of [Stacks, Tag 088B] at a general base to a single hypothesis,
`Stacks.Algebraization.HasAffineLocalDirectImageSolution`: over every affine open `V` of the base
there is a morphism of the restricted systems satisfying the restricted characterization with its
levelwise kernels and cokernels annihilated by a power of `𝒦|_V`. Its module docstring names the
three things that stand between that hypothesis and the available ingredients of the source's second
paragraph:

1. the **transport** of the situation over `V` to one over `Spec Γ(V, 𝒪_X)`;
2. the **identification** of the restricted `δ` and `γ_n` with the `δ` and `γ_n` of `π ∣_ V`;
3. the **return of the annihilation** along `B ⟶ B ^∧`.

This file supplies the ideal-sheaf half of 1, the system-level half of 2, and the
commutative-algebra core of 3. `Stacks.Algebraization.HasAffineLocalDirectImageSolution` is
**not** discharged; the module docstring records below exactly what each of the three is still
missing.

## Main results

* `Stacks.Algebraization.comap_adicIdealSheaf_isoSpec` — **the ideal sheaf of the transport.**
  Over an affine open `V ⊆ X` with `B = Γ(X, V)`, the identification
  `Stacks.Algebraization.adicIdealSheaf` of `AlgebraicGeometry.IsAffineOpen.isoSpec` carries
  `J(V) · 𝒪_{Spec B}` to `𝒥|_V`. This is what makes the data over `V` data of the shape the
  second paragraph of the source is stated for: the ideal sheaf on `Spec B` that
  `Stacks.Algebraization.exists_isDirectImageCharacterized_of_adicCompletionPullback` and
  `Stacks.Algebraization.exists_isDirectImageCharacterized_of_adicBaseChangeSquares` use is
  `Stacks.Algebraization.adicIdealSheaf B (𝒥(V))`, and `𝒥|_V` is its inverse image along the
  chart.
* `Stacks.Algebraization.eq_zero_of_one_tmul_eq_zero_adicCompletion` — **the return map of the
  base change is injective on power-torsion modules.** For a Noetherian `B`, an ideal `J ⊆ B` and a
  `J`-power-torsion `B`-module `M`, a section killed by `M ⟶ B ^∧ ⊗_B M` is zero. This is the
  torsion-submodule clause of More on Algebra 05EC,
  `Stacks.Algebraization.exists_primaryComponent_baseChange_equiv_adicCompletion`, read at an
  element.
* `Stacks.Algebraization.idealPow_smul_eq_zero_of_baseChange_adicCompletion` and
  `Stacks.Algebraization.smul_top_eq_bot_of_baseChange_adicCompletion` — **the annihilation of a
  power-torsion module returns along `B ⟶ B ^∧`.** If `𝔞 B ^∧` to the power `t` annihilates
  `B ^∧ ⊗_B M` then `𝔞 ᵗ` annihilates `M`. This is piece 3: the levelwise kernels and cokernels
  of the `α` of Stacks 088B at level `k` are annihilated by `𝒥 ᵏ⁺¹`, hence are `J`-power torsion,
  so the annihilation by a power of `𝒦 B ^∧` that the solution over `Spec B ^∧` carries comes
  back to annihilation by the same power of `𝒦`.

  Without the power-torsion hypothesis the statement is **false**, and that is why the
  hypothesis is there rather than omitted: `B = ℤ`, `J = (p)`, `M = ℤ/q` for a prime `q ≠ p` has
  `B ^∧ ⊗_B M = 0`, annihilated by every ideal, while `M` is annihilated by no power of `(q)` —
  completion along `J` loses the part of `M` supported away from `V(J)`. What rescues the step in
  Stacks 088B is that the modules it is applied to are already `J`-power torsion, each level of a
  coherent adic system being annihilated by a power of `𝒥`.
* `Stacks.Coherent.directImageQuotientRestrictSourceIso_π`,
  `Stacks.Coherent.completedDirectImageRestrictIsoApp`,
  `Stacks.Coherent.completionProjection_comp_completedDirectImageRestrictIsoApp` and
  `Stacks.Coherent.completedDirectImageRestrictIso` — **the completed direct image commutes with
  restriction to an open of the base**, as an isomorphism of *inverse systems*

  `((f_*𝓕) ^∧)|_U ≅ ((f ∣_ U)_*(𝓕|_{f ⁻¹ U})) ^∧`,

  for `f : X ⟶ Y` proper between Noetherian schemes and an open `U ⊆ Y` with `U` and `f ⁻¹ U`
  Noetherian. This is the system-level half of piece 2, and it is what the levelwise comparisons
  the library had did not add up to: the restricted characterization of Stacks 088B is an
  equation between morphisms of systems, and
  `Stacks.Coherent.directImageQuotientRestrictSourceIso` alone identifies the targets of the two
  presentations one level at a time, with no compatibility with the transition maps.

  The naturality costs nothing once the right normalization is in hand: both sides are determined
  by their composites with the restriction of the projection out of `f_*𝓕`, which is an
  epimorphism (`Stacks.Coherent.epi_completionProjection`, and
  `AlgebraicGeometry.Scheme.Modules.restrictFunctor` preserves epimorphisms, being a left
  adjoint), and `Stacks.Algebraization.completionProjection_naturality` normalizes every
  transition map at both ends against that projection.

## What is not here

**Piece 2 is only half done, and that is the obstruction to discharging
`Stacks.Algebraization.HasAffineLocalDirectImageSolution`.** With
`Stacks.Coherent.completedDirectImageRestrictIso` the *target* of the restricted characterization
is identified as a system; what is still missing is the *source* side, an isomorphism of systems

`β' : (π ∣_ V)^*(G|_V) ≅ (𝓕|_{π ⁻¹ V}) ^∧`

restricting `β`, whose level-`n` component is the one
`Stacks.Coherent.directImageComparison_app_restrict_unit` names — the conjugate of `β_n` by
`Stacks.AlgebraicGeometry.AffinePushforward.pullbackRestrictIso` — together with the
transport of the equation itself across the two identifications, which consumes
`Stacks.Coherent.directImageQuotientComparison_restrict` for the `δ` side and
`Stacks.Coherent.directImageComparison_app_restrict_unit` for the `γ_n` side. Neither the
system `β'` nor the transport is here.

Likewise the geometric half of piece 1 is absent: the transport of `π ∣_ V`, of `𝓕|_{π ⁻¹ V}`, of
`G|_V` and of `β|` across `AlgebraicGeometry.IsAffineOpen.isoSpec` to data over `Spec Γ(X, V)`,
which is what puts them in the shape
`Stacks.Algebraization.exists_isDirectImageCharacterized_of_adicBaseChangeSquares` is stated for.
Only the ideal sheaf is transported here.

Piece 3 is supplied only in its commutative-algebra form. Turning it into the sheaf statement
that `Stacks.Algebraization.IsKernelCokernelAnnihilatedByPower` asks for needs, in addition, the
exactness of pullback along the flat `Spec B ^∧ ⟶ Spec B` on the levelwise kernels and cokernels
and the identification of the sections of a pullback with a base change, neither of which is
assembled here.

## Implementation notes

`Stacks.Algebraization.comap_adicIdealSheaf_isoSpec` is
`Stacks.Algebraization.baseIdealSheaf_isoSpec` of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/Completion/Quasicoherent/ChartIdealSheaf.lean`
with the inverse image moved inside by
`Stacks.PuncturedSpectrumPicard.baseIdealSheaf_comap`; the identification of
`Stacks.Algebraization.adicIdealSheaf` with a `baseIdealSheaf` at the identity is the only other
step.

`Stacks.Coherent.directImageQuotientRestrictSourceIso_π` is the step `hS` of the proof of
`Stacks.Coherent.directImageQuotientComparison_restrict`, which that proof keeps inline; it is
stated here because it is what pins the system isomorphism down, and its proof is that `have`
unchanged.

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules _`, agreeing with it only at
default transparency, so the ambient category of a `cokernel`, of `CategoryTheory.Category.assoc`
and of `CategoryTheory.Category.comp_id` is named explicitly with `(C := _)` or `(obj := _)`, and
the composites are assembled in term mode out of `congrArg` rather than by `rw`: on the goals
below `rw [eqToHom_trans]` fails with the usual *not type-correct under the implicit transparency
level*, and the cancellation of `eqToHom` against its inverse is taken from
`CategoryTheory.Iso.inv_hom_id` at `CategoryTheory.eqToIso` instead.

The two Noetherian hypotheses on `U` and on `f ⁻¹ U` are instance binders rather than derived:
an arbitrary open of a Noetherian scheme is locally Noetherian but need not be quasi-compact. At
the affine open of the intended application both hold, `U` being affine and `f ⁻¹ U` proper
over it.

No `stacks` attribute is attached. Nothing here is a statement of the source: the first result is
an identification of two presentations of one ideal sheaf, and the others are More on Algebra
05EC, whose registration is on
`IPowerTorsion.baseChange_equiv_of_quotientMap_bijective`.

## References

* [Stacks Project, Tag 05EC](https://stacks.math.columbia.edu/tag/05EC)
* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry TensorProduct

universe u

namespace Stacks.Algebraization

/-! ### Piece 1: the ideal sheaf of the transport to `Spec Γ(V, 𝒪_X)` -/

section Transport

variable {X : Scheme.{u}} (J : X.IdealSheafData) {V : X.Opens} (hV : IsAffineOpen V)

/-- **The transport of the ideal sheaf to `Spec Γ(X, V)`.** The inverse image along
`AlgebraicGeometry.IsAffineOpen.isoSpec` of the ideal sheaf
`Stacks.Algebraization.adicIdealSheaf Γ(X, V) (𝒥(V))` of `Spec Γ(X, V)` is `𝒥|_V`.

This is the ideal-sheaf half of the transport the local solution of Stacks 088B needs: the second
paragraph of the source works over `Spec B` at the ideal sheaf
`Stacks.Algebraization.adicIdealSheaf B J`, which is the presentation
`Stacks.Algebraization.exists_isDirectImageCharacterized_of_adicCompletionPullback` and
`Stacks.Algebraization.exists_isDirectImageCharacterized_of_adicBaseChangeSquares` are stated in,
and this says that at `B = Γ(X, V)` and `J = 𝒥(V)` that ideal sheaf pulls back to the `𝒥|_V` the
restricted system lives over.

`Stacks.Algebraization.adicIdealSheaf_eq_baseIdealSheaf` presents it as a `baseIdealSheaf` at the
identity, `Stacks.PuncturedSpectrumPicard.baseIdealSheaf_comap` moves the inverse image inside,
and `Stacks.Algebraization.baseIdealSheaf_isoSpec` finishes. -/
public theorem comap_adicIdealSheaf_isoSpec :
    (adicIdealSheaf ↥Γ(X, V) (J.ideal ⟨V, hV⟩)).comap hV.isoSpec.hom = J.comap V.ι := by
  rw [adicIdealSheaf_eq_baseIdealSheaf, Stacks.PuncturedSpectrumPicard.baseIdealSheaf_comap,
    Category.comp_id]
  exact baseIdealSheaf_isoSpec J ⟨V, hV⟩

end Transport

/-! ### Piece 3: the return of an annihilation along `B ⟶ B ^∧` -/

section Return

variable (B : Type u) [CommRing B] [IsNoetherianRing B] (J : Ideal B)
  {M : Type u} [AddCommGroup M] [Module B M]

/-- **The base change to `B ^∧` is injective on a `J`-power-torsion module.** For `B` Noetherian,
`J ⊆ B` an ideal and `M` a `J`-power-torsion `B`-module, an element of `M` whose image
`1 ⊗ x` in `B ^∧ ⊗_B M` vanishes is zero.

This is the torsion-submodule clause of More on Algebra 05EC,
`Stacks.Algebraization.exists_primaryComponent_baseChange_equiv_adicCompletion`, read at an
element: that clause gives an isomorphism of the `J`-power-torsion submodule of `M` with the
`J B ^∧`-power-torsion submodule of `B ^∧ ⊗_B M` which acts as `x ↦ 1 ⊗ x`, and `M` *is* its own
`J`-power-torsion submodule (`IPowerTorsion.mem_primaryComponent_of_isIPowerTorsion`).

`Stacks.Deformation.eq_zero_of_one_tmul_eq_zero` is the same statement for an arbitrary flat
`R ⟶ S` inducing `R/I ≅ S/IS`; this is its `S = B ^∧` specialization with those two hypotheses
discharged, named after the convention of
`Stacks.Algebraization.hom_baseChange_bijective_adicCompletion`, and it is stated here rather
than obtained from that one because `StacksFrontier/Deformation/` is not in the import closure of
this subtree. -/
public theorem eq_zero_of_one_tmul_eq_zero_adicCompletion (hM : IsIPowerTorsion B M J) {x : M}
    (h : (1 : AdicCompletion J B) ⊗ₜ[B] x = 0) : x = 0 := by
  obtain ⟨e, he⟩ := exists_primaryComponent_baseChange_equiv_adicCompletion B J M
  have hx : x ∈ Ideal.primaryComponent M J :=
    IPowerTorsion.mem_primaryComponent_of_isIPowerTorsion J hM x
  exact Submodule.coe_eq_zero.2
    (e.map_eq_zero_iff.1 (Submodule.coe_eq_zero.1 ((he ⟨x, hx⟩).trans h)))

/-- **Annihilation of a power-torsion module returns along `B ⟶ B ^∧`.** Let `B` be Noetherian,
`J ⊆ B` an ideal, `M` a `J`-power-torsion `B`-module, `𝔞 ⊆ B` an ideal and `t` an exponent. If
the extension `𝔞 B ^∧` to the power `t` annihilates the base change `B ^∧ ⊗_B M`, then `𝔞 ᵗ`
annihilates `M`.

This is the step of the second paragraph of the proof of Stacks 088B that brings the annihilation
half of the conclusion back from `Spec B ^∧`: the levelwise kernels and cokernels of `α` at level
`k` sit between modules annihilated by `𝒥 ᵏ⁺¹`, so they are `J`-power torsion and the hypothesis
applies to them.

The power-torsion hypothesis is essential, not bookkeeping: see the module docstring for the
counterexample without it. -/
public theorem idealPow_smul_eq_zero_of_baseChange_adicCompletion (hM : IsIPowerTorsion B M J)
    (a : Ideal B) (t : ℕ)
    (h : ∀ r ∈ (a.map (algebraMap B (AdicCompletion J B))) ^ t,
      ∀ y : TensorProduct B (AdicCompletion J B) M, r • y = 0) :
    ∀ r ∈ a ^ t, ∀ x : M, r • x = 0 := by
  intro r hr x
  refine eq_zero_of_one_tmul_eq_zero_adicCompletion B J hM ?_
  calc (1 : AdicCompletion J B) ⊗ₜ[B] (r • x)
      = r • ((1 : AdicCompletion J B) ⊗ₜ[B] x) := TensorProduct.tmul_smul r 1 x
    _ = algebraMap B (AdicCompletion J B) r • ((1 : AdicCompletion J B) ⊗ₜ[B] x) :=
        (algebraMap_smul (AdicCompletion J B) r _).symm
    _ = 0 := h _ ((Ideal.map_pow _ a t).le (Ideal.mem_map_of_mem _ hr)) _

/-- **`Stacks.Algebraization.idealPow_smul_eq_zero_of_baseChange_adicCompletion` as a vanishing of
a submodule.** The form in which
`Stacks.Algebraization.idealPowerMultiple_eq_bot_iff_affine_sections_annihilated` consumes an
annihilation statement over an affine open. -/
public theorem smul_top_eq_bot_of_baseChange_adicCompletion (hM : IsIPowerTorsion B M J)
    (a : Ideal B) (t : ℕ)
    (h : ∀ r ∈ (a.map (algebraMap B (AdicCompletion J B))) ^ t,
      ∀ y : TensorProduct B (AdicCompletion J B) M, r • y = 0) :
    a ^ t • (⊤ : Submodule B M) = ⊥ :=
  (ideal_smul_top_eq_bot_iff (a ^ t)).2
    (idealPow_smul_eq_zero_of_baseChange_adicCompletion B J hM a t h)

end Return

end Stacks.Algebraization

/-! ### Piece 2: the completed direct image and restriction to an open of the base -/

namespace Stacks.Coherent

open Stacks.Algebraization Stacks.AlgebraicGeometry.AffinePushforward

section SourceNormalization

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (J : Y.IdealSheafData) (m : ℕ)
  (F : X.Modules) [F.IsQuasicoherent]
  [((Scheme.Modules.pushforward f).obj F).IsQuasicoherent]

omit [F.IsQuasicoherent] in
/-- **The normalization of `Stacks.Coherent.directImageQuotientRestrictSourceIso`**: it carries
the restriction of the quotient projection of `f_*𝓕` to the base-change isomorphism followed by
the quotient projection of `(f ∣_ U)_*(𝓕|_{f ⁻¹ U})`. The projection on the left being an
epimorphism, this determines the identification.

This is the step `hS` of the proof of
`Stacks.Coherent.directImageQuotientComparison_restrict`, stated rather than left inline: it is
what identifies the projections of the *system* `((f_*𝓕) ^∧)|_U` with those of
`((f ∣_ U)_*(𝓕|_{f ⁻¹ U})) ^∧`, which is how
`Stacks.Coherent.completedDirectImageRestrictIso` is pinned down. -/
public theorem directImageQuotientRestrictSourceIso_π :
    (Scheme.Modules.restrictFunctor U.ι).map
        (cokernel.π (C := Y.Modules)
          (idealPowerMultiple J m ((Scheme.Modules.pushforward f).obj F)).ι) ≫
      (directImageQuotientRestrictSourceIso f U J m F).hom =
    (restrictPushforwardIso f U).hom.app F ≫
      cokernel.π (C := U.toScheme.Modules)
        (idealPowerMultiple (J.comap U.ι) m
          ((Scheme.Modules.pushforward (f ∣_ U)).obj
            ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj F))).ι :=
  (Category.assoc (obj := U.toScheme.Modules) _ _ _).symm.trans
    ((congrArg (fun z => z ≫ idealPowerQuotientMap (J.comap U.ι) (J.comap U.ι) m m le_rfl
          ((restrictPushforwardIso f U).hom.app F))
        (restrictFunctor_map_cokernel_π_comp_restrictIdealPowerQuotientIso_inv U.ι J m
          ((Scheme.Modules.pushforward f).obj F))).trans
      (idealPowerQuotientMap_π (J.comap U.ι) (J.comap U.ι) m m le_rfl
        ((restrictPushforwardIso f U).hom.app F)))

end SourceNormalization

section CompletedSystem

variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y) [IsProper f]
  (U : Y.Opens) [IsNoetherian U.toScheme] [IsNoetherian (f ⁻¹ᵁ U).toScheme]
  (J : Y.IdealSheafData)
  (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)

/-- **The restriction of the completed direct image to an open of the base, levelwise.** At level
`n` the restriction to `U` of `((f_*𝓕) ^∧)_n = (f_*𝓕) / 𝒥 ⁿ⁺¹ (f_*𝓕)` is
`((f ∣_ U)_*(𝓕|_{f ⁻¹ U})) ^∧` at the same level: the object formula
`Stacks.Algebraization.completionFunctor_obj` at both ends, with
`Stacks.Coherent.directImageQuotientRestrictSourceIso` in between.

`Stacks.Coherent.completedDirectImageRestrictIso` assembles these into an isomorphism of inverse
systems. -/
public def completedDirectImageRestrictIsoApp (n : ℕ) :
    (Scheme.Modules.restrictFunctor U.ι).obj
        (((completionFunctor Y J).obj (properPushforwardCoherent f F)).obj.obj (op n)) ≅
      ((completionFunctor U.toScheme (J.comap U.ι)).obj
          (properPushforwardCoherent (f ∣_ U)
            (restrictCoherentModules (f ⁻¹ᵁ U).ι F))).obj.obj (op n) :=
  haveI : F.obj.IsCoherent := F.property
  haveI : F.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent F.obj
  haveI : ((Scheme.Modules.pushforward f).obj F.obj).IsCoherent :=
    (properPushforwardCoherent f F).property
  haveI : ((Scheme.Modules.pushforward f).obj F.obj).IsQuasicoherent :=
    isQuasicoherent_of_isCoherent ((Scheme.Modules.pushforward f).obj F.obj)
  (Scheme.Modules.restrictFunctor U.ι).mapIso
      (eqToIso (completionFunctor_obj Y J (properPushforwardCoherent f F) n)) ≪≫
    directImageQuotientRestrictSourceIso f U J (n + 1) F.obj ≪≫
      eqToIso (completionFunctor_obj U.toScheme (J.comap U.ι)
        (properPushforwardCoherent (f ∣_ U) (restrictCoherentModules (f ⁻¹ᵁ U).ι F)) n).symm

omit [AlgebraicGeometry.IsNoetherian (f ⁻¹ᵁ U).toScheme] in
/-- **The levelwise identification carries the projections to the projections.** The restriction
to `U` of `f_*𝓕 ⟶ ((f_*𝓕) ^∧)_n` followed by
`Stacks.Coherent.completedDirectImageRestrictIsoApp` is the base-change isomorphism
`(f_*𝓕)|_U ≅ (f ∣_ U)_*(𝓕|_{f ⁻¹ U})` followed by the projection of the completion over `U`.

The projections are epimorphisms (`Stacks.Algebraization.epi_completionProjection`), so this
determines the identification, and it is what makes the naturality of
`Stacks.Coherent.completedDirectImageRestrictIso` free. -/
public theorem completionProjection_comp_completedDirectImageRestrictIsoApp (n : ℕ) :
    (Scheme.Modules.restrictFunctor U.ι).map
          (completionProjection Y J (properPushforwardCoherent f F) n) ≫
        (completedDirectImageRestrictIsoApp f U J F n).hom =
      (restrictPushforwardIso f U).hom.app F.obj ≫
        completionProjection U.toScheme (J.comap U.ι)
          (properPushforwardCoherent (f ∣_ U) (restrictCoherentModules (f ⁻¹ᵁ U).ι F)) n := by
  have : F.obj.IsCoherent := F.property
  have : F.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent F.obj
  have : ((Scheme.Modules.pushforward f).obj F.obj).IsCoherent :=
    (properPushforwardCoherent f F).property
  have : ((Scheme.Modules.pushforward f).obj F.obj).IsQuasicoherent :=
    isQuasicoherent_of_isCoherent ((Scheme.Modules.pushforward f).obj F.obj)
  have hΦ : (completedDirectImageRestrictIsoApp f U J F n).hom =
      (Scheme.Modules.restrictFunctor U.ι).map
          (eqToHom (completionFunctor_obj Y J (properPushforwardCoherent f F) n)) ≫
        (directImageQuotientRestrictSourceIso f U J (n + 1) F.obj).hom ≫
          eqToHom (completionFunctor_obj U.toScheme (J.comap U.ι)
            (properPushforwardCoherent (f ∣_ U)
              (restrictCoherentModules (f ⁻¹ᵁ U).ι F)) n).symm :=
    rfl
  -- the projection, read against the object formula, is the quotient projection
  have hid : eqToHom (completionFunctor_obj Y J (properPushforwardCoherent f F) n).symm ≫
      eqToHom (completionFunctor_obj Y J (properPushforwardCoherent f F) n) = 𝟙 _ :=
    (eqToIso (completionFunctor_obj Y J (properPushforwardCoherent f F) n)).inv_hom_id
  have hcpe : completionProjection Y J (properPushforwardCoherent f F) n ≫
      eqToHom (completionFunctor_obj Y J (properPushforwardCoherent f F) n) =
      cokernel.π (C := Y.Modules)
        (idealPowerMultiple J (n + 1) ((Scheme.Modules.pushforward f).obj F.obj)).ι :=
    (Category.assoc (obj := Y.Modules) _ _ _).trans
      ((congrArg (fun z => cokernel.π (C := Y.Modules)
            (idealPowerMultiple J (n + 1) ((Scheme.Modules.pushforward f).obj F.obj)).ι ≫ z)
          hid).trans
        (Category.comp_id (obj := Y.Modules) _))
  have key : (Scheme.Modules.restrictFunctor U.ι).map
        (completionProjection Y J (properPushforwardCoherent f F) n) ≫
      (Scheme.Modules.restrictFunctor U.ι).map
        (eqToHom (completionFunctor_obj Y J (properPushforwardCoherent f F) n)) =
      (Scheme.Modules.restrictFunctor U.ι).map
        (cokernel.π (C := Y.Modules)
          (idealPowerMultiple J (n + 1) ((Scheme.Modules.pushforward f).obj F.obj)).ι) :=
    ((Scheme.Modules.restrictFunctor U.ι).map_comp _ _).symm.trans
      (congrArg (Scheme.Modules.restrictFunctor U.ι).map hcpe)
  refine Eq.trans (congrArg (fun z => (Scheme.Modules.restrictFunctor U.ι).map
    (completionProjection Y J (properPushforwardCoherent f F) n) ≫ z) hΦ) ?_
  refine Eq.trans (Category.assoc (obj := U.toScheme.Modules) _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫
    ((directImageQuotientRestrictSourceIso f U J (n + 1) F.obj).hom ≫
      eqToHom (completionFunctor_obj U.toScheme (J.comap U.ι)
        (properPushforwardCoherent (f ∣_ U)
          (restrictCoherentModules (f ⁻¹ᵁ U).ι F)) n).symm)) key) ?_
  refine Eq.trans (Category.assoc (obj := U.toScheme.Modules) _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫
    eqToHom (completionFunctor_obj U.toScheme (J.comap U.ι)
      (properPushforwardCoherent (f ∣_ U) (restrictCoherentModules (f ⁻¹ᵁ U).ι F)) n).symm)
    (directImageQuotientRestrictSourceIso_π f U J (n + 1) F.obj)) ?_
  exact Category.assoc (obj := U.toScheme.Modules) _ _ _

/-- **The completed direct image commutes with restriction to an open of the base.** For a proper
`f : X ⟶ Y` of Noetherian schemes, a quasi-coherent ideal sheaf `𝒥` on `Y`, a coherent
`𝒪_X`-module `𝓕` and an open `U ⊆ Y` with `U` and `f ⁻¹ U` Noetherian,

`((f_*𝓕) ^∧)|_U ≅ ((f ∣_ U)_*(𝓕|_{f ⁻¹ U})) ^∧`

as inverse systems of `𝒪_U`-modules.

**This is what the localization of Stacks 088B over an affine open of the base is missing.** The
levelwise comparisons of the restricted `δ` and `γ_n` with those of `f ∣_ U` are available
(`Stacks.Coherent.directImageQuotientComparison_restrict` and
`Stacks.Coherent.directImageComparison_app_restrict_unit`), but the restricted characterization
of Stacks 088B is an equation between morphisms of *systems*, and until the two presentations of
the target are identified as systems a solution over `U` of the problem for `f ∣_ U` is not a
solution of the restricted problem.

The naturality is free: both sides are determined by their composites with the restriction of the
projection out of `f_*𝓕`, which is an epimorphism, and
`Stacks.Coherent.completionProjection_comp_completedDirectImageRestrictIsoApp` computes those
composites, against `Stacks.Algebraization.completionProjection_naturality` at both ends. -/
public def completedDirectImageRestrictIso :
    ((completionFunctor Y J).obj (properPushforwardCoherent f F)).obj ⋙
        Scheme.Modules.restrictFunctor U.ι ≅
      ((completionFunctor U.toScheme (J.comap U.ι)).obj
        (properPushforwardCoherent (f ∣_ U) (restrictCoherentModules (f ⁻¹ᵁ U).ι F))).obj :=
  NatIso.ofComponents (fun n => completedDirectImageRestrictIsoApp f U J F n.unop) <| by
    intro i j g
    haveI hepi : Epi ((Scheme.Modules.restrictFunctor U.ι).map
        (completionProjection Y J (properPushforwardCoherent f F) i.unop)) :=
      letI := Stacks.Coherent.epi_completionProjection J (properPushforwardCoherent f F) i.unop
      (Scheme.Modules.restrictFunctor U.ι).map_epi _
    refine (@cancel_epi _ _ _ _ _ ((Scheme.Modules.restrictFunctor U.ι).map
      (completionProjection Y J (properPushforwardCoherent f F) i.unop)) hepi _ _).mp ?_
    -- the left-hand side, read out of `(f_*𝓕)|_U`
    have hL : (Scheme.Modules.restrictFunctor U.ι).map
          (completionProjection Y J (properPushforwardCoherent f F) i.unop) ≫
        ((((completionFunctor Y J).obj (properPushforwardCoherent f F)).obj ⋙
              Scheme.Modules.restrictFunctor U.ι).map g ≫
          (completedDirectImageRestrictIsoApp f U J F j.unop).hom) =
        (restrictPushforwardIso f U).hom.app F.obj ≫
          completionProjection U.toScheme (J.comap U.ι)
            (properPushforwardCoherent (f ∣_ U)
              (restrictCoherentModules (f ⁻¹ᵁ U).ι F)) j.unop := by
      refine Eq.trans (Category.assoc (obj := U.toScheme.Modules) _ _ _).symm ?_
      refine Eq.trans (congrArg
        (fun z => z ≫ (completedDirectImageRestrictIsoApp f U J F j.unop).hom)
        (((Scheme.Modules.restrictFunctor U.ι).map_comp _ _).symm.trans
          (congrArg (Scheme.Modules.restrictFunctor U.ι).map
            (completionProjection_naturality J (properPushforwardCoherent f F) g)))) ?_
      exact completionProjection_comp_completedDirectImageRestrictIsoApp f U J F j.unop
    -- the right-hand side, read out of the same object
    have hR : (Scheme.Modules.restrictFunctor U.ι).map
          (completionProjection Y J (properPushforwardCoherent f F) i.unop) ≫
        ((completedDirectImageRestrictIsoApp f U J F i.unop).hom ≫
          ((completionFunctor U.toScheme (J.comap U.ι)).obj
            (properPushforwardCoherent (f ∣_ U)
              (restrictCoherentModules (f ⁻¹ᵁ U).ι F))).obj.map g) =
        (restrictPushforwardIso f U).hom.app F.obj ≫
          completionProjection U.toScheme (J.comap U.ι)
            (properPushforwardCoherent (f ∣_ U)
              (restrictCoherentModules (f ⁻¹ᵁ U).ι F)) j.unop := by
      refine Eq.trans (Category.assoc (obj := U.toScheme.Modules) _ _ _).symm ?_
      refine Eq.trans (congrArg
        (fun z => z ≫ ((completionFunctor U.toScheme (J.comap U.ι)).obj
          (properPushforwardCoherent (f ∣_ U)
            (restrictCoherentModules (f ⁻¹ᵁ U).ι F))).obj.map g)
        (completionProjection_comp_completedDirectImageRestrictIsoApp f U J F i.unop)) ?_
      refine Eq.trans (Category.assoc (obj := U.toScheme.Modules) _ _ _) ?_
      exact congrArg (fun z => (restrictPushforwardIso f U).hom.app F.obj ≫ z)
        (completionProjection_naturality (J.comap U.ι)
          (properPushforwardCoherent (f ∣_ U)
            (restrictCoherentModules (f ⁻¹ᵁ U).ι F)) g)
    exact hL.trans hR.symm

end CompletedSystem

end Stacks.Coherent

end
