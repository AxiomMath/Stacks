module

public import StacksFrontier.AlgebraicGeometry.DeRham.PoincareDuality.TopDifferentialAbelian
public import StacksFrontier.AlgebraicGeometry.FormsTrace.RelativeFrobenius
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeCohomology.HodgeDuality
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyComparison.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.GlobalSectionsTensorQcqs
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.RelativeUniversalHomeomorphism
public import StacksFrontier.AlgebraicGeometry.ProperGeomConnected.Basic

/-!
# The top-degree de Rham differential in characteristic `p`

Let `k` be a field of characteristic `p > 0` and `X` a smooth proper scheme over `k`,
equidimensional of dimension `d`. This file proves the positive-characteristic case of
[Stacks, Tag 0FW6]: the map `d : Hᵈ(X, Ω^{d-1}_{X/k}) ⟶ Hᵈ(X, Ω^d_{X/k})` induced by the de Rham
differential is zero, for schemes over `k` whose dualizing module is `Ω^d` (the input of
[Stacks, Tag 0FW4], through which the dimension of `Hᵈ(X, Ω^d)` is computed).

The cohomology is that of the underlying abelian sheaves, as in the first page of the
Hodge-to-de Rham spectral sequence (`AlgebraicGeometry.SheafOfModules.hodgeToDeRhamFirstPage`):
the de Rham differential is not `𝒪_X`-linear.

## Main results

* `AlgebraicGeometry.TopDegreeDifferential.finiteDimensional_and_finrank_eq`: `Hᵈ(Z, Ω^d)` is
  finite dimensional of the dimension of `H⁰(Z, 𝒪_Z)`, from the perfect pairings of
  [Stacks, Tag 0FW4].
* `AlgebraicGeometry.TopDegreeDifferential.finrank_globalSections_pullback_eq`: global sections
  keep their dimension under base change of the field.
* `AlgebraicGeometry.TopDegreeDifferential.rightDerived_map_deRham_d_eq_zero_of_charP`: the
  characteristic-`p` case of [Stacks, Tag 0FW6].

## References

* [Stacks Project, Tag 0FW6](https://stacks.math.columbia.edu/tag/0FW6)
* [Stacks Project, Tag 0FW4](https://stacks.math.columbia.edu/tag/0FW4)
* [Stacks Project, Tag 0FW2](https://stacks.math.columbia.edu/tag/0FW2)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Duality (sheafCohomology singleModule dualizingModule globalRingHom)
open Stacks.Cohomology.GlobalKunneth (baseRing)
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.TopDegreeDifferential

attribute [local instance 100000] HasDerivedCategory.standard

section Dimension

variable {k : Type u} [Field k] {Z : Scheme.{u}} (h : Z ⟶ Spec (.of k))

/-- `Hⁿ(Z, ℱ)` of `Stacks.Duality.sheafCohomology` is the `n`-th right derived functor of global
sections, read over `k`. -/
def sheafCohomologyIsoRightDerived (F : Z.Modules) (n : ℕ) :
    sheafCohomology h F n ≅ (ModuleCat.restrictScalars (globalRingHom h)).obj
      (((SheafOfModules.evaluation Z.ringCatSheaf (op ⊤)).rightDerived n).obj F) :=
  (ModuleCat.restrictScalars (globalRingHom h)).mapIso
    ((Stacks.Duality.homologyBaseSectionsSingleIso (X := Z) n).app F ≪≫
      ((Stacks.DerivedIndexing.rightDerivedIso
        (Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen Z.toRingedSpace ⊤) n).app F).symm)

/-- **`Hᵈ(Z, Ω^d_{Z/k})` has the dimension of `H⁰(Z, 𝒪_Z)`.** Let `Z` be proper over a field `k`,
smooth of relative dimension `d`, Cohen--Macaulay and equidimensional of dimension `d`, with an
isomorphism `ω_Z ≅ Ω^d_{Z/k}`. The pairing `H⁰(Z, Ω^0) × Hᵈ(Z, Ω^d) ⟶ k` of [Stacks, Tag 0FW4] is
perfect, so `Hᵈ(Z, Ω^d)` is the dual of `H⁰(Z, Ω^0) = H⁰(Z, 𝒪_Z)`; both are finite dimensional. -/
theorem finiteDimensional_and_finrank_eq [IsProper h]
    (hCM : AlgebraicGeometry.IsCohenMacaulay Z) (hequi : TopologicalSpace.Equidimensional Z)
    (d : ℕ) (hd : topologicalKrullDim Z = d) [SmoothOfRelativeDimension d h]
    (e : dualizingModule h ≅ Scheme.Hom.relativeDifferentialForms h d) :
    FiniteDimensional k ((ModuleCat.restrictScalars (globalRingHom h)).obj
        (((SheafOfModules.evaluation Z.ringCatSheaf (op ⊤)).rightDerived d).obj
          (Scheme.Hom.relativeDifferentialForms h d))) ∧
      Module.finrank k ((ModuleCat.restrictScalars (globalRingHom h)).obj
        (((SheafOfModules.evaluation Z.ringCatSheaf (op ⊤)).rightDerived d).obj
          (Scheme.Hom.relativeDifferentialForms h d))) =
      Module.finrank k ((ModuleCat.restrictScalars (globalRingHom h)).obj
        (ModuleCat.of (baseRing Z.toRingedSpace) (baseRing Z.toRingedSpace))) := by
  obtain ⟨t, hperf, -⟩ := Scheme.Hom.hodgeDuality_of_iso h hCM hequi d hd e
  have key : ∀ m : ℤ, m = d → ∀ P : sheafCohomology h (Scheme.Hom.relativeDifferentialForms h 0) 0
      →ₗ[k] sheafCohomology h (Scheme.Hom.relativeDifferentialForms h m) m →ₗ[k] k, P.IsPerfPair →
      FiniteDimensional k (sheafCohomology h (Scheme.Hom.relativeDifferentialForms h m) m) ∧
        Module.finrank k (sheafCohomology h (Scheme.Hom.relativeDifferentialForms h m) m) =
          Module.finrank k ((ModuleCat.restrictScalars (globalRingHom h)).obj
            (ModuleCat.of (baseRing Z.toRingedSpace) (baseRing Z.toRingedSpace))) := by
    rintro m rfl P hP
    have := hP
    have := Module.IsReflexive.of_isPerfPair P
    have := Module.IsReflexive.of_isPerfPair P.flip
    refine ⟨inferInstance, ?_⟩
    rw [(LinearEquiv.ofBijective P.flip hP.bijective_right).finrank_eq,
      Subspace.dual_finrank_eq]
    exact ((ModuleCat.restrictScalars (globalRingHom h)).mapIso
      (Scheme.Hom.hodgeZeroIso h)).toLinearEquiv.finrank_eq
  obtain ⟨hfin, hrank⟩ := key ((d : ℤ) - 0) (sub_zero _) (Scheme.Hom.hodgePairing h d t 0 0)
    (hperf 0 0)
  rw [sub_zero] at hfin hrank
  let E :=
    (sheafCohomologyIsoRightDerived h (Scheme.Hom.relativeDifferentialForms h d) d).toLinearEquiv
  exact ⟨LinearEquiv.finiteDimensional E, E.finrank_eq.symm.trans hrank⟩

/-- **Global sections commute with base change of the field, in dimension.** For `X`
quasi-compact and quasi-separated over a field `k` and any `q : Spec k ⟶ Spec k`, the global
sections of `X ×_{k, q} k`, a `k`-vector space through the second projection, have the dimension
of the global sections of `X`: `Γ(X ×_{k, q} k, 𝒪) = Γ(X, 𝒪_X) ⊗_{k, q} k`
(`AlgebraicGeometry.bijective_globalSectionsTensorDesc`). -/
theorem finrank_globalSections_pullback_eq {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (f : X ⟶ Spec (.of k)) (q : Spec (.of k) ⟶ Spec (.of k)) :
    Module.finrank k ((ModuleCat.restrictScalars (globalRingHom (pullback.snd f q))).obj
        (ModuleCat.of (baseRing (pullback f q).toRingedSpace)
          (baseRing (pullback f q).toRingedSpace))) =
      Module.finrank k ((ModuleCat.restrictScalars (globalRingHom f)).obj
        (ModuleCat.of (baseRing X.toRingedSpace) (baseRing X.toRingedSpace))) := by
  let A := Γ(Spec (.of k), ⊤)
  let : Algebra k Γ(X, ⊤) := (structureRingMap f).hom.toAlgebra
  let : Algebra k A := (structureRingMap q).hom.toAlgebra
  have hb := bijective_globalSectionsTensorDesc f q rfl rfl
  let T := globalSectionsTensorDesc f q rfl rfl
  let mA : Module A Γ(pullback f q, ⊤) := Module.compHom _ (pullback.snd f q).appTop.hom
  let j : A ⊗[k] Γ(X, ⊤) ≃+ Γ(pullback f q, ⊤) :=
    (TensorProduct.comm k A Γ(X, ⊤)).toAddEquiv.trans
      (AddEquiv.ofBijective T.hom.toAddMonoidHom hb)
  have hj : ∀ (a : A) (t : A ⊗[k] Γ(X, ⊤)), j (a • t) = a • j t := by
    intro a t
    induction t using TensorProduct.inductionOn with
    | tmul b x =>
      change T (x ⊗ₜ (a * b)) = (pullback.snd f q).appTop a * T (x ⊗ₜ b)
      rw [globalSectionsTensorDesc_tmul, globalSectionsTensorDesc_tmul, map_mul]
      ring
    | add t₁ t₂ h₁ h₂ => rw [smul_add, map_add, map_add, h₁, h₂, smul_add]
  have h1 : Module.rank A (A ⊗[k] Γ(X, ⊤)) = Module.rank A Γ(pullback f q, ⊤) :=
    rank_eq_of_equiv_equiv id j Function.bijective_id hj
  have h2 : Module.finrank A (A ⊗[k] Γ(X, ⊤)) = Module.finrank k Γ(X, ⊤) :=
    Module.finrank_baseChange
  let ψ := (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  have hψ : Function.Bijective ψ :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv)
  have h3 : Module.rank k ((ModuleCat.restrictScalars (globalRingHom (pullback.snd f q))).obj
      (ModuleCat.of (baseRing (pullback f q).toRingedSpace)
        (baseRing (pullback f q).toRingedSpace))) = Module.rank A Γ(pullback f q, ⊤) :=
    rank_eq_of_equiv_equiv ψ (AddEquiv.refl _) hψ (fun _ _ => rfl)
  have h4 : Module.rank k ((ModuleCat.restrictScalars (globalRingHom f)).obj
      (ModuleCat.of (baseRing X.toRingedSpace) (baseRing X.toRingedSpace))) =
      Module.rank k Γ(X, ⊤) := rfl
  unfold Module.finrank at h2 ⊢
  rw [h3, h4, ← h1, h2]

/-- **Cohomology along an affine morphism, in dimension over `k`** ([Stacks, Tag 089W]): for
`F : X ⟶ Y` affine over `Y ⟶ Spec k` and `ℳ` quasi-coherent on `X`, the `k`-vector spaces
`Hⁿ(Y, F_* ℳ)` and `Hⁿ(X, ℳ)` have the same dimension. -/
theorem rank_rightDerived_pushforward {X Y : Scheme.{u}} (F : X ⟶ Y) [IsAffineHom F]
    (g : Y ⟶ Spec (.of k)) (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    Module.rank k ((ModuleCat.restrictScalars (globalRingHom g)).obj
        (((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).rightDerived n).obj
          ((Scheme.Modules.pushforward F).obj M))) =
      Module.rank k ((ModuleCat.restrictScalars (globalRingHom (F ≫ g))).obj
        (((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).rightDerived n).obj M)) := by
  have h1 := ((ModuleCat.restrictScalars (globalRingHom g)).mapIso
    (Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward F M n)).toLinearEquiv.rank_eq
  exact h1.symm.trans rfl

end Dimension

section Frobenius

open Stacks.Cohomology.Leray (sectionsFunctor)
open Stacks.Frobenius (absoluteFrobenius)

/-- **The trace of a finite syntomic morphism kills the pushed-forward de Rham differential when
it vanishes one degree lower.** For `F : X ⟶ Y` finite syntomic over `S`, the trace
`Θ : F_* Ω^•_{X/S} ⟶ Ω^•_{Y/S}` of [Stacks, Tag 0FLC] is a map of complexes, so if
`Θ^e = 0` then `Θ^{e+1} ∘ F_* d = d ∘ Θ^e = 0` as maps of abelian sheaves on `Y`. -/
theorem pushforward_deRham_d_comp_relativeFormsTrace_eq_zero {X Y S : Scheme.{u}} (F : X ⟶ Y)
    (g : Y ⟶ S) [IsFinite F] (hF : Syntomic F) (e : ℕ)
    (h0 : F.relativeFormsTrace g hF e = 0) :
    (Stacks.ClosedImmersion.abelianSheafPushforward.{u, u} F.base).map
        ((SheafOfModules.toSheaf _).map ((F ≫ g).deRhamComplex.d e (e + 1))) ≫
      (SheafOfModules.toSheaf _).map (F.relativeFormsTrace g hF (e + 1)) = 0 := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))
  obtain ⟨U⟩ := U
  refine AddCommGrpCat.ext fun η => ?_
  change (F.relativeFormsTrace g hF (e + 1)).app U
    (((F ≫ g).deRhamComplex.d e (e + 1)).val.app (op (F ⁻¹ᵁ U)) η) = 0
  refine (Scheme.Hom.relativeFormsTrace_deRhamComplex_d (f := F) (g := g) (p := e) hF U η).trans ?_
  have h1 : (F.relativeFormsTrace g hF e).app U η = 0 := by
    rw [h0]
    rfl
  rw [h1]
  exact map_zero _

/-- **A surjection of `k`-vector spaces of the same finite dimension, read on top-degree
cohomology.** Let `Y` be a Noetherian scheme over `k` of dimension at most `d` and `θ : ℳ ⟶ 𝒩` an
epimorphism of `𝒪_Y`-modules such that `Hᵈ(Y, ℳ)` and `Hᵈ(Y, 𝒩)` are finite dimensional of the same
dimension over `k`. Then `θ` induces an injection on `Hᵈ` of the underlying abelian sheaves: it
induces a surjection there ([Stacks, Tag 02UZ]), hence on `Hᵈ` of modules ([Stacks, Tag 01F1]),
which is `k`-linear between spaces of the same finite dimension. -/
theorem injective_rightDerived_toSheaf_map {k : Type u} [Field k] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of k)) [NoetherianSpace Y] {M N : Y.Modules} (θ : M ⟶ N) [Epi θ] (d : ℕ)
    (hdim : topologicalKrullDim Y ≤ (d : WithBot ℕ∞))
    [FiniteDimensional k ((ModuleCat.restrictScalars (globalRingHom g)).obj
      (((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).rightDerived d).obj M))]
    [FiniteDimensional k ((ModuleCat.restrictScalars (globalRingHom g)).obj
      (((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).rightDerived d).obj N))]
    (hrank : Module.finrank k ((ModuleCat.restrictScalars (globalRingHom g)).obj
        (((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).rightDerived d).obj M)) =
      Module.finrank k ((ModuleCat.restrictScalars (globalRingHom g)).obj
        (((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).rightDerived d).obj N))) :
    Function.Injective (((sectionsFunctor Y.carrier ⊤).rightDerived d).map
      ((SheafOfModules.toSheaf _).map θ)) := by
  have : @Epi (SheafOfModules.{u} Y.ringCatSheaf) _ M N θ :=
    ⟨fun a b hab => (‹Epi θ›).left_cancellation a b hab⟩
  have := Stacks.SheafOfModules.EpiMono.epi_toSheaf_map (R := Y.ringCatSheaf) θ
  let φ := ((ModuleCat.restrictScalars (globalRingHom g)).map
    (((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).rightDerived d).map θ)).hom
  have hφ : Function.Surjective φ :=
    (Stacks.Cohomology.TopDegree.surjective_rightDerived_evaluation_iff Y.ringCatSheaf θ d).2
      (Stacks.Cohomology.TopDegree.surjective_rightDerived_map_of_epi Y.carrier hdim
        ((SheafOfModules.toSheaf Y.ringCatSheaf).map θ))
  exact (Stacks.Cohomology.TopDegree.injective_rightDerived_evaluation_iff Y.ringCatSheaf θ d).1
    ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).2 hφ)

/-- **The trace of a finite syntomic morphism is injective on top-degree cohomology.** For
`F : X ⟶ Y` finite syntomic over `g : Y ⟶ Spec k`, with `X` and `Y` smooth proper over `k`,
equidimensional of dimension `d`, with dualizing modules `Ω^d` and global sections of the same
dimension, the epimorphism `Θ^d : F_* Ω^d_{X/k} ⟶ Ω^d_{Y/k}` is injective on `Hᵈ(Y, -)`. -/
private theorem injective_rightDerived_relativeFormsTrace {k : Type u} [Field k] {X Y : Scheme.{u}}
    (F : X ⟶ Y) (g : Y ⟶ Spec (.of k)) [IsFinite F] (hF : Syntomic F) (d : ℕ)
    [IsProper (F ≫ g)] [SmoothOfRelativeDimension d (F ≫ g)] [IsProper g]
    [SmoothOfRelativeDimension d g] [NoetherianSpace Y] [Epi (F.relativeFormsTrace g hF d)]
    (hX : TopologicalSpace.Equidimensional X) (hXd : topologicalKrullDim X = d)
    (hY : TopologicalSpace.Equidimensional Y) (hYd : topologicalKrullDim Y = d)
    (eX : dualizingModule (F ≫ g) ≅ Scheme.Hom.relativeDifferentialForms (F ≫ g) d)
    (eY : dualizingModule g ≅ Scheme.Hom.relativeDifferentialForms g d)
    (hΓ : Module.finrank k ((ModuleCat.restrictScalars (globalRingHom (F ≫ g))).obj
        (ModuleCat.of (baseRing X.toRingedSpace) (baseRing X.toRingedSpace))) =
      Module.finrank k ((ModuleCat.restrictScalars (globalRingHom g)).obj
        (ModuleCat.of (baseRing Y.toRingedSpace) (baseRing Y.toRingedSpace)))) :
    Function.Injective (((sectionsFunctor Y.carrier ⊤).rightDerived d).map
      ((SheafOfModules.toSheaf _).map (F.relativeFormsTrace g hF d))) := by
  have := SmoothOfRelativeDimension.smooth d g
  have := SmoothOfRelativeDimension.smooth d (F ≫ g)
  obtain ⟨hfX, hrX⟩ := finiteDimensional_and_finrank_eq (F ≫ g)
    (isCohenMacaulay_of_syntomic_over_field (F ≫ g) (syntomic_of_smooth _)) hX d hXd eX
  obtain ⟨hfY, hrY⟩ := finiteDimensional_and_finrank_eq g
    (isCohenMacaulay_of_syntomic_over_field g (syntomic_of_smooth _)) hY d hYd eY
  have := Scheme.Hom.isQuasicoherent_relativeDifferentialForms (F ≫ g) d
  have hrank := rank_rightDerived_pushforward F g
    (Scheme.Hom.relativeDifferentialForms (F ≫ g) (d : ℤ)) d
  have hlt : Module.rank k ((ModuleCat.restrictScalars (globalRingHom g)).obj
      (((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).rightDerived d).obj
        ((Scheme.Modules.pushforward F).obj
          (Scheme.Hom.relativeDifferentialForms (F ≫ g) (d : ℤ))))) < Cardinal.aleph0 :=
    hrank ▸ Module.rank_lt_aleph0 k _
  have := Module.rank_lt_aleph0_iff.1 hlt
  exact injective_rightDerived_toSheaf_map g (F.relativeFormsTrace g hF d) d hYd.le
    ((congrArg Cardinal.toNat hrank).trans (hrX.trans (hΓ.trans hrY.symm)))

/-- **The pushed-forward de Rham differential vanishes on top-degree cohomology.** For
`F : X ⟶ Y` finite syntomic over `S` with `Θ^e = 0` and `Θ^{e+1}` injective on `H^{e+1}(Y, -)`,
the map `F_* d : F_* Ω^e ⟶ F_* Ω^{e+1}` induces zero on `H^{e+1}(Y, -)`. -/
private theorem rightDerived_map_pushforward_deRham_d_eq_zero {X Y S : Scheme.{u}} (F : X ⟶ Y)
    (g : Y ⟶ S) [IsFinite F] (hF : Syntomic F) (e : ℕ) (h0 : F.relativeFormsTrace g hF e = 0)
    (hinj : Function.Injective (((sectionsFunctor Y.carrier ⊤).rightDerived (e + 1)).map
      ((SheafOfModules.toSheaf _).map (F.relativeFormsTrace g hF (e + 1))))) :
    ((sectionsFunctor Y.carrier ⊤).rightDerived (e + 1)).map
      ((Stacks.ClosedImmersion.abelianSheafPushforward.{u, u} F.base).map
        ((SheafOfModules.toSheaf _).map ((F ≫ g).deRhamComplex.d e (e + 1)))) = 0 := by
  let H := (sectionsFunctor Y.carrier ⊤).rightDerived (e + 1)
  have h2 := ((H.map_comp _ _).symm.trans
    (congrArg H.map (pushforward_deRham_d_comp_relativeFormsTrace_eq_zero F g hF e h0))).trans
      (H.map_zero _ _)
  have hm : Mono (H.map ((SheafOfModules.toSheaf _).map (F.relativeFormsTrace g hF (e + 1)))) :=
    (AddCommGrpCat.mono_iff_injective _).2 hinj
  exact hm.right_cancellation _ _ (h2.trans zero_comp.symm)

/-- **[Stacks, Tag 0FW6] in characteristic `p`, for a scheme over `k` with dualizing module
`Ω^d`.** Let `k` be a field of characteristic `p > 0` and `X` a smooth proper scheme over `k`,
equidimensional of dimension `d = e + 1`, such that every smooth proper scheme `Z` over `k` of
relative dimension `d` has `ω_Z ≅ Ω^d_{Z/k}` (as for `X` and its Frobenius twist). Then
`d : Hᵈ(X, Ω^{d-1}_{X/k}) ⟶ Hᵈ(X, Ω^d_{X/k})` is zero.

The proof is the source's. Let `F : X ⟶ X^{(p)}` be the relative Frobenius and `Θ` the trace
of [Stacks, Tag 0FW2]: `Θ^{d-1} = 0`, so `Θ^d ∘ F_* d = d ∘ Θ^{d-1} = 0`, and `Θ^d` is an
epimorphism. On `Hᵈ(X^{(p)}, -)` the map `Θ^d` is then surjective (`Hᵈ` is right exact on a
Noetherian space of dimension `d`, [Stacks, Tag 02UZ]) between `k`-vector spaces of the same
finite dimension: `Hᵈ(X^{(p)}, F_* Ω^d_{X/k}) = Hᵈ(X, Ω^d_{X/k})` ([Stacks, Tag 089W]) and
`Hᵈ(X^{(p)}, Ω^d)` are dual to `H⁰(X, 𝒪_X)` and `H⁰(X^{(p)}, 𝒪) = H⁰(X, 𝒪_X) ⊗_{k, Frob} k` by
[Stacks, Tag 0FW4]. So `Θ^d` is injective on `Hᵈ`, `F_* d` induces zero on `Hᵈ(X^{(p)}, -)`, and
`d` induces zero on `Hᵈ(X, -)` since `F` is a homeomorphism ([Stacks, Tag 02UV]). -/
theorem rightDerived_map_deRham_d_eq_zero_of_charP
    (hω : ∀ {K : Type u} [Field K] {Z : Scheme.{u}} (h : Z ⟶ Spec (.of K)) [IsProper h]
      (n : ℕ) [SmoothOfRelativeDimension n h],
      Nonempty (dualizingModule h ≅ Scheme.Hom.relativeDifferentialForms h n))
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [Smooth f] (hequi : TopologicalSpace.Equidimensional X)
    (e : ℕ) (hd : topologicalKrullDim X = ((e + 1 : ℕ) : WithBot ℕ∞)) :
    ((sectionsFunctor X.carrier ⊤).rightDerived (e + 1)).map
      ((SheafOfModules.toSheaf _).map (f.deRhamComplex.d e (e + 1))) = 0 := by
  have : SmoothOfRelativeDimension (e + 1) f :=
    smoothOfRelativeDimension_of_equidimensional k f hequi (e + 1) hd
  let S := Spec (CommRingCat.of k)
  have hS : Stacks.Frobenius.IsInCharacteristic S p := Stacks.Frobenius.isInCharacteristic_spec k p
  let Xo : Over S := Over.mk f
  have : SmoothOfRelativeDimension (e + 1) Xo.hom := ‹SmoothOfRelativeDimension (e + 1) f›
  obtain ⟨hfin, hsyn, hcomp, hzero, hepi⟩ := relativeFrobenius_relativeFormsTrace S p hS Xo (e + 1)
  let Fr := (relativeFrobenius S p hS Xo).left
  let g := ((frobeniusTwist S p hS).obj Xo).hom
  have hcomp' : Fr ≫ g = f := hcomp
  suffices H : ((sectionsFunctor X.carrier ⊤).rightDerived (e + 1)).map
      ((SheafOfModules.toSheaf _).map ((Fr ≫ g).deRhamComplex.d e (e + 1))) = 0 from hcomp' ▸ H
  have : IsProper (Fr ≫ g) := hcomp' ▸ ‹IsProper f›
  have : SmoothOfRelativeDimension (e + 1) (Fr ≫ g) :=
    hcomp' ▸ ‹SmoothOfRelativeDimension (e + 1) f›
  have : IsProper g := inferInstanceAs (IsProper (pullback.snd f (absoluteFrobenius S p hS)))
  have : SmoothOfRelativeDimension (e + 1) g :=
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := e + 1)
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback f (absoluteFrobenius S p hS))
      ‹SmoothOfRelativeDimension (e + 1) f›
  have hhomeo : IsHomeomorph Fr.base :=
    (relativeFrobenius_universalHomeomorphism S p hS Xo).universally_isHomeomorph
      _ _ _ IsPullback.of_id_snd
  have hdY : topologicalKrullDim ((frobeniusTwist S p hS).obj Xo).left =
      ((e + 1 : ℕ) : WithBot ℕ∞) :=
    (IsHomeomorph.topologicalKrullDim_eq Fr.base hhomeo).symm.trans hd
  have : NoetherianSpace ((frobeniusTwist S p hS).obj Xo).left :=
    Stacks.AlgebraicGeometry.ProperGeomConnected.noetherianSpace_of_isProper g
  obtain ⟨eX⟩ := hω (Fr ≫ g) (e + 1)
  obtain ⟨eY⟩ := hω g (e + 1)
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have hΓX : Module.finrank k ((ModuleCat.restrictScalars (globalRingHom (Fr ≫ g))).obj
      (ModuleCat.of (baseRing X.toRingedSpace) (baseRing X.toRingedSpace))) =
      Module.finrank k ((ModuleCat.restrictScalars (globalRingHom f)).obj
        (ModuleCat.of (baseRing X.toRingedSpace) (baseRing X.toRingedSpace))) := by
    rw [hcomp']
  have hinj := injective_rightDerived_relativeFormsTrace Fr g hsyn (e + 1) hequi hd
    (TopologicalSpace.Equidimensional.of_homeomorph (hhomeo.homeomorph Fr.base).symm hequi) hdY
    eX eY (hΓX.trans (finrank_globalSections_pullback_eq f (absoluteFrobenius S p hS)).symm)
  exact Stacks.Cohomology.TopDegree.rightDerived_map_eq_zero_of_pushforward _ Fr.base
    hhomeo.isClosedEmbedding _ (e + 1)
    (rightDerived_map_pushforward_deRham_d_eq_zero Fr g hsyn e (hzero e (by omega)) hinj)

end Frobenius

end AlgebraicGeometry.TopDegreeDifferential
