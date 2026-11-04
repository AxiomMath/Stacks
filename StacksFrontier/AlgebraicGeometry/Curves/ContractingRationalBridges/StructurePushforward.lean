module

public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.HigherDirectImage

/-!
# The direct image of the structure sheaf along a contraction of a rational bridge

Let `k` be a field, let `X` be a proper scheme over `k` of dimension one with `H⁰(X, 𝒪_X) = k`
and at-worst-nodal singularities, let `C ⊆ X` be a rational bridge (Tag 0E3M), write `X'` for the
scheme-theoretic closure of `X \ C` and `k' = Γ(C, 𝒪_C)`, and let `c : X ⟶ Y` be a contraction of
`C`. This file proves

`c_* 𝒪_X = 𝒪_Y`,

the remaining half of the assertion [Stacks, Tag 0E3M] makes about the direct images of `𝒪_X`;
the other half, `R ¹ c_* 𝒪_X = 0`, is
`Stacks.Curves.isZero_rightDerived_one_pushforward_ambientStructureSheaf_bridge`.

## Main results

* `AlgebraicGeometry.isIso_app_of_isPushout_of_isPushout` — the comparison of two pushout
  presentations sharing a leg: if a scheme `S` is the pushout of `A` and `B` along `Z` and a
  scheme `T` is the pushout of `A` and `K` along `Z`, compatibly through `B ⟶ K`, then the
  morphism `S ⟶ T` is an isomorphism on sections over every open as soon as `B ⟶ K` is.
* `AlgebraicGeometry.isIso_structureSheafToPushforward_of_forall_isIso_app` — a morphism of
  schemes which is an isomorphism on sections over every open of the target has invertible
  comparison map of structure sheaves.
* `AlgebraicGeometry.isIso_app_toSpecΓ` — for a quasi-compact quasi-separated scheme the
  canonical morphism to the spectrum of its global functions is an isomorphism on sections over
  every open.
* `Stacks.Curves.isIso_app_of_isContractionOfRationalBridge` — a contraction is an isomorphism
  on sections over every open of its target.
* `Stacks.Curves.isIso_structureSheafToPushforward_contraction_bridge` — `c_* 𝒪_X = 𝒪_Y`.
* `Stacks.Curves.isIso_structureSheafToPushforward_and_isZero_rightDerived_one_contraction_bridge`
  — the two assertions of [Stacks, Tag 0E3M] about the direct images of `𝒪_X` together.

## The argument

The source deduces `𝒪_Y = c_* 𝒪_X` from the union sequence of [Stacks, Tag 0C4J] and the
description of the structure sheaf of a pushout in [Stacks, Tag 0E25]. Both of those describe a
ring of sections as a fibre product, so the proof here is run on sections and the two
descriptions are compared open by open:

* over an open `U` of `Y`, [Stacks, Tag 0E25] presents `Γ(Y, U)` as the fibre product of
  `Γ(k', b ⁻¹ᵁ U)` and `Γ(X', a ⁻¹ᵁ U)` over `Γ(C ∩ X', …)`, by
  `AlgebraicGeometry.structureSheaf_isPullback_of_isPushout` at the pushout square of the
  contraction;
* over `c ⁻¹ᵁ U`, the same theorem at the presentation of `X` as the scheme-theoretic union of
  `C` and `X'` ([Stacks, Tag 0C4J]) presents `Γ(X, c ⁻¹ᵁ U)` as the fibre product of
  `Γ(C, …)` and `Γ(X', …)` over `Γ(C ∩ X', …)`;
* the two cospans agree: the `X'` and `C ∩ X'` corners literally, because `a = c|_{X'}` and
  because `Scheme.Hom.comp_app` and `Scheme.Hom.comp_preimage` hold by `rfl`, and the remaining
  corner by `AlgebraicGeometry.isIso_app_toSpecΓ`, `C` being proper over `k` and hence
  quasi-compact and quasi-separated.

`AlgebraicGeometry.isIso_of_isPullback_comparison` then makes `c.app U` an isomorphism, and
invertibility of a morphism of sheaves of modules is sectionwise.

## Implementation notes

The comparison is carried out on sections rather than on sheaves of modules. On sheaves of
modules the two fibre squares are
`AlgebraicGeometry.isPullback_structureSheaf_union` pushed forward along `c` and
`AlgebraicGeometry.pushoutModuleSquare_isPullback`, and the four corner identifications then
have to be mediated through `AlgebraicGeometry.Scheme.Modules.pushforwardComp` and
`AlgebraicGeometry.Scheme.Modules.pushforwardCongr`; on sections all three identifications are
either `rfl` or a single transport along an equality of opens, assembled from
`AlgebraicGeometry.app_comp_eqToHom_of_eq` and `AlgebraicGeometry.eqToHom_comp_app`, each proved
by substituting the equality and appealing to proof irrelevance.

Nothing is routed through `AlgebraicGeometry.Scheme.IdealSheafData.closedSubschemeRestriction`,
whose definitional equation to the composite it is built from exceeds the kernel's heartbeat
budget; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Curves/ContractingRationalBridges/UnionStructureSquare.lean`.

## References

* [Stacks Project, Tag 0E3M](https://stacks.math.columbia.edu/tag/0E3M)
* [Stacks Project, Tag 0C4J](https://stacks.math.columbia.edu/tag/0C4J)
* [Stacks Project, Tag 0E25](https://stacks.math.columbia.edu/tag/0E25)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-! ### Transports of sections along equalities of opens -/

/-- Equal morphisms of schemes have the same map on sections over an open, after the transport
along the equality of the two preimages of that open. -/
theorem app_comp_eqToHom_of_eq {A B : Scheme.{u}} {f g : A ⟶ B} (h : f = g) (U : B.Opens) :
    f.app U ≫ eqToHom (congrArg (fun V : A.Opens ↦ Γ(A, V))
        (congrArg (fun φ : A ⟶ B ↦ φ ⁻¹ᵁ U) h)) =
      g.app U := by
  subst h
  simp

/-- The map on sections of a morphism of schemes commutes with the transport along an equality
of opens of its target. -/
theorem eqToHom_comp_app {A B : Scheme.{u}} (f : A ⟶ B) {V W : B.Opens} (e : V = W) :
    eqToHom (congrArg (fun T : B.Opens ↦ Γ(B, T)) e) ≫ f.app W =
      f.app V ≫ eqToHom (congrArg (fun T : B.Opens ↦ Γ(A, f ⁻¹ᵁ T)) e) := by
  subst e
  simp

/-! ### Sectionwise criteria -/

/-- For a quasi-compact quasi-separated scheme the canonical morphism to the spectrum of its
global functions is an isomorphism on the sections over every open. -/
theorem isIso_app_toSpecΓ (Z : Scheme.{u}) [CompactSpace Z] [QuasiSeparatedSpace Z]
    (V : (Spec Γ(Z, ⊤)).Opens) : IsIso (Z.toSpecΓ.app V) := by
  have h := isIso_hom_app_of_isIso_sheafHom
    (isIso_toRingCatSheafHom_toSpecΓ (Z := Z)) (op V)
  have : (forget₂ CommRingCat.{u} RingCat.{u}).ReflectsIsomorphisms :=
    CategoryTheory.reflectsIsomorphisms_forget₂ _ _
  exact (isIso_iff_of_reflects_iso (Z.toSpecΓ.app V)
    (forget₂ CommRingCat.{u} RingCat.{u})).mp h

/-- A morphism of schemes which is an isomorphism on the sections over every open of its target
has invertible comparison map from the structure sheaf of the target to the direct image of the
structure sheaf of the source. -/
theorem isIso_structureSheafToPushforward_of_forall_isIso_app {X P : Scheme.{u}} (f : X ⟶ P)
    (h : ∀ U : P.Opens, IsIso (f.app U)) : IsIso (structureSheafToPushforward f) := by
  refine isIso_unitToPushforwardObjUnit_of_forall_isIso_app f fun U ↦ ?_
  have := h U.unop
  exact inferInstanceAs (IsIso ((forget₂ CommRingCat.{u} RingCat.{u}).map (f.app U.unop)))

/-! ### Two pushout presentations sharing a leg -/

/-- **Comparison of two pushout presentations sharing a leg.** Let `S` be the pushout of
`p : A ⟶ S` and `r : B ⟶ S` along `i : Z ⟶ A`, `j : Z ⟶ B`, let `q : B ⟶ K` collapse the second
leg, and let `T` be the pushout of `p ≫ c : A ⟶ T` and `b : K ⟶ T` along `i` and `j ≫ q`, with
`r ≫ c = q ≫ b`. If `q` is an isomorphism on sections over every open of `K`, then `c : S ⟶ T`
is an isomorphism on the sections over every open of `T`.

Both squares present a ring of sections as a fibre product by [Stacks, Tag 0E25],
`AlgebraicGeometry.structureSheaf_isPullback_of_isPushout`, over the same cospan up to the
identification of the `K`-corner supplied by `q`. -/
theorem isIso_app_of_isPushout_of_isPushout
    {Z A B S K T : Scheme.{u}}
    {i : Z ⟶ A} {j : Z ⟶ B} {p : A ⟶ S} {r : B ⟶ S} {q : B ⟶ K} {b : K ⟶ T} {c : S ⟶ T}
    [IsClosedImmersion i] [IsIntegralHom j] [IsAffineHom p] [IsIntegralHom (j ≫ q)]
    (hunion : IsPushout i j p r) (hpush : IsPushout i (j ≫ q) (p ≫ c) b)
    (hAffine : ∀ y : K, ∃ V : A.Opens, IsAffineOpen V ∧ ∀ z : Z, (j ≫ q) z = y → i z ∈ V)
    (hq : ∀ V : K.Opens, IsIso (q.app V)) (hrc : r ≫ c = q ≫ b) (U : T.Opens) :
    IsIso (c.app U) := by
  have := hq (b ⁻¹ᵁ U)
  have e : q ⁻¹ᵁ (b ⁻¹ᵁ U) = r ⁻¹ᵁ (c ⁻¹ᵁ U) :=
    congrArg (fun φ : B ⟶ T ↦ φ ⁻¹ᵁ U) hrc.symm
  have w : i ⁻¹ᵁ (p ⁻¹ᵁ (c ⁻¹ᵁ U)) = j ⁻¹ᵁ (q ⁻¹ᵁ (b ⁻¹ᵁ U)) :=
    congrArg (fun φ : Z ⟶ T ↦ φ ⁻¹ᵁ U) hpush.w
  have w' : i ⁻¹ᵁ (p ⁻¹ᵁ (c ⁻¹ᵁ U)) = j ⁻¹ᵁ (r ⁻¹ᵁ (c ⁻¹ᵁ U)) :=
    congrArg (fun φ : Z ⟶ S ↦ φ ⁻¹ᵁ (c ⁻¹ᵁ U)) hunion.w
  have hT : IsPullback (b.app U) (c.app U ≫ p.app (c ⁻¹ᵁ U))
      (q.app (b ⁻¹ᵁ U) ≫ j.app (q ⁻¹ᵁ (b ⁻¹ᵁ U)))
      (i.app (p ⁻¹ᵁ (c ⁻¹ᵁ U)) ≫
        eqToHom (congrArg (fun V : Z.Opens ↦ Γ(Z, V)) w)) :=
    structureSheaf_isPullback_of_isPushout hpush hAffine U
  have hS : IsPullback (r.app (c ⁻¹ᵁ U)) (p.app (c ⁻¹ᵁ U)) (j.app (r ⁻¹ᵁ (c ⁻¹ᵁ U)))
      (i.app (p ⁻¹ᵁ (c ⁻¹ᵁ U)) ≫
        eqToHom (congrArg (fun V : Z.Opens ↦ Γ(Z, V)) w')) :=
    structureSheaf_isPullback_of_isPushout_of_isAffineHom hunion (c ⁻¹ᵁ U)
  refine isIso_of_isPullback_comparison hT hS
    (asIso (q.app (b ⁻¹ᵁ U)) ≪≫ eqToIso (congrArg (fun V : B.Opens ↦ Γ(B, V)) e))
    (Iso.refl _) (eqToIso (congrArg (fun V : B.Opens ↦ Γ(Z, j ⁻¹ᵁ V)) e))
    ?_ ?_ (c.app U) ?_ ?_
  · show (q.app (b ⁻¹ᵁ U) ≫ eqToHom (congrArg (fun V : B.Opens ↦ Γ(B, V)) e)) ≫
        j.app (r ⁻¹ᵁ (c ⁻¹ᵁ U)) =
      (q.app (b ⁻¹ᵁ U) ≫ j.app (q ⁻¹ᵁ (b ⁻¹ᵁ U))) ≫
        eqToHom (congrArg (fun V : B.Opens ↦ Γ(Z, j ⁻¹ᵁ V)) e)
    rw [Category.assoc, Category.assoc, eqToHom_comp_app j e]
  · show 𝟙 _ ≫ i.app (p ⁻¹ᵁ (c ⁻¹ᵁ U)) ≫
        eqToHom (congrArg (fun V : Z.Opens ↦ Γ(Z, V)) w') =
      (i.app (p ⁻¹ᵁ (c ⁻¹ᵁ U)) ≫ eqToHom (congrArg (fun V : Z.Opens ↦ Γ(Z, V)) w)) ≫
        eqToHom (congrArg (fun V : B.Opens ↦ Γ(Z, j ⁻¹ᵁ V)) e)
    rw [Category.id_comp, Category.assoc, eqToHom_trans]
  · have h : c.app U ≫ r.app (c ⁻¹ᵁ U) =
        (b.app U ≫ q.app (b ⁻¹ᵁ U)) ≫
          eqToHom (congrArg (fun V : B.Opens ↦ Γ(B, V)) e) :=
      (app_comp_eqToHom_of_eq hrc.symm U).symm
    show c.app U ≫ r.app (c ⁻¹ᵁ U) =
      b.app U ≫ q.app (b ⁻¹ᵁ U) ≫ eqToHom (congrArg (fun V : B.Opens ↦ Γ(B, V)) e)
    rw [h, Category.assoc]
  · show c.app U ≫ p.app (c ⁻¹ᵁ U) = (c.app U ≫ p.app (c ⁻¹ᵁ U)) ≫ 𝟙 _
    rw [Category.comp_id]

end AlgebraicGeometry

namespace Stacks.Curves

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))]
  [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]

/-- **A contraction of a rational bridge is an isomorphism on the sections of the structure
sheaf over every open of its target.** This is the identification [Stacks, Tag 0E3M] draws from
the union sequence of [Stacks, Tag 0C4J] and the description of the structure sheaf of the
pushout in [Stacks, Tag 0E25]: over an open of `Y` both `Γ(Y, U)` and `Γ(X, c ⁻¹ᵁ U)` are the
fibre product of the sections on `X'` and on the bridge over the sections on `C ∩ X'`, the
bridge contributing through `Γ(k', b ⁻¹ᵁ U) ≅ Γ(C, …)`. -/
theorem isIso_app_of_isContractionOfRationalBridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} {hC : IsRationalBridge k X C} {Y : Scheme.{u}} {c : X ⟶ Y}
    (hc : IsContractionOfRationalBridge hC c) (U : Y.Opens) :
    IsIso (c.app U) := by
  obtain ⟨hbot, a, b, hpush, hac, hbc⟩ := hc
  subst hac
  have : IsIntegralHom (Scheme.IdealSheafData.inclusion (I := C)
      (J := intersectionWithComplementaryCurveIdeal C) le_sup_left ≫ C.subscheme.toSpecΓ) :=
    isIntegralHom_intersection_toSpec_bridgeSections hdim hnodal hC
  have : CompactSpace C.subscheme :=
    (quasiCompact_iff_compactSpace (C.subschemeι ≫ (X ↘ Spec (.of k)))).mp inferInstance
  have : QuasiSeparatedSpace C.subscheme :=
    (quasiSeparated_iff_quasiSeparatedSpace (C.subschemeι ≫ (X ↘ Spec (.of k)))).mp inferInstance
  exact isIso_app_of_isPushout_of_isPushout
    (isPushout_subscheme_of_inf_eq_bot C (complementaryCurveIdeal C) hbot) hpush
    (fiber_preimage_subset_affine_bridge hdim hnodal hC)
    (fun V ↦ isIso_app_toSpecΓ C.subscheme V) hbc U

/-- A contraction of a rational bridge is an isomorphism on global functions. -/
theorem isIso_appTop_of_isContractionOfRationalBridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} {hC : IsRationalBridge k X C} {Y : Scheme.{u}} {c : X ⟶ Y}
    (hc : IsContractionOfRationalBridge hC c) : IsIso c.appTop :=
  isIso_app_of_isContractionOfRationalBridge hdim hnodal hc ⊤

/-- **`c_* 𝒪_X = 𝒪_Y` for a contraction `c : X ⟶ Y` of a rational bridge.** Invertibility of a
morphism of sheaves of modules is sectionwise, so this is
`Stacks.Curves.isIso_app_of_isContractionOfRationalBridge`. -/
theorem isIso_structureSheafToPushforward_contraction_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} {hC : IsRationalBridge k X C} {Y : Scheme.{u}} {c : X ⟶ Y}
    (hc : IsContractionOfRationalBridge hC c) :
    IsIso (structureSheafToPushforward c) :=
  isIso_structureSheafToPushforward_of_forall_isIso_app c
    (isIso_app_of_isContractionOfRationalBridge hdim hnodal hc)

/-- **The direct images of `𝒪_X` along a contraction of a rational bridge**: the canonical map
`𝒪_Y ⟶ c_* 𝒪_X` is an isomorphism and `R ¹ c_* 𝒪_X = 0`. This is the clause of
[Stacks, Tag 0E3M] that reads "we claim that `c_* 𝒪_X = 𝒪_Y` and `R ¹ c_* 𝒪_X = 0`". -/
@[stacks 0E3M "c_*𝒪_X = 𝒪_Y and R¹c_*𝒪_X = 0"]
theorem isIso_structureSheafToPushforward_and_isZero_rightDerived_one_contraction_bridge
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : HasAtWorstNodalSingularities k X)
    (C : X.IdealSheafData) (hC : IsRationalBridge k X C)
    {Y : Scheme.{u}} (c : X ⟶ Y) (hc : IsContractionOfRationalBridge hC c) :
    IsIso (structureSheafToPushforward c) ∧
      IsZero (((Scheme.Modules.pushforward c).rightDerived 1).obj (structureSheafModule X)) :=
  ⟨isIso_structureSheafToPushforward_contraction_bridge hdim hnodal hc,
    isZero_rightDerived_one_pushforward_ambientStructureSheaf_bridge hdim hnodal hc⟩

end Stacks.Curves

end
