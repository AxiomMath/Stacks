module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple.OpenEnlargement
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension

/-!
# Induction by enlarging a quasi-compact open subspace

## Main results

* `AlgebraicGeometry.Space.qcqs_induction_on_enlargement` is **Stacks 09IT**: a property of
  the quasi-compact open subspaces of a quasi-compact quasi-separated algebraic space which
  holds for a fixed one and is inherited across elementary distinguished squares with affine
  étale member holds for the whole space.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

attribute [-instance] CategoryTheory.Limits.Types.instHasPushoutsType in
/-- **Stacks 09IT.** Let `X` be a quasi-compact quasi-separated algebraic space and let
`W ⊆ X` be a quasi-compact open subspace. A property `P` of the quasi-compact open subspaces
of `X` which holds for `W`, and which for every elementary distinguished square
`(W₁ ⊆ W₂, f : V ⟶ W₂)` with `W₁`, `W₂` quasi-compact open subspaces of `X` containing `W`
and `V` affine passes from `W₁` to `W₂`, holds for `X`. -/
@[stacks 09IT]
public theorem qcqs_induction_on_enlargement
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS)
    (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (W : Subfunctor X.1) (hWopen : IsOpenSubspace B S hS W)
    (hWqc : IsQuasiCompactSpace B S hS W.toFunctor)
    (P : Subfunctor X.1 → Prop) (hPW : P W)
    (hstep : ∀ (W₁ W₂ : Subfunctor X.1) (hW₁ : IsOpenSubspace B S hS W₁)
      (hW₂ : IsOpenSubspace B S hS W₂),
      IsQuasiCompactSpace B S hS W₁.toFunctor →
      IsQuasiCompactSpace B S hS W₂.toFunctor →
      ∀ hle : W₁ ≤ W₂, W ≤ W₁ →
      ∀ {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : V ⟶ W₂.toFunctor),
        IsAffineSpace B S hS V →
        IsElementaryDistinguishedSquare B S hS hW₂.1
          (Subfunctor.range (Subfunctor.homOfLe hle)) f →
        P W₁ → P W₂) :
    P (⊤ : Subfunctor X.1) := by
  classical
  refine qcqs_induction_on_self B S hS hZ X hXqc hXqs
    (fun Y g => IsOpenImmersion B S hS g → Mono g →
      ∀ D : Subfunctor X.1, IsOpenSubspace B S hS D →
        IsQuasiCompactSpace B S hS D.toFunctor → W ≤ D →
        Set.range (pointsMap B S hS D.toFunctor D.ι) =
          Set.range (pointsMap B S hS W.toFunctor W.ι) ∪
            Set.range (pointsMap B S hS Y g) → P D) ?_ ?_
    (isOpenImmersion_id B S hS X.1) inferInstance ⊤
    (AlgebraicGeometry.Space.isOpenSubspace_top X.2)
    (IsQuasiCompactSpace.of_iso B S hS hXqc (asIso (⊤ : Subfunctor X.1).ι).symm)
    le_top ?_
  · intro Vobj hVaff hgopen hgmono D hDopen hDqc _hWD hDrange
    have := hgmono
    have hVobjalg : IsAlgebraicSpace B S hS Vobj.1.left.1 := Vobj.1.left.property
    have hRopen : IsOpenSubspace B S hS (Subfunctor.range Vobj.1.hom.hom) :=
      isOpenSubspace_range_of_open B S hS Vobj.1.hom.hom hVobjalg hgopen
    obtain ⟨W', hW'open, hWW', f, hW'range, _hcomm, hsq⟩ :=
      open_union_square B S hS X.2 W (Subfunctor.range Vobj.1.hom.hom) hWopen hRopen
    have hW'D : W' = D :=
      openSubspace_eq_of_pointsMap_range_eq B S hS X.2 W' D hW'open hDopen
        (by rw [hW'range, hDrange, range_pointsMap_range B S hS Vobj.1.hom.hom])
    rw [← hW'D]
    exact hstep W W' hWopen hW'open hWqc (by rw [hW'D]; exact hDqc) hWW' le_rfl f
      (IsAffineSpace.of_iso hVaff (asIso (Subfunctor.toRange Vobj.1.hom.hom)))
      hsq hPW
  · intro Wobj Vobj U f _hcompf hsqf _hWqcobj _hWqsobj hUqc hVaff hQU _hQV
      _hQpb hgopen hgmono D hDopen hDqc hWD hDrange
    have := hgmono
    have hWpalg : IsAlgebraicSpace B S hS Wobj.1.left.1 := Wobj.1.left.property
    have hYopen : IsOpenSubspace B S hS (Subfunctor.range Wobj.1.hom.hom) :=
      isOpenSubspace_range_of_open B S hS Wobj.1.hom.hom hWpalg hgopen
    obtain ⟨A, V₄, f₄, hsq₄, hV₄aff, hApts⟩ :=
      exists_transported_square B S hS hWpalg W hWopen
        (Subfunctor.range Wobj.1.hom.hom) hYopen Wobj.1.hom.hom
        (asIso (Subfunctor.toRange Wobj.1.hom.hom))
        (Subfunctor.toRange_ι Wobj.1.hom.hom) U f hsqf hVaff
    exact enlargement_step B S hS X.2 W hWopen hWqc P hstep
      (Subfunctor.range Wobj.1.hom.hom) hYopen Wobj.1.hom.hom
      (range_pointsMap_range B S hS Wobj.1.hom.hom) U hsqf.isOpenSubspace hUqc
      (hQU (isOpenImmersion_comp B S hS U.ι Wobj.1.hom.hom
        hsqf.isOpenSubspace.2 hgopen) inferInstance)
      A f₄ hsq₄ hV₄aff hApts D hDopen hDqc hWD hDrange
  · rw [pointsMap_id, Set.range_id, Set.union_univ]
    exact Set.range_eq_univ.mpr (pointsMap_surjective_of_iso B S hS
      (asIso (⊤ : Subfunctor X.1).ι))

end AlgebraicGeometry.Space

end
