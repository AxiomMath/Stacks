module

public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.SchemeTheoreticUnion
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.Contraction

/-!
# The direct image of the structure sheaf under the contraction of a rational tail

Let `k` be a field and let `X` be a proper one-dimensional scheme over `k` with at-worst-nodal
singularities and `H⁰(X, 𝒪_X) = k`. Let `C ⊆ X` be a rational tail (Tag 0E3H), let
`X' ⊆ X` be the scheme-theoretic closure of the complement of `C`, and let `c : X ⟶ X'` be a
contraction of `C`, that is, a morphism restricting to the identity on `X'` and carrying `C` to
the attaching point `x` through the canonical morphism `C ⟶ Spec κ(x)`. Then the canonical map
`𝒪_{X'} ⟶ c_*𝒪_X` of sheaves of rings is an isomorphism.

The proof is a direct computation on sections rather than the long exact sequence of the union
sequence used in the source. Fix an open `U ⊆ X'` and put `V = c⁻¹(U)`. Restriction along the
closed immersion `X' ⟶ X` is a retraction of `c.app U`, because `c` restricts to the identity on
`X'`; so `c.app U` is injective and it suffices to see that for `s ∈ 𝒪_X(V)` the section
`t = c.app U (s|_{X'}) - s` vanishes. It vanishes on `X'` by construction. It vanishes on `C`
because `c` carries `C` to the single point `x`: either `V` misses `C` altogether, and then
`𝒪_C(V ∩ C)` is the zero ring, or `V` contains all of `C`, and then the restriction of `t` to `C`
is a global function on `C`, which by the rational-tail hypothesis is determined by its value in
the residue field `κ(x)` — and that value is computed by restricting `t` to `X'` first, so it is
zero. Finally a section vanishing on both `C` and `X'` vanishes, because `X` is the
scheme-theoretic union of the two (Tag 0E3H, using that a nodal curve is reduced).

## Main results

* `Stacks.Curves.eq_zero_of_inf_eq_bot` — a section of the structure sheaf vanishing on two
  closed subschemes whose scheme-theoretic union is the whole scheme is zero.
* `Stacks.Curves.isIso_app_of_isContractionOfRationalTail` — a contraction of a rational tail of
  a reduced scheme induces an isomorphism on sections over every open of the target.
* `Stacks.Curves.isIso_appTop_of_isContractionOfRationalTail` — in particular it induces an
  isomorphism on global functions.
* `Stacks.Curves.isIso_structureSheaf_to_pushforward_of_isContraction` — the canonical map
  `𝒪_{X'} ⟶ c_*𝒪_X` of sheaves of rings is an isomorphism, for any contraction `c` of a rational
  tail of a reduced scheme.
* `Stacks.Curves.isIso_structureSheaf_to_pushforward` — the same statement under the standing
  hypotheses of Tag 0E3H, where reducedness is supplied by nodality.

## Implementation notes

The statement is about an arbitrary contraction `c` of the rational tail, characterised by
`AlgebraicGeometry.IsContractionOfRationalTail`, rather than about the canonical contraction: the
two restrictions recorded by `IsContractionOfRationalTail` are all the proof uses.

## References

* [Stacks Project, Tag 0E3H](https://stacks.math.columbia.edu/tag/0E3H)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.Curves

section Auxiliary

/-- If the preimage of `U` under `f` is `V`, then a section over `U` whose image under
`f.appLE U V` vanishes already has vanishing image under `f.app U`. -/
private theorem app_eq_zero_of_appLE_eq_zero {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens}
    {V : X.Opens} (h : f ⁻¹ᵁ U = V) {t : Γ(Y, U)}
    (ht : (Scheme.Hom.appLE f U V h.ge).hom t = 0) :
    (Scheme.Hom.app f U).hom t = 0 := by
  subst h
  rwa [Scheme.Hom.appLE_eq_app] at ht

/-- A morphism of schemes equal to the identity acts as the identity on sections. -/
private theorem appLE_eq_id {X : Scheme.{u}} {g : X ⟶ X} (hg : g = 𝟙 X) (U : X.Opens)
    (e : U ≤ g ⁻¹ᵁ U) : Scheme.Hom.appLE g U U e = 𝟙 _ := by
  subst hg
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
  exact X.presheaf.map_id _

/-- A section of the structure sheaf over an open `V` which vanishes on two closed subschemes
whose scheme-theoretic union is the whole scheme is zero. Closed subschemes are given by ideal
sheaves, so the scheme-theoretic union of the subschemes cut out by `I` and `J` is cut out by
`I ⊓ J`, and it is all of the ambient scheme exactly when `I ⊓ J = ⊥`. -/
theorem eq_zero_of_inf_eq_bot {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I ⊓ J = ⊥)
    {V : X.Opens} (t : Γ(X, V))
    (hI : (Scheme.Hom.app I.subschemeι V).hom t = 0)
    (hJ : (Scheme.Hom.app J.subschemeι V).hom t = 0) : t = 0 := by
  refine TopCat.Presheaf.section_ext X.sheaf V t 0 ?_
  intro x hx
  obtain ⟨W, hWmem, hxW, hWV⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hx
  have key : (X.presheaf.map (homOfLE hWV).op).hom t = 0 := by
    have hker : ∀ K : X.IdealSheafData, (Scheme.Hom.app K.subschemeι V).hom t = 0 →
        (X.presheaf.map (homOfLE hWV).op).hom t ∈ K.ideal ⟨W, hWmem⟩ := by
      intro K hK
      rw [← Scheme.IdealSheafData.ker_subschemeι_app K ⟨W, hWmem⟩]
      have hnat := Scheme.Hom.naturality K.subschemeι (homOfLE hWV).op
      have hnat' := congrArg (fun φ : Γ(X, V) ⟶ _ => φ.hom t) hnat
      simp only [CommRingCat.comp_apply] at hnat'
      simp only [RingHom.mem_ker, hnat', hK, map_zero]
    have hmem : (X.presheaf.map (homOfLE hWV).op).hom t ∈ (I ⊓ J).ideal ⟨W, hWmem⟩ := by
      rw [Scheme.IdealSheafData.ideal_inf]
      exact ⟨hker I hI, hker J hJ⟩
    rw [h, Scheme.IdealSheafData.ideal_bot] at hmem
    simpa using hmem
  have hg := TopCat.Presheaf.germ_res_apply X.sheaf.presheaf (homOfLE hWV) x hxW t
  have hzero : (ConcreteCategory.hom (X.sheaf.presheaf.map (homOfLE hWV).op)) t = 0 := key
  rw [← hg, hzero, map_zero, map_zero]

/-- Evaluation at a point only depends on the point, not on the proof that it lies in the
open set. -/
private theorem evaluation_eq_zero_congr {X : Scheme.{u}} {V : X.Opens} {z w : X} (h : z = w)
    {hz : z ∈ V} {hw : w ∈ V} {t : Γ(X, V)} (ht : (X.evaluation V z hz).hom t = 0) :
    (X.evaluation V w hw).hom t = 0 := by
  subst h; exact ht

/-- A section over an open on which global evaluation at a point is an isomorphism is
determined by its value in the residue field at that point. -/
private theorem eq_zero_of_evaluation_eq_zero {Z : Scheme.{u}} (z : Z)
    (hz : IsIso (Z.Γevaluation z)) {W : Z.Opens} (hW : W = ⊤) {hzW : z ∈ W} {s : Γ(Z, W)}
    (hs : (Z.evaluation W z hzW).hom s = 0) : s = 0 := by
  subst hW
  have : (inv (Z.Γevaluation z)).hom ((Z.Γevaluation z).hom s) = s := by
    rw [← CommRingCat.comp_apply, IsIso.hom_inv_id]
    rfl
  rw [← this, show (Z.Γevaluation z).hom s = 0 from hs, map_zero]

/-- The map induced by a morphism of schemes on residue fields is injective, being a
homomorphism of fields. -/
private theorem eq_zero_of_residueFieldMap_eq_zero {A B : Scheme.{u}} (f : A ⟶ B) (a : A)
    {v : B.residueField (f a)} (h : (Scheme.Hom.residueFieldMap f a).hom v = 0) : v = 0 :=
  (Scheme.Hom.residueFieldMap f a).hom.injective (by rw [h, map_zero])

/-- An open subset of the spectrum of a field is either empty or everything. -/
private theorem eq_top_or_eq_bot_of_subsingleton {T : TopCat.{u}} [Subsingleton T]
    (W : Opens T) : W = ⊤ ∨ W = ⊥ := by
  rcases isEmpty_or_nonempty W with hW | ⟨⟨z, hz⟩⟩
  · right
    ext y
    simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    exact fun hy => hW.elim ⟨y, hy⟩
  · left
    ext y
    simpa using (Subsingleton.elim y z) ▸ hz

end Auxiliary

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  {C : X.IdealSheafData}

/-- The restriction to a rational tail of a section that vanishes on the closure of the
complement, over the preimage of an open of that closure under a contraction, is zero. This is
the step where the rational-tail hypothesis `Γ(C, 𝒪_C) ≅ κ(x)` is used: the preimage of an open
either misses the tail entirely, or contains all of it, and in the second case the restriction
is a global function on the tail and therefore determined by its value at the attaching
point. -/
theorem subschemeι_app_eq_zero_of_complementaryCurveι_app_eq_zero
    (hC : IsRationalTail k X C) {c : X ⟶ complementaryCurve C}
    (hc : IsContractionOfRationalTail hC c) (U : (complementaryCurve C).Opens)
    {t : Γ(X, c ⁻¹ᵁ U)}
    (ht : (Scheme.Hom.app (complementaryCurveι C) (c ⁻¹ᵁ U)).hom t = 0) :
    (Scheme.Hom.app C.subschemeι (c ⁻¹ᵁ U)).hom t = 0 := by
  obtain ⟨p, hp, hjc⟩ := hc.2
  -- the preimage of `U` in the tail is the preimage of `p ⁻¹ᵁ U` under the canonical map
  have hjV : C.subschemeι ⁻¹ᵁ (c ⁻¹ᵁ U) = canonicalMapToAttachingPoint hC ⁻¹ᵁ (p ⁻¹ᵁ U) := by
    change (C.subschemeι ≫ c) ⁻¹ᵁ U = (canonicalMapToAttachingPoint hC ≫ p) ⁻¹ᵁ U
    rw [hjc]
  rcases eq_top_or_eq_bot_of_subsingleton (p ⁻¹ᵁ U) with hpU | hpU
  · -- the preimage contains the whole tail
    have hVtop : C.subschemeι ⁻¹ᵁ (c ⁻¹ᵁ U) = ⊤ := by rw [hjV, hpU]; simp
    have hxtV : hC.attachingPoint ∈ C.subschemeι ⁻¹ᵁ (c ⁻¹ᵁ U) := hVtop ▸ trivial
    -- the attaching point lies on the closure of the complement as well
    obtain ⟨z⟩ : Nonempty (Spec (C.subscheme.residueField hC.attachingPoint)) := inferInstance
    have hiy : complementaryCurveι C (p z) = C.subschemeι hC.attachingPoint := by
      have h1 := congrArg
        (fun f : Spec (C.subscheme.residueField hC.attachingPoint) ⟶ X => f.base z) hp
      simpa [Scheme.fromSpecResidueField_apply] using h1
    have hpzV : p z ∈ complementaryCurveι C ⁻¹ᵁ (c ⁻¹ᵁ U) := by
      change complementaryCurveι C (p z) ∈ c ⁻¹ᵁ U
      rw [hiy]; exact hxtV
    -- the value of `t` at the attaching point, computed on the closure of the complement
    have hval : (X.evaluation (c ⁻¹ᵁ U) (complementaryCurveι C (p z)) hpzV).hom t = 0 := by
      have hnat := Scheme.evaluation_naturality_apply (complementaryCurveι C) (p z) hpzV t
      rw [ht, map_zero] at hnat
      exact eq_zero_of_residueFieldMap_eq_zero _ _ hnat
    have hval' :
        (X.evaluation (c ⁻¹ᵁ U) (C.subschemeι hC.attachingPoint) hxtV).hom t = 0 :=
      evaluation_eq_zero_congr hiy hval
    -- transport it to the tail
    have hnat := Scheme.evaluation_naturality_apply C.subschemeι hC.attachingPoint hxtV t
    rw [hval', map_zero] at hnat
    exact eq_zero_of_evaluation_eq_zero hC.attachingPoint
      hC.isIso_Γevaluation_attachingPoint hVtop hnat.symm
  · -- the preimage misses the tail
    have hVbot : C.subschemeι ⁻¹ᵁ (c ⁻¹ᵁ U) = ⊥ := by rw [hjV, hpU]; simp
    have : Subsingleton Γ(C.subscheme, C.subschemeι ⁻¹ᵁ (c ⁻¹ᵁ U)) := hVbot ▸ inferInstance
    exact Subsingleton.elim _ _

/-- A contraction of a rational tail of a reduced scheme induces an isomorphism on sections
over every open subset of the closure of the complement. -/
theorem isIso_app_of_isContractionOfRationalTail [IsReduced X] (hC : IsRationalTail k X C)
    {c : X ⟶ complementaryCurve C} (hc : IsContractionOfRationalTail hC c)
    (U : (complementaryCurve C).Opens) : IsIso (Scheme.Hom.app c U) := by
  -- the contraction restricts to the identity, so the preimage of `U` pulls back to `U`
  have hiV : complementaryCurveι C ⁻¹ᵁ (c ⁻¹ᵁ U) = U := by
    change (complementaryCurveι C ≫ c) ⁻¹ᵁ U = U
    rw [hc.1]; simp
  -- restriction along the closed immersion is a retraction of `c.app U`
  have hsplit : Scheme.Hom.app c U ≫
      Scheme.Hom.appLE (complementaryCurveι C) (c ⁻¹ᵁ U) U hiV.ge = 𝟙 _ := by
    rw [← Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_comp_appLE]
    exact appLE_eq_id hc.1 U _
  -- and it is also a section of it
  have hsection : Scheme.Hom.appLE (complementaryCurveι C) (c ⁻¹ᵁ U) U hiV.ge ≫
      Scheme.Hom.app c U = 𝟙 _ := by
    ext s
    have hid := congrArg (fun φ : Γ((complementaryCurve C), U) ⟶ _ => φ.hom
      ((Scheme.Hom.appLE (complementaryCurveι C) (c ⁻¹ᵁ U) U hiV.ge).hom s)) hsplit
    simp only [CommRingCat.comp_apply, CommRingCat.id_apply] at hid
    have hres : (Scheme.Hom.app (complementaryCurveι C) (c ⁻¹ᵁ U)).hom
        ((Scheme.Hom.app c U).hom
          ((Scheme.Hom.appLE (complementaryCurveι C) (c ⁻¹ᵁ U) U hiV.ge).hom s) - s) = 0 := by
      refine app_eq_zero_of_appLE_eq_zero _ hiV ?_
      rw [map_sub, hid, sub_self]
    have hzero := eq_zero_of_inf_eq_bot (inf_complementaryCurveIdeal_eq_bot C) _
      (subschemeι_app_eq_zero_of_complementaryCurveι_app_eq_zero hC hc U hres) hres
    rw [sub_eq_zero] at hzero
    simpa using hzero
  exact ⟨_, hsplit, hsection⟩

/-- A contraction of a rational tail of a reduced scheme induces an isomorphism on global
functions: `Γ(X', 𝒪_{X'}) ≅ Γ(X, 𝒪_X)`. -/
theorem isIso_appTop_of_isContractionOfRationalTail [IsReduced X] (hC : IsRationalTail k X C)
    {c : X ⟶ complementaryCurve C} (hc : IsContractionOfRationalTail hC c) :
    IsIso c.appTop :=
  isIso_app_of_isContractionOfRationalTail hC hc ⊤

/-- A contraction of a rational tail of a reduced scheme induces an isomorphism
`𝒪_{X'} ⟶ c_*𝒪_X` of sheaves of rings. -/
theorem isIso_structureSheaf_to_pushforward_of_isContraction [IsReduced X]
    (hC : IsRationalTail k X C) {c : X ⟶ complementaryCurve C}
    (hc : IsContractionOfRationalTail hC c) : IsIso c.toRingCatSheafHom := by
  refine TopCat.Sheaf.isIso_iff_isIso_basis (B := id (α := (complementaryCurve C).Opens)) ?_ ?_
  · rw [Set.range_id]
    refine Opens.isBasis_iff_nbhd.2 ?_
    intro U x hx
    exact ⟨U, Set.mem_univ _, hx, le_rfl⟩
  · intro U
    change IsIso ((forget₂ CommRingCat RingCat).map (Scheme.Hom.app c U))
    have := isIso_app_of_isContractionOfRationalTail hC hc U
    infer_instance

/-- Let `X` be a proper one-dimensional scheme over a field `k` with at-worst-nodal singularities
and with only constant global functions, let `C ⊆ X` be a rational tail and let `c : X ⟶ X'` be
a contraction of `C` onto the scheme-theoretic closure `X'` of the complement of `C`. Then the
canonical map `𝒪_{X'} ⟶ c_*𝒪_X` of sheaves of rings is an isomorphism. -/
theorem isIso_structureSheaf_to_pushforward (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    (_hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : HasAtWorstNodalSingularities k X) (C : X.IdealSheafData)
    (hC : IsRationalTail k X C) {c : X ⟶ complementaryCurve C}
    (hc : IsContractionOfRationalTail hC c) : IsIso c.toRingCatSheafHom := by
  have : IsReduced X := isReduced_of_hasAtWorstNodalSingularities k X hnodal
  exact isIso_structureSheaf_to_pushforward_of_isContraction hC hc

end Stacks.Curves

end
