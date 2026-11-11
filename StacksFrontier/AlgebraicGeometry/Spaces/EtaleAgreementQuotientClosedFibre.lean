module

public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Isomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleAgreementQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.FormalAlgebraization
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismAlgebraizationLocallyFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.FppfCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonomorphism

/-!
# A quotient which identifies all pairs over the closed fibre

Let `A` be a ring with an ideal `I`, and let `ε : E ⟶ X'` be an étale surjection and
`q : X' ⟶ X` an étale morphism of algebraic spaces over `Spec A`, with `π = ε ≫ q`
surjective. Suppose that any two points `a, b` of `E` with the same image in `X` and lying over
the closed fibre `Spec (A / I)` have the same image in `X'`. Then the closed fibre
`q₀ : X'_0 ⟶ X_0` of `q` is an isomorphism: it is étale and surjective, and it is a monomorphism,
because two points of `X'_0` with the same image in `X_0` lift fppf locally to points of `E` over
the closed fibre with the same image in `X`.

This is what the quotient of `AlgebraicGeometry.Space.exists_isEtale_quotient_etaleAgreementLocus`
satisfies when the agreement locus contains the closed fibre of `E ×_X E`.

Two morphisms `α, β : E ⟶ X'` with `α ≫ q = β ≫ q` into a space étale over `X` which agree on
the closed fibre agree on every adic fibre: they agree on the open subspace of `E` where the pair
`(α, β)` lands in the open diagonal of `q`, and that open subspace contains the points of the
closed fibre, which are the points of every adic fibre.

## Main results

* `AlgebraicGeometry.Space.isIso_adicFibreMap_zero_of_comp_eq`: the closed fibre of `q` is an
  isomorphism.
* `AlgebraicGeometry.Space.adicFibreMap_eq_of_isEtale_of_adicFibreMap_zero_eq`: two lifts through
  an étale morphism which agree on the closed fibre agree on every adic fibre.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {A : Type u} [CommRing A] {I : Ideal A} {B : BigFppfSite.{u}}
  {hS : B.Contains (Spec (.of A))} {hSn : ∀ n, B.Contains (adicThickening A I n)}

/-- The adic fibre of a morphism `j : G ⟶ F` over the base is the base change of `j` along the
projection `F_n ⟶ F`. -/
theorem isPullback_fst_adicFibreMap {F G : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    {fF : F ⟶ yoneda.obj (baseObject A B hS)} (j : G ⟶ F) (n : ℕ) :
    IsPullback (pullback.fst (j ≫ fF) (yoneda.map (adicThickeningMap A I B hS hSn n)))
      (adicFibreMap A I B hS hSn j rfl n) j
      (pullback.fst fF (yoneda.map (adicThickeningMap A I B hS hSn n))) := by
  refine IsPullback.of_bot ?_ (adicFibreMap_fst A I B hS hSn j rfl n).symm
    (IsPullback.of_hasPullback fF _)
  rw [adicFibreMap_snd]
  exact IsPullback.of_hasPullback (j ≫ fF) _

/-- The structure morphism of the closed fibre `Spec (A / I) ⟶ Spec A`, as a morphism of
represented presheaves. -/
local notation "𝔱" => yoneda.map (adicThickeningMap A I B hS hSn 0)

/-- **The closed fibre of the quotient map is an isomorphism.** Let `ε : E ⟶ X'` be étale and
surjective and `q : X' ⟶ X` étale, with `π = ε ≫ q` surjective, over `Spec A`. If any two
morphisms `a, b : T ⟶ E` with `a ≫ π = b ≫ π` for which `a ≫ π` lies over the closed fibre
`Spec (A / I)` satisfy `a ≫ ε = b ≫ ε`, then the closed fibre `X'_0 ⟶ X_0` of `q` is an
isomorphism. -/
theorem isIso_adicFibreMap_zero_of_comp_eq
    {E X X' : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    (hE : IsAlgebraicSpace B _ hS E) (hX : IsAlgebraicSpace B _ hS X)
    (hX' : IsAlgebraicSpace B _ hS X') {fX : X ⟶ yoneda.obj (baseObject A B hS)}
    {π : E ⟶ X} (hπ : IsSurjective B _ hS π) {ε : E ⟶ X'} {q : X' ⟶ X} (hεq : ε ≫ q = π)
    (hε : IsEtale B _ hS ε) (hεs : IsSurjective B _ hS ε) (hq : IsEtale B _ hS q)
    (h : ∀ {T : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u} (a b : T ⟶ E),
      a ≫ π = b ≫ π → ∀ c : T ⟶ yoneda.obj (adicThickeningObject A I B hS hSn 0),
        a ≫ π ≫ fX = c ≫ yoneda.map (adicThickeningMap A I B hS hSn 0) → a ≫ ε = b ≫ ε) :
    IsIso (adicFibreMap A I B hS hSn q (rfl : q ≫ fX = q ≫ fX) 0) := by
  set q₀ := adicFibreMap A I B hS hSn q (rfl : q ≫ fX = q ≫ fX) 0 with hq₀def
  have hX'₀ : IsAlgebraicSpace B _ hS (pullback (q ≫ fX) 𝔱) :=
    isAlgebraicSpace_adicFibre A I B hS hSn hX' (q ≫ fX) 0
  have hX₀ : IsAlgebraicSpace B _ hS (pullback fX 𝔱) :=
    isAlgebraicSpace_adicFibre A I B hS hSn hX fX 0
  have hsq := isPullback_fst_adicFibreMap (hSn := hSn) (fF := fX) q 0
  have hsqs : IsPullback
      (ObjectProperty.homMk (pullback.fst (q ≫ fX) 𝔱) :
        (⟨pullback (q ≫ fX) 𝔱, hX'₀⟩ : AlgebraicSpaces B _ hS) ⟶ ⟨X', hX'⟩)
      (ObjectProperty.homMk q₀ : (⟨pullback (q ≫ fX) 𝔱, hX'₀⟩ : AlgebraicSpaces B _ hS) ⟶
        ⟨pullback fX 𝔱, hX₀⟩)
      (ObjectProperty.homMk q : (⟨X', hX'⟩ : AlgebraicSpaces B _ hS) ⟶ ⟨X, hX⟩)
      (ObjectProperty.homMk (pullback.fst fX 𝔱) :
        (⟨pullback fX 𝔱, hX₀⟩ : AlgebraicSpaces B _ hS) ⟶ ⟨X, hX⟩) :=
    IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ hsq.w) hsq
  -- `q₀` is étale and surjective.
  have hq₀e : IsEtale B _ hS q₀ := isEtale_of_isPullback B _ hS _ _ _ _ hsqs hq
  have hqs : IsSurjective B _ hS q := by
    have hc : IsSurjective B _ hS (ε ≫ q) := hεq ▸ hπ
    rw [IsSurjective, pointsMap_comp] at hc
    exact Function.Surjective.of_comp hc
  have hq₀s : IsSurjective B _ hS q₀ := isSurjective_of_isPullback B _ hS hsqs hqs
  -- `q₀` is a monomorphism.
  have hεl : Presheaf.IsLocallySurjective (BigFppfOver.topology B _ hS) ε :=
    isLocallySurjective_of_surjective_flat_locallyOfFinitePresentation B _ hS hE hX' ε hεs
      (isFlat_of_isEtale B _ hS hε) (isLocallyOfFinitePresentation_of_isEtale B _ hS hε)
  have hkey : ∀ {T : BigFppfOver B (Spec (.of A)) hS} (x y : yoneda.obj T ⟶ X')
      (c : yoneda.obj T ⟶ yoneda.obj (adicThickeningObject A I B hS hSn 0)),
      x ≫ q = y ≫ q → x ≫ q ≫ fX = c ≫ 𝔱 → x = y := by
    intro T x y c hxy hxc
    have hsheaf : Presieve.IsSheaf (BigFppfOver.topology B _ hS) X' :=
      (isSheaf_iff_isSheaf_of_type _ _).1 hX'.isSheaf
    apply yonedaEquiv.injective
    refine (hsheaf _ (GrothendieckTopology.intersection_covering _
      (Presheaf.imageSieve_mem (BigFppfOver.topology B _ hS) ε (yonedaEquiv x))
      (Presheaf.imageSieve_mem (BigFppfOver.topology B _ hS) ε (yonedaEquiv y)))).isSeparatedFor.ext
      ?_
    rintro V f ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    have ha' : yonedaEquiv.symm a ≫ ε = yoneda.map f ≫ x := by
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, Equiv.apply_symm_apply, ← yonedaEquiv_naturality]
      exact ha
    have hb' : yonedaEquiv.symm b ≫ ε = yoneda.map f ≫ y := by
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, Equiv.apply_symm_apply, ← yonedaEquiv_naturality]
      exact hb
    have hab : yonedaEquiv.symm a ≫ π = yonedaEquiv.symm b ≫ π := by
      rw [← hεq, reassoc_of% ha', reassoc_of% hb', hxy]
    have hfib : yonedaEquiv.symm a ≫ π ≫ fX = (yoneda.map f ≫ c) ≫ 𝔱 := by
      rw [← hεq, Category.assoc, reassoc_of% ha', hxc, Category.assoc]
    have := h _ _ hab _ hfib
    rw [ha', hb'] at this
    have h' := congrArg yonedaEquiv this
    rw [← yonedaEquiv_naturality, ← yonedaEquiv_naturality] at h'
    exact h'
  have hmono : Mono q₀ := by
    refine (NatTrans.mono_iff_mono_app _).2 fun T => (mono_iff_injective _).2 fun x y hxy => ?_
    set xm : yoneda.obj T.unop ⟶ pullback (q ≫ fX) 𝔱 := yonedaEquiv.symm x
    set ym : yoneda.obj T.unop ⟶ pullback (q ≫ fX) 𝔱 := yonedaEquiv.symm y
    have hxym : xm ≫ q₀ = ym ≫ q₀ := by
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact hxy
    have hsnd : xm ≫ pullback.snd (q ≫ fX) 𝔱 = ym ≫ pullback.snd (q ≫ fX) 𝔱 := by
      have := congrArg (· ≫ pullback.snd fX 𝔱) hxym
      simpa only [Category.assoc, hq₀def, adicFibreMap_snd] using this
    have hfst : xm ≫ pullback.fst (q ≫ fX) 𝔱 = ym ≫ pullback.fst (q ≫ fX) 𝔱 := by
      refine hkey _ _ (xm ≫ pullback.snd (q ≫ fX) 𝔱) ?_ ?_
      · have := congrArg (· ≫ pullback.fst fX 𝔱) hxym
        simpa only [Category.assoc, hq₀def, adicFibreMap_fst] using this
      · rw [Category.assoc, pullback.condition, Category.assoc]
    have : xm = ym := pullback.hom_ext hfst hsnd
    have h' := congrArg yonedaEquiv this
    simpa only [xm, ym, Equiv.apply_symm_apply] using h'
  exact isIso_of_isEtale_of_universallyInjective_of_isSurjective B _ hS hX'₀ hX₀ q₀ hq₀e
    (universallyInjective_of_mono B _ hS q₀ hmono) hq₀s

/-- The points of every adic fibre of a presheaf over the base map into `|F|` with the same image
as those of the closed fibre. -/
theorem range_pointsMap_fst_adicFibre_subset {F : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    (fF : F ⟶ yoneda.obj (baseObject A B hS)) (n : ℕ) :
    Set.range (pointsMap B _ hS _
        (pullback.fst fF (yoneda.map (adicThickeningMap A I B hS hSn n)))) ⊆
      Set.range (pointsMap B _ hS _
        (pullback.fst fF (yoneda.map (adicThickeningMap A I B hS hSn 0)))) := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih =>
    rintro _ ⟨z, rfl⟩
    obtain ⟨w, rfl⟩ := surjective_pointsMap_adicFibreSucc fF n z
    refine ih ⟨w, ?_⟩
    rw [← Function.comp_apply (f := pointsMap B _ hS _ _), ← pointsMap_comp, adicFibreSucc_fst]

/-- **Two lifts through an étale morphism agreeing on the closed fibre agree on every adic
fibre.** Let `q : X' ⟶ X` be étale and `α, β : E ⟶ X'` with `α ≫ q = β ≫ q`, over `Spec A`. If
the closed fibres of `α` and `β` agree, so do all their adic fibres.

The pair `(α, β)` lands in the diagonal of `q`, an open immersion, over an open subspace `W` of
`E`, on which `α = β`; the closed fibre of `E` maps into `W`, hence so does every adic fibre,
which has the same points. -/
theorem adicFibreMap_eq_of_isEtale_of_adicFibreMap_zero_eq
    {E X X' : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    (hE : IsAlgebraicSpace B _ hS E) (hX : IsAlgebraicSpace B _ hS X)
    (hX' : IsAlgebraicSpace B _ hS X') {fX : X ⟶ yoneda.obj (baseObject A B hS)}
    {fE : E ⟶ yoneda.obj (baseObject A B hS)} {q : X' ⟶ X} (hq : IsEtale B _ hS q)
    {α β : E ⟶ X'} (hα : α ≫ q ≫ fX = fE) (hβ : β ≫ q ≫ fX = fE) (hαβ : α ≫ q = β ≫ q)
    (h0 : adicFibreMap A I B hS hSn α hα 0 = adicFibreMap A I B hS hSn β hβ 0) (n : ℕ) :
    adicFibreMap A I B hS hSn α hα n = adicFibreMap A I B hS hSn β hβ n := by
  have hD : IsOpenImmersion B _ hS (pullback.diagonal q) :=
    isOpenImmersion_diagonal_of_isUnramified B _ hS hX' hX q (isUnramified_of_isEtale B _ hS hq)
  have hPq : IsAlgebraicSpace B _ hS (pullback q q) :=
    isAlgebraicSpace_pullback B _ hS q q hX' hX' hX
  set l : E ⟶ pullback q q := pullback.lift α β hαβ
  have hl₁ : l ≫ pullback.fst q q = α := pullback.lift_fst _ _ _
  have hl₂ : l ≫ pullback.snd q q = β := pullback.lift_snd _ _ _
  set D := Subfunctor.range (pullback.diagonal q)
  set W := D.preimage l
  have hW : IsOpenSubspace B _ hS W :=
    isOpenSubspace_preimage B _ hS l D hPq hE (isOpenSubspace_subfunctorRange B _ hS hX' hD)
  -- `α` and `β` agree on `W`.
  have hWα : ∀ {T : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u} (k : T ⟶ E),
      Subfunctor.range k ≤ W → k ≫ α = k ≫ β := by
    intro T k hk
    have hkD : Subfunctor.range (k ≫ l) ≤ D := by
      rw [Subfunctor.range_comp, Subfunctor.image_le_iff]
      exact hk
    set m := Subfunctor.lift _ hkD
    have hm : m ≫ D.ι = k ≫ l := Subfunctor.lift_ι _ _
    have : Mono (pullback.diagonal q) := inferInstance
    have hmD : m ≫ inv (Subfunctor.toRange (pullback.diagonal q)) ≫ pullback.diagonal q =
        k ≫ l := by
      rw [(IsIso.inv_comp_eq _).mpr (Subfunctor.toRange_ι _).symm, hm]
    have h₁ := congrArg (· ≫ pullback.fst q q) hmD
    have h₂ := congrArg (· ≫ pullback.snd q q) hmD
    simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id]
      at h₁ h₂
    rw [hl₁] at h₁
    rw [hl₂] at h₂
    exact h₁.symm.trans h₂
  -- The closed fibre maps into `W`.
  set t₀ := yoneda.map (adicThickeningMap A I B hS hSn 0)
  have h0' : pullback.fst fE t₀ ≫ α = pullback.fst fE t₀ ≫ β := by
    have h₁ := adicFibreMap_fst A I B hS hSn α hα 0
    have h₂ := adicFibreMap_fst A I B hS hSn β hβ 0
    rw [← h₁, ← h₂, h0]
  have hW0 : Subfunctor.range (pullback.fst fE t₀) ≤ W := by
    rw [← Subfunctor.image_le_iff, ← Subfunctor.range_comp]
    have : pullback.fst fE t₀ ≫ l = (pullback.fst fE t₀ ≫ α) ≫ pullback.diagonal q := by
      apply pullback.hom_ext
      · rw [Category.assoc, hl₁, Category.assoc, pullback.diagonal_fst, Category.comp_id]
      · rw [Category.assoc, hl₂, Category.assoc, pullback.diagonal_snd, Category.comp_id, h0']
    rw [this]
    exact (Subfunctor.range_comp_le _ _).trans (le_refl _)
  -- Hence so does every adic fibre.
  have hWn : Subfunctor.range (pullback.fst fE (yoneda.map (adicThickeningMap A I B hS hSn n)))
      ≤ W := by
    refine le_trans ?_ (eq_openSubspaceOfPoints_range_pointsMap_ι B _ hS hE hW).ge
    rintro V _ ⟨x, rfl⟩
    rw [mem_openSubspaceOfPoints_iff, ← yonedaEquiv_symm_naturality_right, pointsMap_comp]
    refine (Set.range_comp_subset_range _ _).trans
      ((range_pointsMap_fst_adicFibre_subset fE n).trans ?_)
    rintro _ ⟨z, rfl⟩
    refine ⟨pointsMap B _ hS _ (Subfunctor.lift _ hW0) z, ?_⟩
    rw [← Function.comp_apply (f := pointsMap B _ hS _ W.ι), ← pointsMap_comp, Subfunctor.lift_ι]
  have hfst := hWα _ hWn
  apply pullback.hom_ext
  · rw [adicFibreMap_fst, adicFibreMap_fst, hfst]
  · rw [adicFibreMap_snd, adicFibreMap_snd]

end AlgebraicGeometry.Space

end
