module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraizationMorphismExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperTowerAlgebraization

/-!
# Grothendieck's algebraization of morphisms of algebraic spaces

Stacks 0A4Z: for `A` Noetherian and `I`-adically complete, `X` proper over `Spec A` and `Y`
separated of finite type over `Spec A`, a compatible system of morphisms between the
infinitesimal fibres over `Spec (A / Iⁿ)` comes from a unique morphism `X ⟶ Y` over `Spec A`.
The results here take Stacks 08BG as an explicit hypothesis.

## Main results

* Stacks 0A4Z, for algebraic spaces over an affine `V`:
  `AlgebraicGeometry.Space.existsUnique_algebraization_fibreMaps_of_closedSubspaceTowerAlgebraizes`
* `AlgebraicGeometry.Space.existsUnique_algebraization_of_closedSubspaceTowerAlgebraizes`: the
  general form, for a target separated and locally of finite type over an algebraic space `Q`.
* `AlgebraicGeometry.Space.thickeningMapsAlgebraize_of_closedSubspaceTowerAlgebraizes`: the form
  `AlgebraicGeometry.Space.ThickeningMapsAlgebraize`.
* `AlgebraicGeometry.Space.hasProperTowerAlgebraization_of_closedSubspaceTowerAlgebraizes`: the
  form `AlgebraicGeometry.Space.HasProperTowerAlgebraization`, for a target separated and locally
  of finite type over `S`.
* `AlgebraicGeometry.Space.fibreSpaceIsoPullbackOfHom`: the infinitesimal fibres as fibre
  products.

## References

* [Stacks Project, Tag 0A4Z](https://stacks.math.columbia.edu/tag/0A4Z)
* [Stacks Project, Remark 0GHK](https://stacks.math.columbia.edu/tag/0GHK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

section Situation

variable {V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  {I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)}

/-- **Algebraization of a compatible system of morphisms into a space separated and locally of
finite type over a base, given Stacks 08BG.** -/
theorem existsUnique_algebraization_of_closedSubspaceTowerAlgebraizes
    [_root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)]
    [IsAdicComplete I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
    (h08BG : ∀ (W : AlgebraicSpaces B S hS) (f : W ⟶ schemeSpace V),
      ClosedSubspaceTowerAlgebraizes V I f)
    {X : AlgebraicSpaces B S hS} (fX : X ⟶ schemeSpace V) (hX : IsProper B S hS fX.hom)
    {Q T : AlgebraicSpaces B S hS} (q : X ⟶ Q) (t : T ⟶ Q)
    (htsep : IsSeparated B S hS t.hom) (htlft : IsLocallyOfFiniteType B S hS t.hom)
    (g : ∀ n, fibreSpace V I fX n ⟶ T)
    (hg : ∀ n, g n ≫ t = fibreInclusion V I fX n ≫ q)
    (hc : ∀ n, fibreTransition V I fX (Nat.le_succ n) ≫ g (n + 1) = g n) :
    ∃! h : {h : X ⟶ T // h ≫ t = q}, ∀ n, fibreInclusion V I fX n ≫ h.1 = g n := by
  obtain ⟨h, hq, hn⟩ :=
    exists_comp_eq_of_closedSubspaceTowerAlgebraizes h08BG hX htsep htlft hg hc
  refine ⟨⟨h, hq⟩, hn, fun h' hh' => Subtype.ext ?_⟩
  exact eq_of_forall_fibreInclusion_comp_eq V I fX hX t htsep h'.1 h
    (h'.2.trans hq.symm) fun n => (hh' n).trans (hn n).symm

/-- **Stacks 0A4Z in the tower form of `AlgebraicGeometry.Space.ThickeningMapsAlgebraize`, given
Stacks 08BG.** -/
theorem thickeningMapsAlgebraize_of_closedSubspaceTowerAlgebraizes
    [_root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)]
    (h08BG : ∀ (W : AlgebraicSpaces B S hS) (f : W ⟶ schemeSpace V),
      ClosedSubspaceTowerAlgebraizes V I f) :
    ThickeningMapsAlgebraize V I := by
  intro hcomp X Y p q hp hqsep hqft g hg hc
  have := hcomp
  obtain ⟨⟨h, hq⟩, hh, huniq⟩ := existsUnique_algebraization_of_closedSubspaceTowerAlgebraizes
    h08BG p hp p q hqsep hqft.1 g hg fun n => hc n (n + 1) (Nat.le_succ n)
  exact ⟨h, ⟨hq, hh⟩, fun h' ⟨hq', hh'⟩ => congrArg Subtype.val (huniq ⟨h', hq'⟩ hh')⟩

/-- `Spec (A / Iⁿ)` is isomorphic to its image in `V`. -/
theorem isIso_toRange_yoneda_map_adicCompletionQuotientObjHom (V : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) (n : ℕ) :
    IsIso (Subfunctor.toRange (yoneda.map (adicCompletionQuotientObjHom B S hS V I n))) := by
  have : Mono (adicCompletionQuotientObjHom B S hS V I n) :=
    (BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance
  have : Mono (Subfunctor.toRange (yoneda.map (adicCompletionQuotientObjHom B S hS V I n))) :=
    mono_of_mono_fac (Subfunctor.toRange_ι _)
  exact isIso_of_mono_of_epi _

/-- The closed subspace `Spec (A / Iⁿ) ⊆ V`, identified with `Spec (A / Iⁿ)`. -/
def adicQuotientSubspaceIso (V : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) (n : ℕ) :
    (adicQuotientSubspace V I n).1.toFunctor ≅
      yoneda.obj (adicCompletionQuotientObj B S hS V I n) :=
  (@asIso _ _ _ _ (Subfunctor.toRange (yoneda.map (adicCompletionQuotientObjHom B S hS V I n)))
    (isIso_toRange_yoneda_map_adicCompletionQuotientObjHom V I n)).symm

/-- The identification `adicQuotientSubspaceIso`, followed by `Spec (A / Iⁿ) → V`, is the inclusion
of the closed subspace. -/
theorem adicQuotientSubspaceIso_hom_comp (V : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) (n : ℕ) :
    (adicQuotientSubspaceIso V I n).hom ≫ yoneda.map (adicCompletionQuotientObjHom B S hS V I n) =
      (adicQuotientSubspace V I n).1.ι := by
  have := isIso_toRange_yoneda_map_adicCompletionQuotientObjHom V I n
  change inv (Subfunctor.toRange (yoneda.map (adicCompletionQuotientObjHom B S hS V I n))) ≫ _ =
    (Subfunctor.range (yoneda.map (adicCompletionQuotientObjHom B S hS V I n))).ι
  rw [IsIso.inv_comp_eq, Subfunctor.toRange_ι]

/-- **The infinitesimal fibre `Y ×_V Spec (A / Iⁿ)`, as a subfunctor, is the fibre product.** -/
theorem isPullback_fibreInclusion {Y : AlgebraicSpaces B S hS} (p : Y ⟶ schemeSpace V)
    (n : ℕ) :
    IsPullback (fibreInclusion V I p n).hom
      ((adicQuotientSubspace V I n).1.fromPreimage p.hom ≫ (adicQuotientSubspaceIso V I n).hom)
      p.hom (yoneda.map (adicCompletionQuotientObjHom B S hS V I n)) := by
  refine (Subfunctor.isPullback_preimage p.hom (adicQuotientSubspace V I n).1).flip.of_iso
    (Iso.refl _) (Iso.refl _) (adicQuotientSubspaceIso V I n) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · exact (Category.id_comp _).symm
  · simp
  · rw [Iso.refl_hom, Category.comp_id]
    exact (adicQuotientSubspaceIso_hom_comp V I n).symm

/-- The infinitesimal fibre and the fibre product, identified. -/
def fibreSpaceIsoPullback {Y : AlgebraicSpaces B S hS} (p : Y ⟶ schemeSpace V) (n : ℕ) :
    (fibreSpace V I p n).1 ≅
      pullback p.hom (yoneda.map (adicCompletionQuotientObjHom B S hS V I n)) :=
  (isPullback_fibreInclusion (I := I) p n).isoPullback

/-- `fibreSpaceIsoPullback`, followed by the first projection, is the inclusion of the
infinitesimal fibre. -/
@[reassoc (attr := simp)]
theorem fibreSpaceIsoPullback_hom_fst {Y : AlgebraicSpaces B S hS} (p : Y ⟶ schemeSpace V)
    (n : ℕ) : (fibreSpaceIsoPullback (I := I) p n).hom ≫ pullback.fst _ _ =
      (fibreInclusion V I p n).hom :=
  IsPullback.isoPullback_hom_fst _

/-- `AlgebraicGeometry.Space.isPullback_fibreInclusion` for a morphism to the presheaf
represented by `V`. -/
theorem isPullback_fibreInclusion_of_hom {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (p : Y ⟶ yoneda.obj V) (n : ℕ) :
    IsPullback (fibreInclusion V I
        (ObjectProperty.homMk p : (⟨Y, hY⟩ : AlgebraicSpaces B S hS) ⟶ schemeSpace V) n).hom
      ((adicQuotientSubspace V I n).1.fromPreimage p ≫ (adicQuotientSubspaceIso V I n).hom)
      p (yoneda.map (adicCompletionQuotientObjHom B S hS V I n)) :=
  isPullback_fibreInclusion _ n

/-- The infinitesimal fibre of a morphism to the presheaf represented by `V`, identified with the
fibre product. -/
def fibreSpaceIsoPullbackOfHom {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (p : Y ⟶ yoneda.obj V) (n : ℕ) :
    (fibreSpace V I
        (ObjectProperty.homMk p : (⟨Y, hY⟩ : AlgebraicSpaces B S hS) ⟶ schemeSpace V) n).1 ≅
      pullback p (yoneda.map (adicCompletionQuotientObjHom B S hS V I n)) :=
  (isPullback_fibreInclusion_of_hom (I := I) hY p n).isoPullback

/-- `fibreSpaceIsoPullbackOfHom`, followed by the first projection, is the inclusion of the
infinitesimal fibre. -/
@[reassoc (attr := simp)]
theorem fibreSpaceIsoPullbackOfHom_hom_fst {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (p : Y ⟶ yoneda.obj V) (n : ℕ) :
    (fibreSpaceIsoPullbackOfHom (I := I) hY p n).hom ≫ pullback.fst _ _ =
      (fibreInclusion V I
        (ObjectProperty.homMk p : (⟨Y, hY⟩ : AlgebraicSpaces B S hS) ⟶ schemeSpace V) n).hom :=
  IsPullback.isoPullback_hom_fst _

/-- The transitions of the thickenings, read through `fibreSpaceIsoPullbackOfHom`. -/
theorem fibreTransition_comp_fibreSpaceIsoPullbackOfHom {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (p : Y ⟶ yoneda.obj V) (m : ℕ) :
    (fibreTransition V I
        (ObjectProperty.homMk p : (⟨Y, hY⟩ : AlgebraicSpaces B S hS) ⟶ schemeSpace V)
        (Nat.le_succ (m + 1))).hom ≫ (fibreSpaceIsoPullbackOfHom (I := I) hY p (m + 1 + 1)).hom =
      (fibreSpaceIsoPullbackOfHom (I := I) hY p (m + 1)).hom ≫
        properThickeningTransition I p m := by
  have : Mono (adicCompletionQuotientObjHom B S hS V I (m + 1 + 1)) :=
    (BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance
  have htr := congrArg (fun k => k.hom) (fibreTransition_comp V I
    (ObjectProperty.homMk p : (⟨Y, hY⟩ : AlgebraicSpaces B S hS) ⟶ schemeSpace V)
    (Nat.le_succ (m + 1)))
  simp only [ObjectProperty.FullSubcategory.comp_hom] at htr
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, fibreSpaceIsoPullbackOfHom_hom_fst, Category.assoc,
      properThickeningTransition, pullback.lift_fst, fibreSpaceIsoPullbackOfHom_hom_fst]
    exact htr
  · have r₁ : yoneda.map (adicCompletionQuotientObjTransition B S hS V I
        (Nat.le_add_right (m + 1) 1)) ≫
          yoneda.map (adicCompletionQuotientObjHom B S hS V I (m + 1 + 1)) =
        yoneda.map (adicCompletionQuotientObjHom B S hS V I (m + 1)) := by
      rw [← Functor.map_comp, adicCompletionQuotientObjTransition_comp_hom]
    rw [← cancel_mono (yoneda.map (adicCompletionQuotientObjHom B S hS V I (m + 1 + 1))),
      Category.assoc, Category.assoc, ← pullback.condition,
      fibreSpaceIsoPullbackOfHom_hom_fst_assoc, Category.assoc, Category.assoc,
      properThickeningTransition, pullback.lift_snd_assoc]
    simp only [Category.assoc, r₁]
    rw [← pullback.condition, fibreSpaceIsoPullbackOfHom_hom_fst_assoc, ← Category.assoc, htr]

end Situation

/-- **Algebraization of morphisms (Stacks 0A4Z), given Stacks 08BG.** Let `A = Γ(V, 𝒪_V)` be
Noetherian and complete with respect to an ideal `I`, write `Sₙ = Spec (A / Iⁿ)`, and let `X`,
`Y` be algebraic spaces over `V` with `Xₙ = X ×_V Sₙ` and `Yₙ = Y ×_V Sₙ`. Assume `X ⟶ V` proper
and `Y ⟶ V` separated of finite type. A compatible system of morphisms `gₙ : Xₙ ⟶ Yₙ` over `Sₙ`
(`n ≥ 1`, indexed here by `n + 1`) comes from a unique morphism `g : X ⟶ Y` over `V` whose base
change to every `Sₙ` is `gₙ`. -/
theorem existsUnique_algebraization_fibreMaps_of_closedSubspaceTowerAlgebraizes
    (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
    (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
    [IsAdicComplete I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
    (h08BG : ∀ [_root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)]
      (W : AlgebraicSpaces B S hS) (f : W ⟶ schemeSpace V), ClosedSubspaceTowerAlgebraizes V I f)
    {X Y : AlgebraicSpaces B S hS} (p : X ⟶ schemeSpace V) (q : Y ⟶ schemeSpace V)
    (hp : IsProper B S hS p.hom) (hqsep : IsSeparated B S hS q.hom)
    (hqft : IsFiniteType B S hS q.hom)
    (g : ∀ n : ℕ, fibreSpace V I p (n + 1) ⟶ fibreSpace V I q (n + 1))
    (hg : ∀ n, g n ≫ fibreInclusion V I q (n + 1) ≫ q = fibreInclusion V I p (n + 1) ≫ p)
    (hc : ∀ n, fibreTransition V I p (Nat.le_succ (n + 1)) ≫ g (n + 1) =
      g n ≫ fibreTransition V I q (Nat.le_succ (n + 1))) :
    ∃! g' : X ⟶ Y, g' ≫ q = p ∧
      ∀ n, fibreInclusion V I p (n + 1) ≫ g' = g n ≫ fibreInclusion V I q (n + 1) := by
  have : _root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V) :=
    isLocallyNoetherian_of_isOpenImmersion ((BigFppfOver.toScheme B S hS).obj V).isoSpec.hom
  let g' : ∀ n, fibreSpace V I p n ⟶ Y := fun n => match n with
    | 0 => fibreTransition V I p (Nat.le_succ 0) ≫ g 0 ≫ fibreInclusion V I q (0 + 1)
    | m + 1 => g m ≫ fibreInclusion V I q (m + 1)
  have hg' : ∀ n, g' n ≫ q = fibreInclusion V I p n ≫ p := by
    intro n
    rcases n with _ | m
    · change (fibreTransition V I p (Nat.le_succ 0) ≫ g 0 ≫ fibreInclusion V I q (0 + 1)) ≫ q = _
      rw [Category.assoc, Category.assoc, hg 0, ← Category.assoc, fibreTransition_comp]
    · exact (Category.assoc _ _ _).trans (hg m)
  have hc' : ∀ n, fibreTransition V I p (Nat.le_succ n) ≫ g' (n + 1) = g' n := by
    intro n
    rcases n with _ | m
    · rfl
    · change fibreTransition V I p (Nat.le_succ (m + 1)) ≫ g (m + 1) ≫
          fibreInclusion V I q (m + 1 + 1) = g m ≫ fibreInclusion V I q (m + 1)
      rw [← Category.assoc, hc m, Category.assoc, fibreTransition_comp]
  obtain ⟨⟨h, hq⟩, hh, huniq⟩ := existsUnique_algebraization_of_closedSubspaceTowerAlgebraizes
    h08BG p hp p q hqsep hqft.1 g' hg' hc'
  refine ⟨h, ⟨hq, fun n => hh (n + 1)⟩, fun h' ⟨hq', hh'⟩ => ?_⟩
  refine congrArg Subtype.val (huniq ⟨h', hq'⟩ fun n => ?_)
  rcases n with _ | m
  · change fibreInclusion V I p 0 ≫ h' =
      fibreTransition V I p (Nat.le_succ 0) ≫ g 0 ≫ fibreInclusion V I q (0 + 1)
    rw [← hh' 0, ← Category.assoc, fibreTransition_comp]
  · exact hh' m

/-- **Algebraization from the thickenings of a proper space, given Stacks 08BG at `V`.** A
compatible system of morphisms from the thickenings `Y ×_V Spec (A / Iⁿ⁺¹)` of an algebraic space
`Y` proper over an affine `V` with Noetherian `I`-adically complete ring of functions, into an
algebraic space `X` separated and locally of finite type over `S`, comes from a morphism
`Y ⟶ X`. -/
theorem exists_comp_eq_of_properThickeningTransition (V : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [_root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)]
    (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
    [IsAdicComplete I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
    (h08BG : ∀ (W : AlgebraicSpaces B S hS) (f : W ⟶ schemeSpace V),
      ClosedSubspaceTowerAlgebraizes V I f)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hsep : IsSeparated B S hS (terminal.from X))
    (hlft : IsLocallyOfFiniteType B S hS (terminal.from X))
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (p : Y ⟶ yoneda.obj V) (hp : IsProper B S hS p)
    (g : ∀ n : ℕ, pullback p (yoneda.map (adicCompletionQuotientObjHom B S hS V I (n + 1))) ⟶ X)
    (hg : ∀ n, properThickeningTransition I p n ≫ g (n + 1) = g n) :
    ∃ y : Y ⟶ X, ∀ n, pullback.fst _ _ ≫ y = g n := by
  let Ys : AlgebraicSpaces B S hS := ⟨Y, hY⟩
  let fY : Ys ⟶ schemeSpace V := ObjectProperty.homMk p
  let Qs : AlgebraicSpaces B S hS := ⟨⊤_ _, isAlgebraicSpace_terminal B S hS⟩
  let Ts : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let t : Ts ⟶ Qs := ObjectProperty.homMk (terminal.from X)
  let q : Ys ⟶ Qs := ObjectProperty.homMk (terminal.from Y)
  let g' : ∀ n, fibreSpace V I fY n ⟶ Ts := fun n => match n with
    | 0 => fibreTransition V I fY (Nat.le_succ 0) ≫
        ObjectProperty.homMk ((fibreSpaceIsoPullbackOfHom (I := I) hY p (0 + 1)).hom ≫ g 0)
    | m + 1 => ObjectProperty.homMk ((fibreSpaceIsoPullbackOfHom (I := I) hY p (m + 1)).hom ≫ g m)
  have hg' : ∀ n, g' n ≫ t = fibreInclusion V I fY n ≫ q := fun n =>
    ObjectProperty.hom_ext _ (terminal.hom_ext _ _)
  have hc' : ∀ n, fibreTransition V I fY (Nat.le_succ n) ≫ g' (n + 1) = g' n := by
    intro n
    rcases n with _ | m
    · rfl
    · refine ObjectProperty.hom_ext _ ?_
      change (fibreTransition V I fY (Nat.le_succ (m + 1))).hom ≫
          (fibreSpaceIsoPullbackOfHom (I := I) hY p (m + 1 + 1)).hom ≫ g (m + 1) =
        (fibreSpaceIsoPullbackOfHom (I := I) hY p (m + 1)).hom ≫ g m
      rw [← hg m, ← Category.assoc, ← Category.assoc,
        fibreTransition_comp_fibreSpaceIsoPullbackOfHom]
  obtain ⟨h, -, hh⟩ := exists_comp_eq_of_closedSubspaceTowerAlgebraizes h08BG hp hsep hlft
    hg' hc'
  refine ⟨h.hom, fun n => ?_⟩
  have e₁ := congrArg (fun k => k.hom) (hh (n + 1))
  have e₂ : pullback.fst p (yoneda.map (adicCompletionQuotientObjHom B S hS V I (n + 1))) =
      (fibreSpaceIsoPullbackOfHom (I := I) hY p (n + 1)).inv ≫
        (fibreInclusion V I fY (n + 1)).hom := by
    rw [Iso.eq_inv_comp, fibreSpaceIsoPullbackOfHom_hom_fst]
  change (fibreInclusion V I fY (n + 1)).hom ≫ h.hom =
    (fibreSpaceIsoPullbackOfHom (I := I) hY p (n + 1)).hom ≫ g n at e₁
  rw [e₂, Category.assoc, e₁, Iso.inv_hom_id_assoc]

/-- **The tower form of Stacks 0A4Z, given Stacks 08BG.** An algebraic
space `X` separated and locally of finite type over `S` has the algebraization property
`AlgebraicGeometry.Space.HasProperTowerAlgebraization`. -/
theorem hasProperTowerAlgebraization_of_closedSubspaceTowerAlgebraizes
    (h08BG : ∀ (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
      [_root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)]
      (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) (W : AlgebraicSpaces B S hS)
      (f : W ⟶ schemeSpace V), ClosedSubspaceTowerAlgebraizes V I f)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hsep : IsSeparated B S hS (terminal.from X))
    (hlft : IsLocallyOfFiniteType B S hS (terminal.from X)) :
    HasProperTowerAlgebraization X := by
  intro V _ I hN hcomp Y hY p hp g hg
  have := hN
  have : _root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V) :=
    isLocallyNoetherian_of_isOpenImmersion ((BigFppfOver.toScheme B S hS).obj V).isoSpec.hom
  have := hcomp
  exact exists_comp_eq_of_properThickeningTransition V I (h08BG V I) hX hsep hlft hY p hp g hg

end AlgebraicGeometry.Space
