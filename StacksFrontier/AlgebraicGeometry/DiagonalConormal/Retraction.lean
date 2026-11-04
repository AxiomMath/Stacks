module

public import StacksFrontier.AlgebraicGeometry.ConormalAffineCotangent.Sections
public import StacksFrontier.AlgebraicGeometry.DiagonalConormal.AffineDiagonal

/-!
# The two retractions of the diagonal on sections

Let `f : X ⟶ S` be a morphism of schemes. Both projections `p₁, p₂ : X ×_S X ⟶ X` retract the
diagonal `pullback.diagonal f`, so the structure map of its canonical closed factorization sends
each of `p₁^♯ b` and `p₂^♯ b` back to `b`. Hence, for every open `V` of the coborder neighbourhood
of the diagonal and every section `b`, the difference `p₂^♯ b - p₁^♯ b` is the image of a unique
section of the ideal sheaf of the canonical closed factorization: the section `x` of the generator
clause of [Stacks, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2).

## Main results

* `Stacks.DiagonalConormal.appLE_retraction`: if `g ≫ r = 𝟙 X`, then the composite of the `appLE`
  maps of `r` and `g` is a restriction map of `𝒪_X`.
* `Stacks.DiagonalConormal.appLE_opensι_comp`: for an open `O` of `P`, `(O.ι ≫ p).appLE U V` and
  `p.appLE U (O.ι ''ᵁ V)` agree on sections.
* `Stacks.DiagonalConormal.liftCoborder_appLE_fst` and
  `Stacks.DiagonalConormal.liftCoborder_appLE_snd`: the structure map of the canonical closed
  factorization of the diagonal sends `p₁^♯ b` and `p₂^♯ b` to `b`.
* `Stacks.DiagonalConormal.liftCoborder_app_snd_sub_fst_eq_zero`: it sends `p₂^♯ b - p₁^♯ b` to
  zero.
* `Stacks.DiagonalConormal.exists_idealSheaf_section_snd_sub_fst` and
  `Stacks.DiagonalConormal.existsUnique_idealSheaf_section_snd_sub_fst`: `p₂^♯ b - p₁^♯ b` is the
  image of a unique section of the ideal sheaf of the canonical closed factorization.
* `Stacks.DiagonalConormal.exists_preimage_eq`: every open of the source of a closed immersion is
  the preimage of an open of the target.
* `Stacks.DiagonalConormal.exists_coborder_open`: every open `U` of `X` is the preimage of an open
  `V` of the coborder neighbourhood of the diagonal whose image lies in `p₁ ⁻¹ᵁ U` and in
  `p₂ ⁻¹ᵁ U`.

## References

* [Stacks Project, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.DiagonalConormal

/-! ### Transporting `appLE` along an equality of morphisms -/

/-- Equal morphisms have equal `AlgebraicGeometry.Scheme.Hom.appLE` maps. -/
theorem appLE_congr {X Y : Scheme.{u}} {f f' : X ⟶ Y} (hf : f = f') (U : Y.Opens) (V : X.Opens)
    (h : V ≤ f ⁻¹ᵁ U) (h' : V ≤ f' ⁻¹ᵁ U) :
    Scheme.Hom.appLE f U V h = f'.appLE U V h' := by
  subst hf; rfl

/-- The `appLE` maps of an identity morphism are the restriction maps of the structure
sheaf. -/
theorem id_appLE {X : Scheme.{u}} (U V : X.Opens) (h : V ≤ (𝟙 X) ⁻¹ᵁ U) (hVU : V ≤ U) :
    Scheme.Hom.appLE (𝟙 X) U V h = X.presheaf.map (homOfLE hVU).op :=
  (Category.id_comp _).trans rfl

/-- A restriction map of the structure sheaf from an open to itself is the identity. -/
theorem presheaf_map_self {X : Scheme.{u}} (U : X.Opens) (h : U ≤ U) (b : Γ(X, U)) :
    (X.presheaf.map (homOfLE h).op).hom b = b :=
  congr($(X.presheaf.map_id (.op U)) b)

/-! ### Retractions on sections -/

/-- If `g ≫ r = 𝟙 X`, then applying `r` on sections and then `g` on sections is the restriction map
of `𝒪_X` from `U` to `W`. -/
theorem appLE_retraction {X Y : Scheme.{u}} {g : X ⟶ Y} {r : Y ⟶ X} (hgr : g ≫ r = 𝟙 X)
    (U : X.Opens) (V : Y.Opens) (W : X.Opens) (h : V ≤ r ⁻¹ᵁ U) (h' : W ≤ g ⁻¹ᵁ V)
    (hWU : W ≤ U) (b : Γ(X, U)) :
    (g.appLE V W h').hom ((r.appLE U V h).hom b) =
      (X.presheaf.map (homOfLE hWU).op).hom b := by
  have hcomp : (g.appLE V W h').hom ((r.appLE U V h).hom b) =
      ((r.appLE U V h ≫ g.appLE V W h').hom) b := rfl
  refine hcomp.trans ?_
  refine (congr($(Scheme.Hom.appLE_comp_appLE g r U V W h h') b)).trans ?_
  exact congr($((appLE_congr hgr U W _ (by simpa using hWU)).trans (id_appLE U W _ hWU)) b)

/-- An open of an open subscheme is contained in the preimage of `U` under `O.ι ≫ p` as soon
as its image is contained in the preimage of `U` under `p`. -/
theorem le_preimage_opensι_comp {X P : Scheme.{u}} (O : P.Opens) (p : P ⟶ X) {U : X.Opens}
    {V : O.toScheme.Opens} (h₁ : O.ι ''ᵁ V ≤ p ⁻¹ᵁ U) :
    V ≤ (O.ι ≫ p) ⁻¹ᵁ U :=
  (Scheme.Hom.preimage_image_eq O.ι V).ge.trans (O.ι.preimage_mono h₁)

/-- For an open `O` of `P`, the section of `𝒪_{↑O}` over `V` obtained from `b` through `O.ι ≫ p` is
the section of `𝒪_P` over `O.ι ''ᵁ V` obtained from `b` through `p`. -/
theorem appLE_opensι_comp {X P : Scheme.{u}} (O : P.Opens) (p : P ⟶ X) {U : X.Opens}
    {V : O.toScheme.Opens} (h₁ : O.ι ''ᵁ V ≤ p ⁻¹ᵁ U) (b : Γ(X, U)) :
    ((O.ι ≫ p).appLE U V (le_preimage_opensι_comp O p h₁)).hom b =
      (p.appLE U (O.ι ''ᵁ V) h₁).hom b := by
  have e₂ : V ≤ O.ι ⁻¹ᵁ (O.ι ''ᵁ V) := (Scheme.Hom.preimage_image_eq O.ι V).ge
  have hc := Scheme.Hom.appLE_comp_appLE O.ι p U (O.ι ''ᵁ V) V h₁ e₂
  have hι : Scheme.Hom.appLE O.ι (O.ι ''ᵁ V) V e₂ =
      P.presheaf.map (homOfLE (le_refl (O.ι ''ᵁ V))).op :=
    Scheme.Opens.ι_appLE O (O.ι ''ᵁ V) V e₂
  have hstep : ((p.appLE U (O.ι ''ᵁ V) h₁ ≫ Scheme.Hom.appLE O.ι (O.ι ''ᵁ V) V e₂).hom) b =
      (p.appLE U (O.ι ''ᵁ V) h₁).hom b := by
    refine Eq.trans ?_ (presheaf_map_self (O.ι ''ᵁ V) (le_refl _)
      ((p.appLE U (O.ι ''ᵁ V) h₁).hom b))
    exact congr($(hι) ((p.appLE U (O.ι ''ᵁ V) h₁).hom b))
  refine Eq.trans ?_ hstep
  exact congr($(appLE_congr rfl U V _ (le_preimage_opensι_comp O p h₁)) b).symm ▸
    (congr($(hc.symm) b))

/-! ### The two retractions of the diagonal -/

section Diagonal

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The first projection, read on the coborder neighbourhood of the diagonal, retracts the
canonical closed factorization of the diagonal. -/
theorem liftCoborder_comp_fst :
    (pullback.diagonal f).liftCoborder ≫
        ((pullback.diagonal f).coborderRange.ι ≫ pullback.fst f f) = 𝟙 X :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ pullback.fst f f) (pullback.diagonal f).liftCoborder_ι).trans
      (pullback.diagonal_fst f))

/-- The second projection, read on the coborder neighbourhood of the diagonal, retracts the
canonical closed factorization of the diagonal. -/
theorem liftCoborder_comp_snd :
    (pullback.diagonal f).liftCoborder ≫
        ((pullback.diagonal f).coborderRange.ι ≫ pullback.snd f f) = 𝟙 X :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ pullback.snd f f) (pullback.diagonal f).liftCoborder_ι).trans
      (pullback.diagonal_snd f))

variable (V : (pullback.diagonal f).coborderRange.toScheme.Opens)

/-- The structure map of the canonical closed factorization of the diagonal sends `p^♯ b` back to
`b`, for any retraction `p` of the diagonal on the coborder neighbourhood. -/
private theorem liftCoborder_app_appLE_of_comp_eq_id (p : pullback f f ⟶ X)
    (hp : (pullback.diagonal f).liftCoborder ≫ ((pullback.diagonal f).coborderRange.ι ≫ p) = 𝟙 X)
    (h : (pullback.diagonal f).coborderRange.ι ''ᵁ V ≤
      p ⁻¹ᵁ ((pullback.diagonal f).liftCoborder ⁻¹ᵁ V))
    (b : Γ(X, (pullback.diagonal f).liftCoborder ⁻¹ᵁ V)) :
    ((pullback.diagonal f).liftCoborder.app V).hom ((p.appLE _ _ h).hom b) = b := by
  rw [Scheme.Hom.app_eq_appLE _,
    ← appLE_opensι_comp (pullback.diagonal f).coborderRange p h b]
  exact (appLE_retraction hp _ V _ (le_preimage_opensι_comp _ _ h) (le_refl _) (le_refl _) b).trans
    (presheaf_map_self _ (le_refl _) b)

/-- The structure map of the canonical closed factorization of the diagonal sends `p₁^♯ b` back
to `b`. -/
theorem liftCoborder_appLE_fst
    (h₁ : (pullback.diagonal f).coborderRange.ι ''ᵁ V ≤
      (pullback.fst f f) ⁻¹ᵁ ((pullback.diagonal f).liftCoborder ⁻¹ᵁ V))
    (b : Γ(X, (pullback.diagonal f).liftCoborder ⁻¹ᵁ V)) :
    ((pullback.diagonal f).liftCoborder.app V).hom
        (((pullback.fst f f).appLE _ _ h₁).hom b) = b :=
  liftCoborder_app_appLE_of_comp_eq_id f V _ (liftCoborder_comp_fst f) h₁ b

/-- The structure map of the canonical closed factorization of the diagonal sends `p₂^♯ b` back
to `b`. -/
theorem liftCoborder_appLE_snd
    (h₂ : (pullback.diagonal f).coborderRange.ι ''ᵁ V ≤
      (pullback.snd f f) ⁻¹ᵁ ((pullback.diagonal f).liftCoborder ⁻¹ᵁ V))
    (b : Γ(X, (pullback.diagonal f).liftCoborder ⁻¹ᵁ V)) :
    ((pullback.diagonal f).liftCoborder.app V).hom
        (((pullback.snd f f).appLE _ _ h₂).hom b) = b :=
  liftCoborder_app_appLE_of_comp_eq_id f V _ (liftCoborder_comp_snd f) h₂ b

/-- The structure map of the canonical closed factorization of the diagonal sends `p₂^♯ b - p₁^♯ b`
to zero. -/
theorem liftCoborder_app_snd_sub_fst_eq_zero
    (h₁ : (pullback.diagonal f).coborderRange.ι ''ᵁ V ≤
      (pullback.fst f f) ⁻¹ᵁ ((pullback.diagonal f).liftCoborder ⁻¹ᵁ V))
    (h₂ : (pullback.diagonal f).coborderRange.ι ''ᵁ V ≤
      (pullback.snd f f) ⁻¹ᵁ ((pullback.diagonal f).liftCoborder ⁻¹ᵁ V))
    (b : Γ(X, (pullback.diagonal f).liftCoborder ⁻¹ᵁ V)) :
    ((pullback.diagonal f).liftCoborder.app V).hom
        (((pullback.snd f f).appLE _ _ h₂).hom b - ((pullback.fst f f).appLE _ _ h₁).hom b) =
      0 := by
  have hsub := map_sub ((pullback.diagonal f).liftCoborder.app V).hom
    (((pullback.snd f f).appLE _ _ h₂).hom b) (((pullback.fst f f).appLE _ _ h₁).hom b)
  exact hsub.trans
    ((congr($(liftCoborder_appLE_snd f V h₂ b) - $(liftCoborder_appLE_fst f V h₁ b))).trans
      (sub_self b))

/-- For every open `V` of the coborder neighbourhood of the diagonal satisfying both inclusions and
every section `b`, there is a section `x` of the ideal sheaf of the canonical closed factorization
of the diagonal whose image in the structure sheaf is `p₂^♯ b - p₁^♯ b`. -/
theorem exists_idealSheaf_section_snd_sub_fst
    (h₁ : (pullback.diagonal f).coborderRange.ι ''ᵁ V ≤
      (pullback.fst f f) ⁻¹ᵁ ((pullback.diagonal f).liftCoborder ⁻¹ᵁ V))
    (h₂ : (pullback.diagonal f).coborderRange.ι ''ᵁ V ≤
      (pullback.snd f f) ⁻¹ᵁ ((pullback.diagonal f).liftCoborder ⁻¹ᵁ V))
    (b : Γ(X, (pullback.diagonal f).liftCoborder ⁻¹ᵁ V)) :
    ∃ x : (Stacks.ClosedImmersion.idealSheaf
        (pullback.diagonal f).liftCoborder.toLRSHom.toShHom).val.obj (.op V),
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom
          (pullback.diagonal f).liftCoborder.toLRSHom.toShHom))).val.app (.op V) x =
        ((pullback.snd f f).appLE _ _ h₂).hom b - ((pullback.fst f f).appLE _ _ h₁).hom b :=
  (Stacks.Conormal.AffineCotangent.Sections.exists_idealSheaf_section_iff
      (pullback.diagonal f).liftCoborder V _).2
    (liftCoborder_app_snd_sub_fst_eq_zero f V h₁ h₂ b)

/-- For every open `V` of the coborder neighbourhood of the diagonal satisfying both inclusions and
every section `b`, there is a unique section `x` of the ideal sheaf of the canonical closed
factorization of the diagonal whose image in the structure sheaf is `p₂^♯ b - p₁^♯ b`. -/
theorem existsUnique_idealSheaf_section_snd_sub_fst
    (h₁ : (pullback.diagonal f).coborderRange.ι ''ᵁ V ≤
      (pullback.fst f f) ⁻¹ᵁ ((pullback.diagonal f).liftCoborder ⁻¹ᵁ V))
    (h₂ : (pullback.diagonal f).coborderRange.ι ''ᵁ V ≤
      (pullback.snd f f) ⁻¹ᵁ ((pullback.diagonal f).liftCoborder ⁻¹ᵁ V))
    (b : Γ(X, (pullback.diagonal f).liftCoborder ⁻¹ᵁ V)) :
    ∃! x : (Stacks.ClosedImmersion.idealSheaf
        (pullback.diagonal f).liftCoborder.toLRSHom.toShHom).val.obj (.op V),
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom
          (pullback.diagonal f).liftCoborder.toLRSHom.toShHom))).val.app (.op V) x =
        ((pullback.snd f f).appLE _ _ h₂).hom b - ((pullback.fst f f).appLE _ _ h₁).hom b := by
  obtain ⟨x, hx⟩ := exists_idealSheaf_section_snd_sub_fst f V h₁ h₂ b
  exact ⟨x, hx, fun y hy => Stacks.Conormal.Locality.idealSheaf_section_injective
    (pullback.diagonal f).liftCoborder V (hy.trans hx.symm)⟩

/-! ### Every open of the source is admissible -/

/-- An open of an open subscheme has image inside any open containing its preimage. -/
theorem image_le_of_le_preimage {P : Scheme.{u}} {O : P.Opens} {A : O.toScheme.Opens}
    {B : P.Opens} (h : A ≤ O.ι ⁻¹ᵁ B) : O.ι ''ᵁ A ≤ B := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact h hy

/-- Every open of the source of a closed immersion is the preimage of an open of the target. -/
theorem exists_preimage_eq {X Y : Scheme.{u}} (g : X ⟶ Y) [IsClosedImmersion g] (U : X.Opens) :
    ∃ V : Y.Opens, g ⁻¹ᵁ V = U := by
  obtain ⟨t, ht, hts⟩ := (g.isClosedEmbedding.isInducing.isOpen_iff (s := U.1)).1 U.2
  exact ⟨⟨t, ht⟩, TopologicalSpace.Opens.ext hts⟩

/-- Every open `U` of `X` is the preimage, under the canonical closed factorization of the
diagonal, of an open `V` of the coborder neighbourhood of the diagonal whose image lies in
`p₁ ⁻¹ᵁ U` and in `p₂ ⁻¹ᵁ U`. -/
theorem exists_coborder_open (U : X.Opens) :
    ∃ V : (pullback.diagonal f).coborderRange.toScheme.Opens,
      (pullback.diagonal f).liftCoborder ⁻¹ᵁ V = U ∧
      (pullback.diagonal f).coborderRange.ι ''ᵁ V ≤ (pullback.fst f f) ⁻¹ᵁ U ∧
      (pullback.diagonal f).coborderRange.ι ''ᵁ V ≤ (pullback.snd f f) ⁻¹ᵁ U := by
  obtain ⟨V₀, hV₀⟩ := exists_preimage_eq (pullback.diagonal f).liftCoborder U
  have h1 : (pullback.diagonal f).liftCoborder ⁻¹ᵁ
      ((pullback.diagonal f).coborderRange.ι ⁻¹ᵁ ((pullback.fst f f) ⁻¹ᵁ U)) = U :=
    congrArg (fun m => m ⁻¹ᵁ U) (liftCoborder_comp_fst f)
  have h2 : (pullback.diagonal f).liftCoborder ⁻¹ᵁ
      ((pullback.diagonal f).coborderRange.ι ⁻¹ᵁ ((pullback.snd f f) ⁻¹ᵁ U)) = U :=
    congrArg (fun m => m ⁻¹ᵁ U) (liftCoborder_comp_snd f)
  refine ⟨V₀ ⊓ ((pullback.diagonal f).coborderRange.ι ⁻¹ᵁ ((pullback.fst f f) ⁻¹ᵁ U)) ⊓
      ((pullback.diagonal f).coborderRange.ι ⁻¹ᵁ ((pullback.snd f f) ⁻¹ᵁ U)), ?_, ?_, ?_⟩
  · refine le_antisymm
      (((pullback.diagonal f).liftCoborder.preimage_mono
        (le_trans inf_le_left inf_le_left)).trans hV₀.le) ?_
    intro x hx
    exact ⟨⟨hV₀.ge hx, h1.ge hx⟩, h2.ge hx⟩
  · exact image_le_of_le_preimage (le_trans inf_le_left inf_le_right)
  · exact image_le_of_le_preimage inf_le_right

end Diagonal

end Stacks.DiagonalConormal

end
