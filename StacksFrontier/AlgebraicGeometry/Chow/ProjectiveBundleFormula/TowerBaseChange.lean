module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Tower
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ClosedImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionCorrespondence
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.BaseChangeDivisor
public import StacksFrontier.AlgebraicGeometry.Blowup.ClassifyingMorphism
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.BaseChange
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.UFDExtensionInvertibleGlobal
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalRankTwo

/-!
# Base change of projective towers

A projective tower `Stacks.Chow.IsProjectiveTower n π L` is stable under base change: in a
cartesian square `P' = U' ×_U P`, the projection `π' : P' ⟶ U'` with the pullback of `L` is again
a projective tower of fibre dimension `n`. Each piece of the recursive structure base changes:
the pulled-back section has as zero scheme the inverse image of the zero scheme
([Stacks, Tag 0B6Y]), which is a relative effective Cartier divisor over `U'`
([Stacks, Tag 056Q]); flatness, properness and local finite type are stable under base change,
and so is relative dimension ([Stacks, Tag 02NK]); the complement of the zero scheme is the
inverse image of the complement, and affine-space bundles are stable under base change. The
same then holds locally on the base, for `Stacks.Chow.IsLocallyProjectiveTower`.

Isomorphisms, open subschemes and closed subschemes of the base are the special cases the
intersection theory uses.

## Main results

* `Stacks.Chow.IsAffineSpaceBundle.of_isPullback` — affine-space bundles base change.
* `Stacks.Chow.IsProjectiveTower.of_isPullback` — projective towers base change along any
  cartesian square, with any module isomorphic to the pullback.
* `Stacks.Chow.IsProjectiveTower.of_iso_left`, `Stacks.Chow.IsProjectiveTower.of_iso_right`,
  `Stacks.Chow.IsProjectiveTower.of_iso_module` — invariance under isomorphisms.
* `Stacks.Chow.IsProjectiveTower.pullback`, `Stacks.Chow.IsProjectiveTower.restrict`,
  `Stacks.Chow.IsProjectiveTower.comapRestrict` — base change along an arbitrary morphism, to an
  open subscheme and to a closed subscheme of the base.
* `Stacks.Chow.IsLocallyProjectiveTower.of_isPullback` and its special cases
  `Stacks.Chow.IsLocallyProjectiveTower.pullback`,
  `Stacks.Chow.IsLocallyProjectiveTower.restrict`,
  `Stacks.Chow.IsLocallyProjectiveTower.comapRestrict` — the same for locally projective towers.

## Implementation notes

The base change is stated for an arbitrary cartesian square, presented by `IsPullback`, and an
arbitrary module isomorphic to the pullback of `L`, so that isomorphism invariance, restriction
to opens and restriction to closed subschemes are all instances of one statement, proved by
induction on the tower.

## References

* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 056Q](https://stacks.math.columbia.edu/tag/056Q)
* [Stacks Project, Tag 02NK](https://stacks.math.columbia.edu/tag/02NK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Restricting a cartesian square over an open of the base -/

/-- In a commutative square, the two iterated preimages of an open of the bottom right corner
agree. -/
theorem preimage_preimage_eq_of_isPullback {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (hsq : IsPullback g' f' f g) (V : Y.Opens) :
    g' ⁻¹ᵁ (f ⁻¹ᵁ V) = f' ⁻¹ᵁ (g ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hsq.w]

/-- A cartesian square restricts to a cartesian square over an open `V` of the base: the
restriction of `f'` to the preimage of `V` is the base change of the restriction of `f` to `V`.
-/
theorem isPullback_morphismRestrict_of_isPullback {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (hsq : IsPullback g' f' f g) (V : Y.Opens) :
    IsPullback (g'.resLE (f ⁻¹ᵁ V) (f' ⁻¹ᵁ (g ⁻¹ᵁ V))
        (preimage_preimage_eq_of_isPullback hsq V).ge)
      (f' ∣_ (g ⁻¹ᵁ V)) (f ∣_ V) (g.resLE V (g ⁻¹ᵁ V) le_rfl) := by
  have hpre : f' ⁻¹ᵁ (g ⁻¹ᵁ V) = g' ⁻¹ᵁ (f ⁻¹ᵁ V) ⊓ f' ⁻¹ᵁ (g ⁻¹ᵁ V) := by
    rw [preimage_preimage_eq_of_isPullback hsq V, inf_idem]
  have h := Scheme.Hom.isPullback_resLE hsq (US := V) (UT := g ⁻¹ᵁ V) (UX := f ⁻¹ᵁ V)
    le_rfl le_rfl hpre
  rwa [Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.resLE_eq_morphismRestrict] at h

/-! ### Affine-space bundles -/

/-- **Affine-space bundles are stable under base change.** In a cartesian square, the base
change of an affine-space bundle of rank `r` is an affine-space bundle of rank `r`: over the
preimage of a trivializing open `V`, both the base change and affine `r`-space over the preimage
are base changes of `𝔸^r_V ⟶ V`. -/
theorem IsAffineSpaceBundle.of_isPullback {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (hsq : IsPullback g' f' f g) {r : ℕ}
    (h : IsAffineSpaceBundle f r) : IsAffineSpaceBundle f' r := by
  intro y'
  obtain ⟨V, hyV, e, he⟩ := h (g y')
  refine ⟨g ⁻¹ᵁ V, hyV, ?_⟩
  have h₁ := isPullback_morphismRestrict_of_isPullback hsq V
  have h₂ : IsPullback e.hom (f ∣_ V) (𝔸(ULift.{u} (Fin r); V.toScheme) ↘ V.toScheme) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [he, Category.comp_id]⟩
  have h₁₂ := h₁.paste_horiz h₂
  rw [Category.comp_id] at h₁₂
  have h₃ := AffineSpace.isPullback_map (n := ULift.{u} (Fin r))
    (g.resLE V (g ⁻¹ᵁ V) le_rfl)
  exact ⟨h₁₂.isoIsPullback _ _ h₃, h₁₂.isoIsPullback_hom_snd _ _ h₃⟩

/-! ### Modules -/

/-- Pulling a module back along the two sides of a commutative square gives isomorphic
modules. -/
def pullbackObjIsoOfComm {A B C D : Scheme.{u}} {a : A ⟶ B} {b : B ⟶ D} {c : A ⟶ C}
    {d : C ⟶ D} (h : a ≫ b = c ≫ d) (M : D.Modules) :
    (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback b).obj M) ≅
      (Scheme.Modules.pullback c).obj ((Scheme.Modules.pullback d).obj M) :=
  (Scheme.Modules.pullbackComp a b).app M ≪≫ (Scheme.Modules.pullbackCongr h).app M ≪≫
    ((Scheme.Modules.pullbackComp c d).app M).symm

/-- Pull an isomorphism `N ≅ b^* M` back along `a`, swapping pullbacks across a square. -/
private def pullbackIsoOfComm {A B C D : Scheme.{u}} {a : A ⟶ B} {b : B ⟶ D} {c : A ⟶ C}
    {d : C ⟶ D} (h : a ≫ b = c ≫ d) {M : D.Modules} {N : B.Modules}
    (e : N ≅ (Scheme.Modules.pullback b).obj M) :
    (Scheme.Modules.pullback a).obj N ≅ (Scheme.Modules.pullback c).obj
      ((Scheme.Modules.pullback d).obj M) :=
  (Scheme.Modules.pullback a).mapIso e ≪≫ pullbackObjIsoOfComm h M

/-- A module isomorphic to `L` is isomorphic to its pullback along the identity. -/
private def pullbackIdIsoOfIso {P : Scheme.{u}} {L L' : P.Modules} (e : L' ≅ L) :
    L' ≅ (Scheme.Modules.pullback (𝟙 P)).obj L :=
  e ≪≫ ((Scheme.Modules.pullbackId (X := P)).app L).symm

/-! ### Projective towers -/

/-- The successor constructor of `Stacks.Chow.IsProjectiveTower`, with the zero scheme of the
section and its complement given by any closed subscheme and open subscheme equal to them. -/
theorem IsProjectiveTower.succ_of_eq {P U : Scheme.{u}} (n : ℕ) (π : P ⟶ U) (L : P.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L]
    [LocallyOfFiniteType π] [Flat π] [IsProper π]
    (hπ : AlgebraicGeometry.RelativeDimension π (n + 1)) (s : Γ(L, ⊤))
    (D : P.IdealSheafData) (hDs : Stacks.Divisors.zeroScheme P L s = D)
    (hD : Stacks.Divisors.IsRelativeEffectiveCartierDivisor π D)
    [LocallyOfFiniteType (D.subschemeι ≫ π)]
    (hq : AlgebraicGeometry.RelativeDimension (D.subschemeι ≫ π) n)
    (htower : IsProjectiveTower n (D.subschemeι ≫ π)
      ((Scheme.Modules.pullback D.subschemeι).obj L))
    (W : P.Opens) (hW : (W : Set P) = ((D.support : Set P))ᶜ)
    (haff : IsAffineSpaceBundle (W.ι ≫ π) (n + 1)) :
    IsProjectiveTower (n + 1) π L := by
  subst hDs
  obtain rfl : W = zeroSchemeComplement P L s := Opens.ext hW
  exact .succ n π L hπ s hD hq htower haff

/-- **Projective towers are stable under base change.** In a cartesian square
`P' = U' ×_U P`, a projective tower `π : P ⟶ U` of fibre dimension `n` with module `L` base
changes to a projective tower `π' : P' ⟶ U'` of fibre dimension `n`, with any module isomorphic
to the pullback of `L`. -/
theorem IsProjectiveTower.of_isPullback {n : ℕ} {P U : Scheme.{u}} {π : P ⟶ U} {L : P.Modules}
    (h : IsProjectiveTower n π L) {P' U' : Scheme.{u}} {π' : P' ⟶ U'} {g' : P' ⟶ P}
    {g : U' ⟶ U} (hsq : IsPullback g' π' π g) {L' : P'.Modules}
    (e : L' ≅ (Scheme.Modules.pullback g').obj L) : IsProjectiveTower n π' L' := by
  induction h generalizing P' U' with
  | zero π L hπ hL =>
    have := hπ
    obtain ⟨i⟩ := hL
    exact .zero π' L' (hsq.isIso_snd_of_isIso)
      ⟨e ≪≫ (Scheme.Modules.pullback g').mapIso i ≪≫ Scheme.Modules.pullbackUnitIso g'⟩
  | @succ P U n π L hL _ _ _ hπ s hD _ hq htower haff ih =>
    have hLp : AlgebraicGeometry.SheafOfModules.IsInvertible P'.sheaf.obj
        P'.ringCatSheaf.property ((Scheme.Modules.pullback g').obj L) :=
      Stacks.RelativeProj.isInvertible_pullback_obj g' L hL
    have hL' : AlgebraicGeometry.SheafOfModules.IsInvertible P'.sheaf.obj
        P'.ringCatSheaf.property L' :=
      Stacks.UFDExtensionGlobal.isInvertible_of_iso e.symm hLp
    have : LocallyOfFiniteType π' := MorphismProperty.of_isPullback hsq inferInstance
    have : Flat π' := MorphismProperty.of_isPullback hsq inferInstance
    have : IsProper π' := MorphismProperty.of_isPullback hsq inferInstance
    set D := Stacks.Divisors.zeroScheme P L s with hDdef
    let s' : Γ(L', ⊤) := Scheme.Modules.Hom.app e.inv ⊤ (pullbackGlobalSections g' L s)
    have hDs' : Stacks.Divisors.zeroScheme P' L' s' = D.comap g' :=
      (AlgebraicGeometry.zeroScheme_eq_of_iso e.symm rfl).symm.trans
        (Stacks.Divisors.zeroScheme_pullback g' L s)
    have hDsq : IsPullback (comapRestrict D g') ((D.comap g').subschemeι ≫ π')
        (D.subschemeι ≫ π) g :=
      (isPullback_comapRestrict D g').flip.paste_vert hsq
    have hcart : Stacks.Divisors.IsEffectiveCartierDivisor (D.comap g') := by
      have := hD.2
      rw [← hsq.flip.isoPullback_hom_snd, Scheme.IdealSheafData.comap_comp]
      exact Stacks.Divisors.isPullbackDefined_of_flat _ _
        (isEffectiveCartierDivisor_comap_pullback π g D hD.1)
    have hD' : Stacks.Divisors.IsRelativeEffectiveCartierDivisor π' (D.comap g') :=
      ⟨hcart, MorphismProperty.of_isPullback hDsq hD.2⟩
    have hq' := RelativeDimension.of_isPullback hDsq hq
    have htower' := ih hDsq (pullbackIsoOfComm (comapRestrict_subschemeι D g').symm e)
    have haff' := IsAffineSpaceBundle.of_isPullback
      ((isPullback_morphismRestrict g' (zeroSchemeComplement P L s)).paste_vert hsq) haff
    refine IsProjectiveTower.succ_of_eq n π' L' (RelativeDimension.of_isPullback hsq hπ) s'
      (D.comap g') hDs' hD' hq' htower' _ ?_ haff'
    simp [zeroSchemeComplement, D]

/-- A projective tower stays a projective tower when its module is replaced by an isomorphic
one. -/
theorem IsProjectiveTower.of_iso_module {n : ℕ} {P U : Scheme.{u}} {π : P ⟶ U} {L L' : P.Modules}
    (h : IsProjectiveTower n π L) (e : L' ≅ L) : IsProjectiveTower n π L' :=
  h.of_isPullback (IsPullback.of_horiz_isIso (fst := 𝟙 P) (g := 𝟙 U) ⟨by simp⟩)
    (pullbackIdIsoOfIso e)

/-- **Projective towers are invariant under isomorphism of the total space.** If `e : P ≅ P'`
lies over `U` and `L` is isomorphic to the pullback of `L'` along `e`, a projective tower
structure on `(π', L')` gives one on `(π, L)`. -/
theorem IsProjectiveTower.of_iso_left {n : ℕ} {P P' U : Scheme.{u}} {π : P ⟶ U} {π' : P' ⟶ U}
    {L : P.Modules} {L' : P'.Modules} (e : P ≅ P') (he : e.hom ≫ π' = π)
    (eL : L ≅ (Scheme.Modules.pullback e.hom).obj L') (h : IsProjectiveTower n π' L') :
    IsProjectiveTower n π L :=
  h.of_isPullback (IsPullback.of_horiz_isIso (g := 𝟙 U) ⟨by simp [he]⟩) eL

/-- **Projective towers are invariant under isomorphism of the base.** Composing a projective
tower with an isomorphism `e : U ≅ U'` of the base gives a projective tower with the same
module. -/
theorem IsProjectiveTower.of_iso_right {n : ℕ} {P U U' : Scheme.{u}} {π : P ⟶ U}
    {L : P.Modules} (e : U ≅ U') (h : IsProjectiveTower n π L) :
    IsProjectiveTower n (π ≫ e.hom) L :=
  h.of_isPullback (IsPullback.of_horiz_isIso (fst := 𝟙 P) (g := e.inv) ⟨by simp⟩)
    (pullbackIdIsoOfIso (Iso.refl L))

/-- **Base change of a projective tower along an arbitrary morphism**, in Mathlib's chosen
fibre product: for `g : U' ⟶ U`, the projection `P ×_U U' ⟶ U'` with the pullback of `L` is a
projective tower of the same fibre dimension. -/
theorem IsProjectiveTower.pullback {n : ℕ} {P U : Scheme.{u}} {π : P ⟶ U} {L : P.Modules}
    (h : IsProjectiveTower n π L) {U' : Scheme.{u}} (g : U' ⟶ U) :
    IsProjectiveTower n (pullback.snd π g)
      ((Scheme.Modules.pullback (pullback.fst π g)).obj L) :=
  h.of_isPullback (IsPullback.of_hasPullback π g) (Iso.refl _)

/-- **Restriction of a projective tower to an open of the base**: over an open `V ⊆ U`, the
restriction `π⁻¹(V) ⟶ V` with the restriction of `L` is a projective tower. -/
theorem IsProjectiveTower.restrict {n : ℕ} {P U : Scheme.{u}} {π : P ⟶ U} {L : P.Modules}
    (h : IsProjectiveTower n π L) (V : U.Opens) :
    IsProjectiveTower n (π ∣_ V) ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L) :=
  h.of_isPullback (isPullback_morphismRestrict π V).flip (Iso.refl _)

/-- **Restriction of a projective tower to a closed subscheme of the base**: over a closed
subscheme `W` of `U`, the restriction `π⁻¹(W) ⟶ W` with the pullback of `L` to the inverse
image of `W` is a projective tower. -/
theorem IsProjectiveTower.comapRestrict {n : ℕ} {P U : Scheme.{u}} {π : P ⟶ U} {L : P.Modules}
    (h : IsProjectiveTower n π L) (W : U.IdealSheafData) :
    IsProjectiveTower n (Stacks.Chow.comapRestrict W π)
      ((Scheme.Modules.pullback (W.comap π).subschemeι).obj L) :=
  h.of_isPullback (isPullback_comapRestrict W π) (Iso.refl _)

/-! ### Locally projective towers -/

/-- A projective tower is a projective tower locally on the base. -/
theorem IsProjectiveTower.isLocallyProjectiveTower {n : ℕ} {P U : Scheme.{u}} {π : P ⟶ U}
    {L : P.Modules} (h : IsProjectiveTower n π L) : IsLocallyProjectiveTower n π L :=
  fun _ ↦ ⟨⊤, trivial, h.restrict ⊤⟩

/-- **Locally projective towers are stable under base change.** In a cartesian square
`P' = U' ×_U P`, if `π : P ⟶ U` with `L` is a projective tower of fibre dimension `n` locally on
`U`, then `π' : P' ⟶ U'` with any module isomorphic to the pullback of `L` is one locally on
`U'`: over the preimage of a trivializing open of `U` the square restricts to a cartesian square.
-/
theorem IsLocallyProjectiveTower.of_isPullback {n : ℕ} {P U : Scheme.{u}} {π : P ⟶ U}
    {L : P.Modules} (h : IsLocallyProjectiveTower n π L) {P' U' : Scheme.{u}} {π' : P' ⟶ U'}
    {g' : P' ⟶ P} {g : U' ⟶ U} (hsq : IsPullback g' π' π g) {L' : P'.Modules}
    (e : L' ≅ (Scheme.Modules.pullback g').obj L) : IsLocallyProjectiveTower n π' L' := by
  intro x'
  obtain ⟨V, hxV, hV⟩ := h (g x')
  refine ⟨g ⁻¹ᵁ V, hxV, hV.of_isPullback (isPullback_morphismRestrict_of_isPullback hsq V) ?_⟩
  exact pullbackIsoOfComm (Scheme.Hom.resLE_comp_ι _ _).symm e

/-- **Base change of a locally projective tower along an arbitrary morphism**, in Mathlib's
chosen fibre product. -/
theorem IsLocallyProjectiveTower.pullback {n : ℕ} {P U : Scheme.{u}} {π : P ⟶ U}
    {L : P.Modules} (h : IsLocallyProjectiveTower n π L) {U' : Scheme.{u}} (g : U' ⟶ U) :
    IsLocallyProjectiveTower n (pullback.snd π g)
      ((Scheme.Modules.pullback (pullback.fst π g)).obj L) :=
  h.of_isPullback (IsPullback.of_hasPullback π g) (Iso.refl _)

/-- **Restriction of a locally projective tower to an open of the base.** -/
theorem IsLocallyProjectiveTower.restrict {n : ℕ} {P U : Scheme.{u}} {π : P ⟶ U}
    {L : P.Modules} (h : IsLocallyProjectiveTower n π L) (V : U.Opens) :
    IsLocallyProjectiveTower n (π ∣_ V) ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L) :=
  h.of_isPullback (isPullback_morphismRestrict π V).flip (Iso.refl _)

/-- **Restriction of a locally projective tower to a closed subscheme of the base**: over a
closed subscheme `W` of `U`, the restriction `π⁻¹(W) ⟶ W` of `π` with the pullback of `L` to the
inverse image of `W` is a projective tower locally on `W`. -/
theorem IsLocallyProjectiveTower.comapRestrict {n : ℕ} {P U : Scheme.{u}} {π : P ⟶ U}
    {L : P.Modules} (h : IsLocallyProjectiveTower n π L) (W : U.IdealSheafData) :
    IsLocallyProjectiveTower n (Stacks.Chow.comapRestrict W π)
      ((Scheme.Modules.pullback (W.comap π).subschemeι).obj L) :=
  h.of_isPullback (isPullback_comapRestrict W π) (Iso.refl _)

/-- A locally projective tower stays one when its module is replaced by an isomorphic one. -/
theorem IsLocallyProjectiveTower.of_iso_module {n : ℕ} {P U : Scheme.{u}} {π : P ⟶ U}
    {L L' : P.Modules} (h : IsLocallyProjectiveTower n π L) (e : L' ≅ L) :
    IsLocallyProjectiveTower n π L' :=
  h.of_isPullback (IsPullback.of_horiz_isIso (fst := 𝟙 P) (g := 𝟙 U) ⟨by simp⟩)
    (pullbackIdIsoOfIso e)

end Stacks.Chow

end
