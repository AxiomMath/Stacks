module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleClosedPointIdeal
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleSectionPairAvoidance
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleSectionPairClosedFibre
public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.GlobalSections

/-!
# Extending sections from the punctured closed fibre, and section pairs without depth

Let `A` be a Noetherian local ring with maximal ideal `𝔪` and let `f ∈ 𝔪`. Every section of a
quasi-coherent module `ℒ₀` on the closed fibre over the punctured closed fibre becomes the
restriction of a global section of `ℒ₀` after multiplication by a high enough power of any given
`g ∈ 𝔪`. With `Stacks.Algebraization.exists_mem_maximalIdeal_nonvanishing_smul_pow`, this gives a
section pair of an invertible triple whose punctured-spectrum member does not vanish on
`Ass(T.F) ∪ Ass(T.F / f T.F)`, with no depth hypothesis on `A`.

## Main definitions

* `Stacks.Algebraization.HasPowerExtendableClosedFibreSections`: a section over the punctured
  closed fibre extends to the closed fibre after multiplication by a power of any given element
  of the maximal ideal.

## Main results

* `AlgebraicGeometry.pullbackGlobalSections_restrictFunctorIsoPullback`: along an open immersion,
  the pullback map on global sections is restriction to the image, read through
  `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.exists_pow_smul_eq_restrict`: on a Noetherian
  affine scheme, a power of any global function in `I(X)` carries a section of a quasi-coherent
  module over `X \ V(I)` into the image of restriction from `X`.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.exists_pow_smul_eq_pullbackGlobalSections`: the
  same, with restriction written as `AlgebraicGeometry.pullbackGlobalSections`.
* `Stacks.Algebraization.globalSectionsMap_smul_scalars`: the canonical map on global sections
  carries the action of `A` through the two structure maps.
* `Stacks.Algebraization.hasPowerExtendableClosedFibreSections`: sections over the punctured
  closed fibre of a quasi-coherent module extend after multiplication by a power, for `f ∈ 𝔪`.
* `Stacks.Algebraization.exists_sectionPair_nonvanishing_on_associatedPoints_depthFree`: a
  section pair whose punctured-spectrum member does not vanish on `Ass(T.F) ∪ Ass(T.F / f T.F)`.
* `Stacks.Algebraization.exists_homUnit_nonvanishing_on_associatedPoints_depthFree`: the same,
  as a morphism of coherent triples out of the unit triple.

## References

* [Stacks Project, Tag 0F27](https://stacks.math.columbia.edu/tag/0F27)
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing Opposite
open Stacks.AlgebraicGeometry.IdealPower
open Stacks.AlgebraicGeometry.PrincipalIdealExtension

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-! ### Restriction to an open set, in its two spellings -/

private theorem pullbackGlobalSections_eq_unit_app (g : X ⟶ Y) (F : Y.Modules) (s : Γ(F, ⊤)) :
    pullbackGlobalSections g F s =
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F).app ⊤ s := by
  show ((Scheme.Modules.pullback g).obj F).presheaf.map (𝟙 (op (⊤ : X.Opens)))
      (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F).app (⊤ : Y.Opens) s) = _
  exact Functor.map_id_apply _ _ _

/-- Along an open immersion the canonical pullback map on global sections is restriction to the
image, read through `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`. -/
public theorem pullbackGlobalSections_restrictFunctorIsoPullback (i : Y ⟶ X)
    [IsOpenImmersion i] (F : X.Modules) (s : Γ(F, ⊤)) :
    pullbackGlobalSections i F s =
      ((Scheme.Modules.restrictFunctorIsoPullback i).hom.app F).app ⊤
        (F.presheaf.map (homOfLE (show i ''ᵁ (⊤ : Y.Opens) ≤ ⊤ from le_top)).op s) := by
  have h := CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app
    (Scheme.Modules.restrictAdjunction i) (Scheme.Modules.pullbackPushforwardAdjunction i) F
  have h' := congrArg (fun ψ => (Scheme.Modules.Hom.app ψ ⊤) s) h
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.restrictAdjunction_unit_app_app] at h'
  exact (pullbackGlobalSections_eq_unit_app i F s).trans h'.symm

/-- The sections of the restriction of `F` along an open immersion are the sections of `F` over
the image, `AlgebraicGeometry.Scheme.Modules.restrictAppIso` being the identity. -/
private theorem restrictAppIso_hom_apply (i : Y ⟶ X) [IsOpenImmersion i] (F : X.Modules)
    (V : Y.Opens) (x : Γ((Scheme.Modules.restrictFunctor i).obj F, V)) :
    (Scheme.Modules.restrictAppIso i F V).hom x = x := rfl

/-- Multiplying a section of the restriction of `F` by a function on the source is multiplying
the corresponding section of `F` by the corresponding function on the image. -/
private theorem smul_restrict_eq (i : Y ⟶ X) [IsOpenImmersion i] (F : X.Modules) (V : Y.Opens)
    (r : Γ(Y, V)) (x : Γ((Scheme.Modules.restrictFunctor i).obj F, V)) :
    r • x = (show Γ((Scheme.Modules.restrictFunctor i).obj F, V) from
      (i.appIso V).inv r • (show Γ(F, i ''ᵁ V) from x)) := rfl

/-- The function on the image corresponding to the pullback of a global function is the
restriction of that function to the image. -/
private theorem appIso_inv_appTop (i : Y ⟶ X) [IsOpenImmersion i] (a : Γ(X, ⊤)) :
    (i.appIso (⊤ : Y.Opens)).inv (i.appTop a)
      = X.presheaf.map (homOfLE (show i ''ᵁ (⊤ : Y.Opens) ≤ ⊤ from le_top)).op a := by
  have h := ConcreteCategory.congr_hom (Scheme.Hom.app_appIso_inv i (⊤ : X.Opens)) a
  rwa [ConcreteCategory.comp_apply] at h

end AlgebraicGeometry

namespace Stacks.AlgebraicGeometry.IdealPowerColimit

variable {X : Scheme.{u}}

/-! ### A power of a global function in `I` extends a section over the complement -/

/-- The value of a multiple of the unit section of `Iⁿ` is the multiplier. -/
private theorem val_smul_oneSection (I : X.IdealSheafData) (n : ℕ)
    (r : Γ(X, (I.support.compl : X.Opens))) :
    ((r • oneSection I n).1 : Γ(X, (I.support.compl : X.Opens))) = r :=
  mul_one r

/-- **A power of a global function in `I` carries a section over `X \ V(I)` into the image of
restriction from `X`.** Let `X` be a Noetherian affine scheme, `I` a quasi-coherent sheaf of
ideals, `F` a quasi-coherent module and `a ∈ I(X)`. Every section `s` of `F` over `X \ V(I)` has
`a^n|·s` in the image of `Γ(F, X) ⟶ Γ(F, X \ V(I))` for some `n`. -/
public theorem exists_pow_smul_eq_restrict [_root_.AlgebraicGeometry.IsNoetherian X] [IsAffine X]
    (I : X.IdealSheafData) (F : X.Modules) [F.IsQuasicoherent] {V : X.Opens}
    (hV : V = (I.support.compl : X.Opens)) (a : Γ(X, ⊤))
    (ha : a ∈ I.ideal ⟨⊤, isAffineOpen_top X⟩) (s : Γ(F, V)) :
    ∃ (n : ℕ) (t₀ : Γ(F, ⊤)),
      X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op (a ^ n) • s =
        F.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op t₀ := by
  subst hV
  obtain ⟨n, φ, hφ⟩ := exists_hom_idealPow_app_oneSection_eq_of_isQuasicoherent I F s
  have hmem : a ^ n ∈
      (idealPowerMultiple I n (structureModule X)).toSubmodule.obj (op (⊤ : X.Opens)) := by
    rw [obj_idealPow_affineOpen I n ⟨⊤, isAffineOpen_top X⟩]
    exact Ideal.pow_mem_pow ha n
  refine ⟨n, φ.app ⊤ ⟨a ^ n, hmem⟩, ?_⟩
  have hle : (I.support.compl : X.Opens) ≤ ⊤ := le_top
  have h1 : (((idealPow I n).presheaf.map (homOfLE hle).op ⟨a ^ n, hmem⟩).1
        : Γ(X, (I.support.compl : X.Opens)))
      = X.presheaf.map (homOfLE hle).op (a ^ n) :=
    val_map_idealPow I n hle ⟨a ^ n, hmem⟩
  have h2 : ((X.presheaf.map (homOfLE hle).op (a ^ n) • oneSection I n).1
        : Γ(X, (I.support.compl : X.Opens)))
      = X.presheaf.map (homOfLE hle).op (a ^ n) :=
    val_smul_oneSection I n _
  rw [app_naturality φ hle ⟨a ^ n, hmem⟩, Subtype.ext (h1.trans h2.symm),
    Scheme.Modules.Hom.app_smul, hφ]

/-- For an open `U` of a Noetherian affine scheme equal to the complement of the support of a
quasi-coherent sheaf of ideals `I`, and a global section `a` of `I`, every global section of
`U^* F` is carried by a power of `a` into the image of
`AlgebraicGeometry.pullbackGlobalSections U.ι F`. -/
public theorem exists_pow_smul_eq_pullbackGlobalSections
    [_root_.AlgebraicGeometry.IsNoetherian X] [IsAffine X] (I : X.IdealSheafData)
    (F : X.Modules) [F.IsQuasicoherent] (U : X.Opens)
    (hU : U = (I.support.compl : X.Opens)) (a : Γ(X, ⊤))
    (ha : a ∈ I.ideal ⟨⊤, isAffineOpen_top X⟩)
    (t : Γ((Scheme.Modules.pullback U.ι).obj F, ⊤)) :
    ∃ (n : ℕ) (t₀ : Γ(F, ⊤)),
      U.ι.appTop a ^ n • t = pullbackGlobalSections U.ι F t₀ := by
  have hiso : IsIso ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app F) :=
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app F).isIso_hom
  obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app F).app ⊤)).surjective t
  obtain ⟨n, t₀, h⟩ := exists_pow_smul_eq_restrict I F
    ((Scheme.Opens.ι_image_top U).trans hU) a ha
    ((Scheme.Modules.restrictAppIso U.ι F (⊤ : U.toScheme.Opens)).hom x)
  refine ⟨n, t₀, ?_⟩
  rw [← hx, ← Scheme.Modules.Hom.app_smul, pullbackGlobalSections_restrictFunctorIsoPullback]
  refine congrArg _ (Eq.trans ?_ h)
  rw [restrictAppIso_hom_apply, smul_restrict_eq, map_pow, appIso_inv_appTop, map_pow]

end Stacks.AlgebraicGeometry.IdealPowerColimit

namespace Stacks.Algebraization

/-! ### Linearity of the canonical map on global sections -/

/-- The canonical map on global sections carries the action of `A` through the structure maps of
the punctured spectrum and of the punctured closed fibre. -/
public theorem globalSectionsMap_smul_scalars (A : Type u) [CommRing A] [IsLocalRing A] (f : A)
    (T : CoherentTriple A f) (a : A) (x : Γ(T.F, ⊤)) :
    globalSectionsMap A f T (puncturedScalars A a • x) =
      puncturedClosedFibreScalars A f a • globalSectionsMap A f T x := by
  let := puncturedSectionsModule A T.F
  let := puncturedClosedFibreSectionsModule A f
    ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj T.F₀)
  exact (globalSectionsMap A f T).map_smul a x

/-! ### Extendability after multiplication by a power -/

/-- Every section of `F₀` over the punctured closed fibre extends to the closed fibre after
multiplication by a high enough power of any given element of the maximal ideal. -/
public def HasPowerExtendableClosedFibreSections {A : Type u} [CommRing A] [IsLocalRing A]
    (f : A) (F₀ : (closedFibre A f).Modules) : Prop :=
  ∀ g ∈ maximalIdeal A,
    ∀ t : Γ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj F₀, ⊤),
      ∃ (N : ℕ) (t₀ : Γ(F₀, ⊤)),
        puncturedClosedFibreScalars A f g ^ N • t =
          pullbackGlobalSections (puncturedClosedFibre A f).ι F₀ t₀

/-- For a Noetherian local ring `A`, an `f ∈ 𝔪` and a quasi-coherent module `ℒ₀` on the closed
fibre, every section of `ℒ₀` over the punctured closed fibre becomes the restriction of a global
section of `ℒ₀` after multiplication by a high enough power of any given `g ∈ 𝔪`. -/
public theorem hasPowerExtendableClosedFibreSections {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] {f : A} (hf : f ∈ maximalIdeal A)
    (F₀ : (closedFibre A f).Modules) [F₀.IsQuasicoherent] :
    HasPowerExtendableClosedFibreSections f F₀ := by
  have hI : Ideal.span {f} ≠ (⊤ : Ideal A) := fun h =>
    (maximalIdeal.isMaximal A).ne_top
      (top_unique (h ▸ Ideal.span_le.mpr (by simpa using hf)))
  have : Nontrivial (A ⧸ Ideal.span {f}) := Ideal.Quotient.nontrivial_iff.mpr hI
  let : IsLocalRing (A ⧸ Ideal.span {f}) := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk (Ideal.span {f})) Ideal.Quotient.mk_surjective
  have : IsLocalHom (Ideal.Quotient.mk (Ideal.span {f}) : A →+* A ⧸ Ideal.span {f}) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  intro g hg t
  have hgq : Ideal.Quotient.mk (Ideal.span {f}) g ∈ maximalIdeal (A ⧸ Ideal.span {f}) :=
    (IsLocalRing.mem_maximalIdeal _).mpr fun hu =>
      (IsLocalRing.mem_maximalIdeal _).mp hg (isUnit_of_map_unit _ g hu)
  obtain ⟨n, t₀, h⟩ :=
    Stacks.AlgebraicGeometry.IdealPowerColimit.exists_pow_smul_eq_pullbackGlobalSections
      (Scheme.Hom.ker
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (A ⧸ Ideal.span {f})))))
      F₀ (puncturedClosedFibre A f)
      ((puncturedClosedFibre_eq_puncturedSpectrum A f hf).trans
        (puncturedSpectrum_eq_support_compl (A ⧸ Ideal.span {f})))
      ((Scheme.ΓSpecIso (CommRingCat.of (A ⧸ Ideal.span {f}))).inv
        (Ideal.Quotient.mk (Ideal.span {f}) g))
      (by
        rw [closedPointIdealSheaf_ideal_top (A ⧸ Ideal.span {f})]
        exact Ideal.mem_map_of_mem _ hgq)
      t
  refine ⟨n, t₀, ?_⟩
  have hsc : puncturedClosedFibreScalars A f g =
      (puncturedClosedFibre A f).ι.appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (A ⧸ Ideal.span {f}))).inv
          (Ideal.Quotient.mk (Ideal.span {f}) g)) :=
    (congrArg (puncturedClosedFibre A f).ι.appTop (closedFibreScalars_eq A f g)).symm
  rwa [hsc]

/-! ### The section pair with no depth hypothesis -/

/-- For an invertible triple `L` over a Noetherian local ring, `f ∈ 𝔪` and any triple `T`, there
is a global section of each member of `L`, the two corresponding over the punctured closed fibre,
such that the punctured-spectrum member does not vanish at any point of
`Ass(T.F) ∪ Ass(T.F / f T.F)`. -/
public theorem exists_sectionPair_nonvanishing_on_associatedPoints_depthFree {A : Type u}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {f : A} (hf : f ∈ maximalIdeal A)
    {L : CoherentTriple A f} (hL : IsInvertibleTriple L) (T : CoherentTriple A f) :
    letI := hL.invertible_F
    ∃ (x : Γ(L.F, ⊤)) (x₀ : Γ(L.F₀, ⊤)),
      globalSectionsMap A f L x =
          pullbackGlobalSections (puncturedClosedFibre A f).ι L.F₀ x₀ ∧
        (Stacks.Divisors.associatedPoints T.F ∪
            Stacks.Divisors.associatedPoints
              (cokernel (smulPowHom T.F (scalarOnOpen A f ⊤) 1))) ⊆
          (Stacks.NonvanishingOpen.nonvanishingOpen
            (Stacks.Divisors.puncturedSpectrum A).toScheme L.F x : Set _) := by
  let := hL.invertible_F
  have := L.coherent_F₀
  have : L.F₀.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent L.F₀
  obtain ⟨g, hgm, x, hx⟩ := exists_mem_maximalIdeal_nonvanishing_smul_pow hL T
  obtain ⟨N, x₀, hx₀⟩ := hasPowerExtendableClosedFibreSections hf L.F₀ g hgm
    (globalSectionsMap A f L x)
  refine ⟨puncturedScalars A g ^ N • x, x₀, ?_, hx N⟩
  rwa [← map_pow, globalSectionsMap_smul_scalars, map_pow]

/-- For an invertible triple `L` over a Noetherian local ring, `f ∈ 𝔪` and any triple `T`, there
are a global section `x` of `L.F` not vanishing at any point of `Ass(T.F) ∪ Ass(T.F / f T.F)`
and a morphism of coherent triples from the unit triple to `L` whose punctured-spectrum member is
the morphism given by `x`. -/
public theorem exists_homUnit_nonvanishing_on_associatedPoints_depthFree {A : Type u}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {f : A} (hf : f ∈ maximalIdeal A)
    {L : CoherentTriple A f} (hL : IsInvertibleTriple L) (T : CoherentTriple A f) :
    letI := hL.invertible_F
    ∃ (x : Γ(L.F, ⊤))
      (φ : (CoherentTriple.unit A f hL.isFTorsionFree_unitModule).Hom L),
      φ.onPunctured = Scheme.Modules.unitHomEquivTop L.F x ∧
        (Stacks.Divisors.associatedPoints T.F ∪
            Stacks.Divisors.associatedPoints
              (cokernel (smulPowHom T.F (scalarOnOpen A f ⊤) 1))) ⊆
          (Stacks.NonvanishingOpen.nonvanishingOpen
            (Stacks.Divisors.puncturedSpectrum A).toScheme L.F x : Set _) := by
  let := hL.invertible_F
  obtain ⟨x, x₀, hx₀, hx⟩ :=
    exists_sectionPair_nonvanishing_on_associatedPoints_depthFree hf hL T
  exact ⟨x, CoherentTriple.homUnitOfGlobalSections hL.isFTorsionFree_unitModule x x₀ hx₀,
    rfl, hx⟩

end Stacks.Algebraization

end
