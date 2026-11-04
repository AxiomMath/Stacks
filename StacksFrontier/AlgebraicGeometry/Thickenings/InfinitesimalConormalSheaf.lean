module

public import StacksFrontier.AlgebraicGeometry.Conormal.SquareEpi
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.TwoImmersionsConormalMono
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.TwoImmersionsConormalSequence
public import StacksFrontier.AlgebraicGeometry.PullbackPseudofunctor.Basic
public import StacksFrontier.AlgebraicGeometry.Thickenings.InfinitesimalIdealSheaf

/-!
# The conormal sheaf of a first-order infinitesimal neighbourhood (Stacks 04F0)

Let `i : Z ⟶ X` be an immersion of schemes and let `Z ⊂ Z'` be its first-order infinitesimal
neighbourhood of [Stacks Project, Tag 04EY]. The commutative square

```
Z  ⟶  Z'
↓      ↓
Z  ⟶  X
```

whose vertical arrows are the identity of `Z` and the structure morphism of the neighbourhood
induces, by [Stacks Project, Tag 01R4], a morphism of conormal sheaves `𝒞_{Z/X} ⟶ 𝒞_{Z/Z'}`.
This file proves [Stacks Project, Tag 04F0]: that morphism is an **isomorphism**.

## Main results

* `Stacks.Thickenings.isIso_conormalTransitivityMap_nthOrderInclusion` is
  [Stacks Project, Tag 04F0]: the canonical map `𝒞_{Z/X} ⟶ 𝒞_{Z/Z'}` is an isomorphism.
* `Stacks.Thickenings.isIso_infinitesimalImmersionConormalSheafMap` is the same statement for the
  map of [Stacks Project, Tag 01R4] out of the pullback along the identity of `Z`.
* `Stacks.Thickenings.epi_infinitesimalImmersionConormalSheafMap` and
  `Stacks.Thickenings.isPullback_nthOrderInclusion`: the square is cartesian, so the map is
  surjective by the clause of [Stacks Project, Tag 0473] already in the library.
* `Stacks.Thickenings.chart_app_surjective_and_ker` is the chart computation the proof rests on:
  over the image in `X` of an affine open `V` of the ambient open subscheme, the section map of
  `Z' ⟶ X` is surjective with kernel the **square** of the ideal cutting out `Z`.

## Implementation notes

Sheaves of modules on a space form an abelian category, so an epimorphism that is also a
monomorphism is an isomorphism; surjectivity is already available, and what is proved here is
monomorphy.

Monomorphy is checked on sections, as in
`Stacks.ConormalSequenceTwoImmersions.mono_conormalTransitivityMap_of_formallySmooth`. The affine
characterization of [Stacks Project, Tag 01R4],
`Stacks.Immersion.IsInducedConormalSheafMap`, identifies the map on the sections over a
compatible pair of affine opens with `Ideal.mapCotangent`; the charts used are the preimages
`Z' ∩ V` of the affine opens `V` of `AlgebraicGeometry.Scheme.Hom.coborderRange`, over which the
neighbourhood is cut out by the square of the ideal of `Z`. The algebraic input is then
`Stacks.Thickenings.toCotangent_eq_of_ker_eq_sq`: for a surjection `A ⟶ C` whose kernel is `J²`
and `I = J·C`, the map `J/J² ⟶ I/I²` is injective, since an element of `J` landing in
`I² = J²·C` differs from an element of `J²` by one of `ker = J²`. Those charts meet `Z` in
arbitrarily small opens because the closed-immersion factorization of `i` is a topological
embedding, so the sheaf condition upgrades injectivity on them to monomorphy.

The argument is carried out for an abstract factorization `Z ⟶ Z₁ ⟶ X` with the chart properties
as hypotheses — `Stacks.Thickenings.mono_immersionConormalSheafMap_of_charts` — and only then
instantiated at the infinitesimal neighbourhood. This is not cosmetic: with `Z₁` spelled as
`AlgebraicGeometry.Scheme.IdealSheafData.subscheme`, every definitional-equality check performed
on a sheaf of modules over it unfolds that construction, and the kernel does not finish.

## References

* [Stacks Project, Tag 04EY](https://stacks.math.columbia.edu/tag/04EY)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 0473](https://stacks.math.columbia.edu/tag/0473)
* [Stacks Project, Tag 04F0](https://stacks.math.columbia.edu/tag/04F0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.ClosedImmersion Stacks.ClosedImmersion.AffineConormal
open Stacks.ClosedImmersion.IdealSheafAffine

universe u

namespace Stacks.Thickenings

/-! ### Generalities on section maps -/

/-- Two equal morphisms of schemes have equal restricted section maps. -/
private lemma appLE_congr {A C : Scheme.{u}} {f f' : A ⟶ C} (h : f = f') {O : C.Opens}
    {T : A.Opens} (hT : T ≤ f ⁻¹ᵁ O) (hT' : T ≤ f' ⁻¹ᵁ O) :
    f.appLE O T hT = f'.appLE O T hT' := by
  subst h
  congr 1


/-- Over the full preimage the restricted section map is the section map, so the two have the
same kernel. -/
private lemma ker_appLE_eq_ker_app {A C : Scheme.{u}} (f : A ⟶ C) (O : C.Opens) (T : A.Opens)
    (hT : T ≤ f ⁻¹ᵁ O) (hTeq : T = f ⁻¹ᵁ O) :
    RingHom.ker (f.appLE O T hT).hom = RingHom.ker (f.app O).hom := by
  subst hTeq
  rw [Scheme.Hom.appLE_eq_app]

/-- For a factorization `f ≫ g = h`, the section map of `h` over `O` and `f ⁻¹ᵁ V` is the section
map of `g` over `O` and `V` followed by the section map of `f` over `V`. -/
private lemma hom_appLE_eq_comp_app {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (h : A ⟶ C)
    (hc : f ≫ g = h) (O : C.Opens) (V : B.Opens) (hV : V ≤ g ⁻¹ᵁ O) (hT : f ⁻¹ᵁ V ≤ h ⁻¹ᵁ O) :
    (h.appLE O (f ⁻¹ᵁ V) hT).hom = (f.app V).hom.comp (g.appLE O V hV).hom := by
  subst hc
  have h1 := Scheme.Hom.appLE_comp_appLE f g O V (f ⁻¹ᵁ V) hV le_rfl
  rw [Scheme.Hom.appLE_eq_app] at h1
  rw [← CommRingCat.hom_comp, h1]

/-- For a factorization `f ≫ g = h` with `f ⁻¹ᵁ V = h ⁻¹ᵁ O`, the section map of `g` pulls the
kernel of the section map of `f` over `V` back to the kernel of that of `h` over `O`. -/
private lemma comap_ker_app_eq {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (h : A ⟶ C)
    (hc : f ≫ g = h) (O : C.Opens) (V : B.Opens) (hV : V ≤ g ⁻¹ᵁ O) (hpre : f ⁻¹ᵁ V = h ⁻¹ᵁ O) :
    (RingHom.ker (f.app V).hom).comap (g.appLE O V hV).hom = RingHom.ker (h.app O).hom := by
  rw [RingHom.comap_ker, ← hom_appLE_eq_comp_app f g h hc O V hV hpre.le,
    ker_appLE_eq_ker_app h O _ hpre.le hpre]

/-- Contraction along a bijective ring map commutes with powers of an ideal. -/
private lemma comap_pow_of_bijective {A C : Type u} [CommRing A] [CommRing C] (ρ : A →+* C)
    (hρ : Function.Bijective ρ) (L : Ideal C) (n : ℕ) :
    (L ^ n).comap ρ = (L.comap ρ) ^ n := by
  conv_lhs => rw [← Ideal.map_comap_of_surjective ρ hρ.2 L]
  rw [← Ideal.map_pow, Ideal.comap_map_of_surjective ρ hρ.2,
    Ideal.comap_bot_of_injective ρ hρ.1, sup_bot_eq]

/-- An affine open of the ambient scheme inside the coborder of the range of an immersion
carries an affine model of the scheme-theoretic intersection. -/
private theorem exists_affineModel_of_restrict {A C : Scheme.{u}} (f : A ⟶ C)
    (O : C.Opens) (hO : IsAffineOpen O) (hcl : IsClosedImmersion (f ∣_ O)) :
    ∃ (L : Ideal Γ(C, O)) (e : pullback f O.ι ≅ Spec (quotRing L)),
      pullback.snd f O.ι ≫ hO.isoSpec.hom = e.hom ≫ quotImmersion Γ(C, O) L := by
  let _ : IsClosedImmersion (f ∣_ O) := hcl
  have : IsClosedImmersion ((f ∣_ O) ≫ hO.isoSpec.hom) := inferInstance
  obtain ⟨L, e₀, he₀⟩ :=
    (IsClosedImmersion.Spec_iff (f := (f ∣_ O) ≫ hO.isoSpec.hom)).mp inferInstance
  refine ⟨L, pullbackRestrictIsoRestrict f O ≪≫ e₀, ?_⟩
  rw [Iso.trans_hom, Category.assoc, ← he₀, ← Category.assoc,
    pullbackRestrictIsoRestrict_hom_morphismRestrict]

/-- An affine open of the ambient scheme inside the coborder of the range of an immersion
carries an affine model of the scheme-theoretic intersection. -/
private theorem exists_affineModel {A C : Scheme.{u}} (f : A ⟶ C) [IsImmersion f]
    (O : C.Opens) (hO : IsAffineOpen O) (hOc : O ≤ f.coborderRange) :
    ∃ (L : Ideal Γ(C, O)) (e : pullback f O.ι ≅ Spec (quotRing L)),
      pullback.snd f O.ι ≫ hO.isoSpec.hom = e.hom ≫ quotImmersion Γ(C, O) L :=
  exists_affineModel_of_restrict f O hO (by
    have h := isClosedImmersion_resLE_of_le_coborderRange f O hOc
    rwa [Scheme.Hom.resLE_eq_morphismRestrict] at h)

/-- An affine open of the target of a closed immersion carries an affine model of the
scheme-theoretic preimage. -/
private theorem exists_affineModel_of_isClosedImmersion {A C : Scheme.{u}} (f : A ⟶ C)
    [IsClosedImmersion f] (O : C.Opens) (hO : IsAffineOpen O) :
    ∃ (L : Ideal Γ(C, O)) (e : pullback f O.ι ≅ Spec (quotRing L)),
      pullback.snd f O.ι ≫ hO.isoSpec.hom = e.hom ≫ quotImmersion Γ(C, O) L :=
  exists_affineModel_of_restrict f O hO
    (MorphismProperty.of_isPullback (isPullback_morphismRestrict f O).flip inferInstance)

/-- The affine model ideal of a chart is the kernel of the map on sections. -/
private theorem ker_app_eq_of_affineModel {A C : Scheme.{u}} (f : A ⟶ C) [IsImmersion f]
    (O : C.Opens) (hO : IsAffineOpen O) (L : Ideal Γ(C, O))
    (e : pullback f O.ι ≅ Spec (quotRing L))
    (he : pullback.snd f O.ι ≫ hO.isoSpec.hom = e.hom ≫ quotImmersion Γ(C, O) L) :
    RingHom.ker (f.app O).hom = L := by
  rw [Scheme.Hom.app_eq_appLE]
  exact Stacks.Conormal.ker_appLE_eq_of_affineModel f O hO L e he

/-! ### Generalities on monomorphisms of sheaves of modules -/


/-- **A morphism out of the pullback along an identity is a monomorphism as soon as its
transpose is**, the unit of the adjunction being an isomorphism. -/
private theorem mono_of_mono_homEquiv {W : Scheme.{u}}
    {M N : SheafOfModules.{u} (structureSheafRing W.toLocallyRingedSpace.toRingedSpace)}
    (c : (modulePullback (Scheme.Hom.toLRSHom (𝟙 W)).toShHom).obj M ⟶ N)
    (hm : Mono ((modulePullbackPushforwardAdjunction
      (Scheme.Hom.toLRSHom (𝟙 W)).toShHom).homEquiv M N c)) : Mono c := by
  rw [Stacks.ConormalSequenceTwoImmersions.homEquiv_id_eq] at hm
  exact Stacks.ConormalSequenceTwoImmersions.mono_of_comp_mono
    (r := ((Stacks.PullbackPseudofunctor.modulePullbackIdIso
      W.toLocallyRingedSpace.toRingedSpace).app M).hom)
    (by rw [Stacks.ConormalSequenceTwoImmersions.unit_id_eq]; exact Iso.hom_inv_id _) hm

/-! ### The algebraic input -/

/-- **The conormal comparison of a square-zero quotient is injective.** Let `ρ : A ⟶ C` be a
surjective ring map whose kernel is the square of an ideal `J ⊆ A`, and let `I = J·C`. Then two
classes in `J/J²` whose images in `I/I²` agree are equal. -/
private theorem toCotangent_eq_of_ker_eq_sq {A C : Type u} [CommRing A] [CommRing C]
    (ρ : A →+* C) (J : Ideal A) (I : Ideal C) (hsurj : Function.Surjective ρ)
    (hker : RingHom.ker ρ = J ^ 2) (hI : I = J.map ρ)
    (hmem : ∀ a ∈ J, ρ a ∈ I) (a a' : J)
    (h : I.toCotangent ⟨ρ (a : A), hmem _ a.2⟩ = I.toCotangent ⟨ρ (a' : A), hmem _ a'.2⟩) :
    J.toCotangent a = J.toCotangent a' := by
  have hsub : (⟨ρ (a : A), hmem _ a.2⟩ - ⟨ρ (a' : A), hmem _ a'.2⟩ : I) =
      ⟨ρ ((a : A) - (a' : A)), by rw [map_sub]; exact sub_mem (hmem _ a.2) (hmem _ a'.2)⟩ := by
    apply Subtype.ext
    simp [map_sub]
  have hzero : I.toCotangent ⟨ρ ((a : A) - (a' : A)), by
      rw [map_sub]; exact sub_mem (hmem _ a.2) (hmem _ a'.2)⟩ = 0 := by
    rw [← hsub, map_sub, h, sub_self]
  rw [Ideal.toCotangent_eq_zero] at hzero
  have hpow : I ^ 2 = (J ^ 2).map ρ := by rw [hI, Ideal.map_pow]
  rw [hpow] at hzero
  obtain ⟨t, ht, hteq⟩ := (Ideal.mem_map_iff_of_surjective ρ hsurj).mp hzero
  have hdiff : (a : A) - (a' : A) - t ∈ RingHom.ker ρ := by
    rw [RingHom.mem_ker, map_sub, hteq, sub_self]
  rw [hker] at hdiff
  have hmem2 : (a : A) - (a' : A) ∈ J ^ 2 := by
    have := add_mem hdiff ht
    simpa using this
  have : J.toCotangent (a - a') = 0 := (J.toCotangent_eq_zero _).2 (by simpa using hmem2)
  rw [map_sub, sub_eq_zero] at this
  exact this

/-! ### The comparison for an abstract square-zero chart -/

section General

variable {Z X Z₁ : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (i₁ : Z ⟶ Z₁) [IsImmersion i₁]
  (g : Z₁ ⟶ X)

omit [IsImmersion i] [IsImmersion i₁] in
/-- **The chart computation, for an abstract square-zero thickening.** Over a compatible pair of
affine opens on which the section map of `g` is surjective with kernel the square of the ideal
`J` cutting out `Z`, two classes in `J/J²` with the same image in `I/I²` agree. -/
private theorem toCotangent_eq_of_square (hc : i₁ ≫ g = i) (U : Z₁.Opens) (V : X.Opens)
    (hUV : U ≤ g ⁻¹ᵁ V) (hpre : i₁ ⁻¹ᵁ U = i ⁻¹ᵁ V)
    (hsurj : Function.Surjective (g.appLE V U hUV).hom)
    (hker : RingHom.ker (g.appLE V U hUV).hom = RingHom.ker (i.app V).hom ^ 2)
    (I : Ideal Γ(Z₁, U)) (J : Ideal Γ(X, V))
    (hI : RingHom.ker (i₁.app U).hom = I) (hJ : RingHom.ker (i.app V).hom = J)
    (hmem : ∀ a ∈ J, (g.appLE V U hUV).hom a ∈ I) (a a' : J)
    (h : I.toCotangent ⟨_, hmem _ a.2⟩ = I.toCotangent ⟨_, hmem _ a'.2⟩) :
    J.toCotangent a = J.toCotangent a' := by
  have hcomapI : I.comap (g.appLE V U hUV).hom = J := by
    rw [← hI, ← hJ]
    exact comap_ker_app_eq i₁ g i hc V U hUV hpre
  refine toCotangent_eq_of_ker_eq_sq _ J I hsurj (by rw [hker, hJ]) ?_ hmem a a' h
  rw [← hcomapI, Ideal.map_comap_of_surjective _ hsurj]

/-- **The conormal comparison is injective on the sections over one square-zero chart.** On a
compatible pair of affine opens the comparison of [Stacks Project, Tag 01R4] carries the class of
`a` in `J/J²` to the class of its image in `I/I²`, which is injective by
`Stacks.Thickenings.toCotangent_eq_of_square`. -/
private theorem injective_conormalSections_app_of_square (hc : i₁ ≫ g = i)
    (U : Z₁.Opens) (V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : U ≤ g ⁻¹ᵁ V) (hpre : i₁ ⁻¹ᵁ U = i ⁻¹ᵁ V)
    (hsurj : Function.Surjective (g.appLE V U hUV).hom)
    (hker : RingHom.ker (g.appLE V U hUV).hom = RingHom.ker (i.app V).hom ^ 2)
    (I : Ideal Γ(Z₁, U)) (J : Ideal Γ(X, V))
    (eZ : pullback i₁ U.ι ≅ Spec (quotRing I))
    (heZ : pullback.snd i₁ U.ι ≫ hU.isoSpec.hom = eZ.hom ≫ quotImmersion Γ(Z₁, U) I)
    (eW : pullback i V.ι ≅ Spec (quotRing J))
    (heW : pullback.snd i V.ι ≫ hV.isoSpec.hom = eW.hom ≫ quotImmersion Γ(X, V) J) :
    Function.Injective (ConcreteCategory.hom
      (((modulePullbackPushforwardAdjunction (Scheme.Hom.toLRSHom (𝟙 Z)).toShHom).homEquiv
        (Stacks.ClosedImmersion.conormalSheaf i.liftCoborder.toLRSHom.toShHom)
        (Stacks.ClosedImmersion.conormalSheaf i₁.liftCoborder.toLRSHom.toShHom)
        (Stacks.Immersion.immersionConormalSheafMap i₁ i (𝟙 Z) g
          (Stacks.Immersion.toShHom_square
            (hc.trans (Category.id_comp i).symm)))).val.app (op (i ⁻¹ᵁ V)))) := by
  have hI : RingHom.ker (i₁.app U).hom = I := ker_app_eq_of_affineModel i₁ U hU I eZ heZ
  have hJ : RingHom.ker (i.app V).hom = J := ker_app_eq_of_affineModel i V hV J eW heW
  have hmem : ∀ c ∈ J, (g.appLE V U hUV).hom c ∈ I := fun c hc' =>
    Stacks.Immersion.immersionConormalSheafMap_ideal_mem i₁ i (𝟙 Z) g
      (hc.trans (Category.id_comp i).symm) U hU V hV hUV I J eZ heZ eW heW ⟨c, hc'⟩
  have hchar := Stacks.Immersion.isInducedConormalSheafMap_immersionConormalSheafMap
    i₁ i (𝟙 Z) g (hc.trans (Category.id_comp i).symm) U hU V hV hUV I J eZ heZ eW heW
  have key := fun c : J =>
    hchar c ⟨(g.appLE V U hUV).hom (c : Γ(X, V)), hmem _ c.2⟩ rfl
  intro x y hxy
  have hsurj' : ∀ z, ∃ a : J,
      (Stacks.Conormal.affineConormalIsoCotangent i V hV J eW heW).inv.hom (J.toCotangent a) = z :=
    fun z => by
      obtain ⟨a, ha⟩ := J.toCotangent_surjective
        ((Stacks.Conormal.affineConormalIsoCotangent i V hV J eW heW).hom.hom z)
      exact ⟨a, by rw [ha, ← ModuleCat.hom_comp_apply, Iso.hom_inv_id]; rfl⟩
  obtain ⟨a, hx⟩ := hsurj' x
  obtain ⟨a', hy⟩ := hsurj' y
  have h3 : (Stacks.Conormal.affineConormalIsoCotangent i₁ U hU I eZ heZ).inv.hom
        (I.toCotangent ⟨_, hmem _ a.2⟩) =
      (Stacks.Conormal.affineConormalIsoCotangent i₁ U hU I eZ heZ).inv.hom
        (I.toCotangent ⟨_, hmem _ a'.2⟩) := by
    rw [← key a, ← key a', hx, hy, hxy]
  rw [← hx, ← hy, toCotangent_eq_of_square i i₁ g hc U V hUV hpre hsurj hker I J hI hJ hmem a a'
    (Stacks.ConormalSequenceTwoImmersions.injective_iso_inv
      (Stacks.Conormal.affineConormalIsoCotangent i₁ U hU I eZ heZ) h3)]

/-- **The conormal comparison of a square-zero thickening is a monomorphism.** The hypothesis is
that `Z` has arbitrarily small neighbourhoods of the form `i⁻¹(V)` for a compatible pair of
affine opens `U ⊆ Z₁`, `V ⊆ X` over which the section map of `g` is surjective with kernel the
square of the ideal cutting out `Z`. -/
private theorem mono_immersionConormalSheafMap_of_charts (hc : i₁ ≫ g = i)
    (hch : ∀ (W : Z.Opens) (z : Z), z ∈ W → ∃ (U : Z₁.Opens) (V : X.Opens),
      IsAffineOpen U ∧ IsAffineOpen V ∧ V ≤ i.coborderRange ∧ IsClosedImmersion (i₁ ∣_ U) ∧
      ∃ hUV : U ≤ g ⁻¹ᵁ V, i₁ ⁻¹ᵁ U = i ⁻¹ᵁ V ∧ z ∈ i ⁻¹ᵁ V ∧ i ⁻¹ᵁ V ≤ W ∧
        Function.Surjective (g.appLE V U hUV).hom ∧
        RingHom.ker (g.appLE V U hUV).hom = RingHom.ker (i.app V).hom ^ 2) :
    Mono (Stacks.Immersion.immersionConormalSheafMap i₁ i (𝟙 Z) g
      (Stacks.Immersion.toShHom_square (hc.trans (Category.id_comp i).symm))) := by
  refine mono_of_mono_homEquiv _
    (Stacks.ConormalSequenceTwoImmersions.mono_of_app_injective_nbhd _ fun W z hzW => ?_)
  obtain ⟨U, V, hU, hV, hVc, hcl, hUV, hpre, hzV, hVW, hsurj, hker⟩ := hch W z hzW
  obtain ⟨I, eZ, heZ⟩ := exists_affineModel_of_restrict i₁ U hU hcl
  obtain ⟨J, eW, heW⟩ := exists_affineModel i V hV hVc
  exact ⟨i ⁻¹ᵁ V, hVW, hzV, injective_conormalSections_app_of_square i i₁ g hc U V hU hV hUV
    hpre hsurj hker I J eZ heZ eW heW⟩

end General

/-! ### The charts of the infinitesimal neighbourhood -/
variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]

/-- The chart of the first-order infinitesimal neighbourhood over the image in `X` of an open of
the ambient open subscheme is the preimage of that open. -/
theorem nthOrderToBase_preimage_image (V : i.coborderRange.toScheme.Opens) :
    nthOrderToBase i 1 ⁻¹ᵁ (i.coborderRange.ι ''ᵁ V) = nthOrderι i 1 ⁻¹ᵁ V := by
  rw [nthOrderToBase_eq, Scheme.Hom.comp_preimage, Scheme.Hom.preimage_image_eq]

/-- `Z` meets the chart of the first-order infinitesimal neighbourhood in the same open in which
it meets the image of the chart in `X`. -/
theorem preimage_nthOrderInclusion_chart (V : i.coborderRange.toScheme.Opens) :
    nthOrderInclusion i 1 ⁻¹ᵁ (nthOrderι i 1 ⁻¹ᵁ V) = i ⁻¹ᵁ (i.coborderRange.ι ''ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage, nthOrderInclusion_nthOrderι,
    Scheme.Hom.liftCoborder_preimage]

/-- **The chart computation behind [Stacks Project, Tag 04F0].** Over the image in `X` of an
affine open `V` of the ambient open subscheme, the section map of the first-order infinitesimal
neighbourhood is surjective and its kernel is the square of the ideal cutting out `Z`.

The map factors as the isomorphism `Γ(X, ι(V)) ≅ Γ(V)` of the open immersion followed by the
chart map of the neighbourhood, whose kernel is `K(V) ^ 2` by
`Stacks.Thickenings.ker_app_nthOrderι`. -/
theorem chart_app_surjective_and_ker (V : i.coborderRange.toScheme.Opens)
    (hVa : IsAffineOpen V) :
    Function.Surjective ((nthOrderToBase i 1).appLE (i.coborderRange.ι ''ᵁ V)
        (nthOrderι i 1 ⁻¹ᵁ V) (nthOrderToBase_preimage_image i V).ge).hom ∧
      RingHom.ker ((nthOrderToBase i 1).appLE (i.coborderRange.ι ''ᵁ V)
          (nthOrderι i 1 ⁻¹ᵁ V) (nthOrderToBase_preimage_image i V).ge).hom =
        RingHom.ker (i.app (i.coborderRange.ι ''ᵁ V)).hom ^ 2 := by
  have hBV : V ≤ i.coborderRange.ι ⁻¹ᵁ (i.coborderRange.ι ''ᵁ V) :=
    (i.coborderRange.ι.preimage_image_eq V).ge
  have hαbij : Function.Bijective
      (i.coborderRange.ι.appLE (i.coborderRange.ι ''ᵁ V) V hBV).hom := by
    rw [← Scheme.Hom.appIso_hom']
    exact ConcreteCategory.bijective_of_isIso _
  have hfac : ((nthOrderToBase i 1).appLE (i.coborderRange.ι ''ᵁ V)
        (nthOrderι i 1 ⁻¹ᵁ V) (nthOrderToBase_preimage_image i V).ge).hom =
      ((nthOrderι i 1).app V).hom.comp
        (i.coborderRange.ι.appLE (i.coborderRange.ι ''ᵁ V) V hBV).hom := by
    exact hom_appLE_eq_comp_app (nthOrderι i 1) i.coborderRange.ι (nthOrderToBase i 1)
      (nthOrderToBase_eq i 1).symm _ V hBV (nthOrderToBase_preimage_image i V).ge
  have hcomapK : (i.liftCoborder.ker.ideal ⟨V, hVa⟩).comap
      (i.coborderRange.ι.appLE (i.coborderRange.ι ''ᵁ V) V hBV).hom =
      RingHom.ker (i.app (i.coborderRange.ι ''ᵁ V)).hom := by
    have hker : i.liftCoborder.ker.ideal ⟨V, hVa⟩ =
        RingHom.ker (i.liftCoborder.app V).hom :=
      Scheme.Hom.ker_apply i.liftCoborder ⟨V, hVa⟩
    rw [hker]
    exact comap_ker_app_eq i.liftCoborder i.coborderRange.ι i i.liftCoborder_ι _ V hBV
      (Scheme.Hom.liftCoborder_preimage i V)
  have hsurjk : Function.Surjective ((nthOrderι i 1).app V).hom :=
    (i.liftCoborder.ker ^ (1 + 1)).subschemeι_app_surjective ⟨V, hVa⟩
  refine ⟨?_, ?_⟩
  · rw [hfac]
    exact hsurjk.comp hαbij.2
  · rw [hfac, ← RingHom.comap_ker, ker_app_nthOrderι i 1 ⟨V, hVa⟩,
      comap_pow_of_bijective _ hαbij, hcomapK]

/-! ### Monomorphy for the infinitesimal neighbourhood -/

/-- The commutative square of [Stacks Project, Tag 04F0]: the inclusion of `Z` into its
first-order infinitesimal neighbourhood over the immersion `i`. -/
theorem nthOrderSquare :
    nthOrderInclusion i 1 ≫ nthOrderToBase i 1 = 𝟙 Z ≫ i := by
  rw [Category.id_comp, nthOrderInclusion_toBase]

/-- The image in `X` of an affine open of the ambient open subscheme is an affine open contained
in the coborder of the range of `i`. -/
private theorem isAffineOpen_image_chart (V : i.coborderRange.toScheme.Opens)
    (hVa : IsAffineOpen V) :
    IsAffineOpen (i.coborderRange.ι ''ᵁ V) ∧ i.coborderRange.ι ''ᵁ V ≤ i.coborderRange := by
  refine ⟨(i.coborderRange.ι.isAffineOpen_iff_of_isOpenImmersion).mpr hVa, ?_⟩
  rintro x ⟨y, -, rfl⟩
  exact y.2

/-- **The charts cut out arbitrarily small opens of `Z`.** Every point of `Z` has, inside any
given neighbourhood, one of the form `i⁻¹(V)` for `V` the image in `X` of an affine open of the
ambient open subscheme. -/
private theorem exists_chart (W : Z.Opens) (z : Z) (hzW : z ∈ W) :
    ∃ V : i.coborderRange.toScheme.Opens, IsAffineOpen V ∧
      z ∈ i ⁻¹ᵁ (i.coborderRange.ι ''ᵁ V) ∧ i ⁻¹ᵁ (i.coborderRange.ι ''ᵁ V) ≤ W := by
  have hb := (i.coborderRange.toScheme).isBasis_affineOpens.of_isInducing
    i.liftCoborder.isEmbedding.isInducing
  obtain ⟨-, ⟨V, hVa, rfl⟩, hzV, hVW⟩ := Opens.isBasis_iff_nbhd.mp hb hzW
  have hpre : i ⁻¹ᵁ (i.coborderRange.ι ''ᵁ V) = i.liftCoborder ⁻¹ᵁ V :=
    (Scheme.Hom.liftCoborder_preimage i V).symm
  exact ⟨V, hVa, hpre ▸ hzV, hpre ▸ hVW⟩

/-- **The conormal comparison of [Stacks Project, Tag 04F0] is a monomorphism.** The charts of
the first-order infinitesimal neighbourhood satisfy the hypotheses of
`Stacks.Thickenings.mono_immersionConormalSheafMap_of_charts`: over the image in `X` of an affine
open `V` of the ambient open subscheme the section map of `Z₁ ⟶ X` is surjective with kernel the
square of the ideal cutting out `Z`, and those charts meet `Z` in arbitrarily small opens. -/
private theorem mono_infinitesimalImmersionConormalSheafMap :
    Mono (Stacks.Immersion.immersionConormalSheafMap (nthOrderInclusion i 1) i (𝟙 Z)
      (nthOrderToBase i 1) (Stacks.Immersion.toShHom_square (nthOrderSquare i))) := by
  refine mono_immersionConormalSheafMap_of_charts i (nthOrderInclusion i 1) (nthOrderToBase i 1)
    (nthOrderInclusion_toBase i 1) fun W z hzW => ?_
  obtain ⟨V, hVa, hzV, hVW⟩ := exists_chart i W z hzW
  obtain ⟨hV, hVc⟩ := isAffineOpen_image_chart i V hVa
  obtain ⟨hsurj, hker⟩ := chart_app_surjective_and_ker i V hVa
  exact ⟨nthOrderι i 1 ⁻¹ᵁ V, i.coborderRange.ι ''ᵁ V, hVa.preimage (nthOrderι i 1), hV, hVc,
    MorphismProperty.of_isPullback
      (isPullback_morphismRestrict (nthOrderInclusion i 1) (nthOrderι i 1 ⁻¹ᵁ V)).flip
      inferInstance,
    (nthOrderToBase_preimage_image i V).ge, preimage_nthOrderInclusion_chart i V, hzV, hVW,
    hsurj, hker⟩

/-! ### Tag 04F0 -/

/-- The square of [Stacks Project, Tag 04F0] is cartesian: its left edge is the identity and its
right edge `Z₁ ⟶ X` is an immersion, hence a monomorphism. -/
theorem isPullback_nthOrderInclusion :
    IsPullback (nthOrderInclusion i 1) (𝟙 Z) (nthOrderToBase i 1) i := by
  have : Mono i := inferInstance
  exact IsPullback.of_vert_isIso_mono (CommSq.mk (nthOrderSquare i))

/-- **The conormal comparison of [Stacks Project, Tag 04F0] is an epimorphism**, the square
being cartesian; this is the surjectivity clause of [Stacks Project, Tag 0473]. -/
theorem epi_infinitesimalImmersionConormalSheafMap :
    Epi (Stacks.Immersion.immersionConormalSheafMap (nthOrderInclusion i 1) i (𝟙 Z)
      (nthOrderToBase i 1) (Stacks.Immersion.toShHom_square (nthOrderSquare i))) :=
  Stacks.Immersion.epi_immersionConormalSheafMap _ _ _ _ (isPullback_nthOrderInclusion i)

/-- **Stacks Project, Tag 04F0, for the map of [Stacks Project, Tag 01R4].** The morphism
`𝒞_{Z/X} ⟶ 𝒞_{Z/Z'}` of conormal sheaves induced by the square relating the immersion `i` to the
inclusion of `Z` into its first-order infinitesimal neighbourhood `Z'` is an isomorphism.

Sheaves of modules form an abelian category, so it suffices that the morphism be both an
epimorphism — `Stacks.Thickenings.epi_infinitesimalImmersionConormalSheafMap` — and a
monomorphism. -/
theorem isIso_infinitesimalImmersionConormalSheafMap :
    IsIso (Stacks.Immersion.immersionConormalSheafMap (nthOrderInclusion i 1) i (𝟙 Z)
      (nthOrderToBase i 1) (Stacks.Immersion.toShHom_square (nthOrderSquare i))) := by
  have hm := mono_infinitesimalImmersionConormalSheafMap i
  have he := epi_infinitesimalImmersionConormalSheafMap i
  exact isIso_of_mono_of_epi _

/-- **Stacks Project, Tag 04F0.** For an immersion `i : Z ⟶ X` with first-order infinitesimal
neighbourhood `Z ⊂ Z'` of [Stacks Project, Tag 04EY], the canonical map of conormal sheaves
`𝒞_{Z/X} ⟶ 𝒞_{Z/Z'}` of [Stacks Project, Tag 01R4] is an isomorphism.

The map is `Stacks.ConormalSequenceTwoImmersions.conormalTransitivityMap` for the factorization
`Z ⟶ Z' ⟶ X` of `i`, which is the map of [Stacks Project, Tag 01R4] for the square with
horizontal arrows `Z ⟶ Z'` and `Z ⟶ X` and vertical arrows the identity of `Z` and `Z' ⟶ X`. -/
@[stacks 04F0]
theorem isIso_conormalTransitivityMap_nthOrderInclusion :
    IsIso (Stacks.ConormalSequenceTwoImmersions.conormalTransitivityMap
      (nthOrderInclusion i 1) i (nthOrderToBase i 1) (nthOrderInclusion_toBase i 1)) := by
  have hiso : IsIso ((Stacks.ConormalSequenceTwoImmersions.pullbackIdIso Z).inv.app
      (Stacks.Conormal.conormalSheaf i)) :=
    Iso.isIso_inv ((Stacks.ConormalSequenceTwoImmersions.pullbackIdIso Z).app
      (Stacks.Conormal.conormalSheaf i))
  rw [Stacks.ConormalSequenceTwoImmersions.conormalTransitivityMap, isIso_comp_left_iff]
  exact isIso_infinitesimalImmersionConormalSheafMap i

end Stacks.Thickenings

end
