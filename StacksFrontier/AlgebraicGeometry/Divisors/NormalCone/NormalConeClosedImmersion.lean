module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceFiniteType
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalConeFunctorial
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.ClosedImmersion

/-!
# When a morphism of normal cones is a closed immersion

Let `i : Z ⟶ X` and `i' : Y ⟶ X'` be immersions, let `f : Z ⟶ Y`, and let
`H : AlgebraicGeometry.ConormalAlgebraHom i i' f` be a morphism of conormal graded algebras. It
induces `Stacks.Conormal.normalConeMap i i' f H : C_{Z/X} ⟶ C_{Y/X'}`, and this file gives the
criterion for that morphism to be a **closed immersion**: that the sectionwise maps
`H.map n : 𝒞_{Y/X',n}(W) ⟶ 𝒞_{Z/X,n}(f⁻¹W)` are surjective in every degree, for `W` running over
a family of affine opens of `Y` covering it whose preimages in `Z` are affine.

The criterion is then applied to the case this was written for: a chain of closed immersions
`Z ⟶ Y ⟶ X`, where the canonical morphism `C_{Z/Y} ⟶ C_{Z/X}` is a closed immersion
unconditionally.

## Main results

* `Stacks.Conormal.surjective_conormalUngradedPushforwardHom_app`: **degreewise surjectivity of
  `H` gives surjectivity on sections** of the morphism of algebra sheaves
  `𝒞_{Y/X',*} ⟶ f_* 𝒞_{Z/X,*}` over an open whose preimage is affine, and
  `Stacks.Conormal.surjective_conormalAlgebraSheafPushforwardHom_app`,
  `Stacks.Conormal.surjective_normalConePushforwardHom_app`: the same for the two spellings of
  that morphism the normal cone is built from.
* `Stacks.Conormal.isClosedImmersion_normalConeMap`: **the criterion.**
* `Stacks.Conormal.exists_mem_chartIdealPow`: on an affine chart of `X` the `n`-th power of the
  ideal of `Z` in `X` surjects onto the `n`-th power of the ideal of `Z` in `Y`.
* `Stacks.Conormal.surjective_nestedConormalHom_map`: hence the canonical morphism of conormal
  graded algebras `𝒞_{Z/X,*} ⟶ 𝒞_{Z/Y,*}` of a chain of closed immersions is surjective on
  sections over every conormal chart, in every degree.
* `Stacks.Conormal.isClosedImmersion_normalConeMapOfSquare_of_factorization`: **the canonical
  morphism `C_{Z/Y} ⟶ C_{Z/X}` of a chain of closed immersions `Z ⟶ Y ⟶ X` is a closed
  immersion.**

## Implementation notes

**Why the criterion is about sections and not about local surjectivity.** The criterion of
[Stacks, Tag 01LV] that `Stacks.RelativeSpec.isClosedImmersion_pairToHom` provides asks for
surjectivity of the algebra component of the pair *on sections* over the affine opens of the
base; `Stacks.SectionEpiAffine.surjective_sections_of_isLocallySurjective` would reduce that to
local surjectivity, but only for a morphism of quasi-coherent algebra sheaves on one base, and
the pair's component is a morphism into a direct image. So surjectivity on sections is proved
directly, and the route is the one the conormal algebra makes available: over an affine open the
sections of the ungraded realization of a sheaf of graded algebras are the direct sum of the
sections of the homogeneous pieces
(`Stacks.RelativeSpec.bijective_ungradedCommUnit_of_isAffineOpen`), every element is therefore a
finite sum of homogeneous ones, and a homogeneous one is hit as soon as `H` is surjective in that
degree.

**The degreewise surjectivity of the nested square needs no transport.** The conormal charts of
`Stacks.Conormal.ConormalAlgebraHom.IsCanonical` are indexed by an affine open `U'` of the
ambient `X` together with an affine open `U` of the intermediate `Y` with `U ≤ g⁻¹(U')`; taking
`U := g⁻¹(U')` and reading the chain as `Z ⟶ Y ⟶ X` with `iZ` *replaced by* `fZ ≫ g` makes the
two opens of `Z` that the sectionwise map relates, `fZ⁻¹(g⁻¹(U'))` and `(fZ ≫ g)⁻¹(U')`, equal by
`rfl`. That is why
`Stacks.Conormal.isClosedImmersion_normalConeMapOfSquare_of_factorization` substitutes along the
factorization before applying the criterion: with `iZ` a variable the two opens are only equal
propositionally, and the sectionwise maps would have to be transported along an equality of opens.

**The ideal-power surjectivity.** On an affine chart `U'` of `X` the ring map
`Γ(X, U') ⟶ Γ(Y, g⁻¹U')` is surjective because `g` is a closed immersion
(`AlgebraicGeometry.Scheme.Hom.app_surjective`), and the ideal of `Z` in the chart of `X` is the
comap of the ideal of `Z` in the chart of `Y` because the two structure maps compose. So the
`n`-th powers correspond under `Ideal.map`, by `Ideal.map_comap_of_surjective` and
`Ideal.map_pow`, and `Ideal.mem_map_iff_of_surjective` produces the representative that
`Stacks.Conormal.ConormalAlgebraHom.IsCanonical` consumes.

## References

* [Stacks Project, Tag 01LV](https://stacks.math.columbia.edu/tag/01LV)
* [Stacks Project, Tag 0630](https://stacks.math.columbia.edu/tag/0630)
* [Stacks Project, Tag 0634](https://stacks.math.columbia.edu/tag/0634)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.AffineAlgebraEquivalence Stacks.SymAlgSheaf Stacks.RelativeSpec

universe u

namespace Stacks.RelativeSpec

/-- An isomorphism of algebra sheaves is surjective on sections over any open: its inverse
provides the preimage. -/
theorem surjective_right_app_of_iso {S : Scheme.{u}} {A B : AlgebraSheaf S} (e : A ≅ B)
    (W : (Opens ↥S)ᵒᵖ) : Function.Surjective (e.hom.right.hom.app W).hom := fun t =>
  ⟨(e.inv.right.hom.app W).hom t,
    congrArg (fun k : B ⟶ B => (k.right.hom.app W).hom t) e.inv_hom_id⟩

/-- A composite of morphisms of algebra sheaves is surjective on sections over an open as soon as
both factors are. -/
theorem surjective_right_app_comp {S : Scheme.{u}} {A B C : AlgebraSheaf S} (a : A ⟶ B)
    (b : B ⟶ C) (W : (Opens ↥S)ᵒᵖ) (ha : Function.Surjective (a.right.hom.app W).hom)
    (hb : Function.Surjective (b.right.hom.app W).hom) :
    Function.Surjective ((a ≫ b).right.hom.app W).hom := hb.comp ha

end Stacks.RelativeSpec

namespace Stacks.Conormal

/-! ### Surjectivity on sections of the morphism of algebra sheaves -/

section Sections

variable {Z X Y X' : Scheme.{u}} (i : Z ⟶ X) (i' : Y ⟶ X') (f : Z ⟶ Y)
  [IsImmersion i] [IsImmersion i'] (H : ConormalAlgebraHom i i' f)

/-- The sheafification unit intertwines `Stacks.Conormal.conormalUngradedPushforwardHom` with the
morphism of presheaves of rings its unital homomorphism determines. This is the universal
property of sheafification, read at the definition of that morphism. -/
theorem ungradedCommToSheaf_comp_conormalUngradedPushforwardHom :
    ungradedCommToSheaf Y (conormalAlgebra i').algebra (conormalAlgebra i').mul_comm_int ≫
        (conormalUngradedPushforwardHom i i' f H).right.hom =
      ungradedCommHom (conormalAlgebra i').algebra (conormalAlgebra i').mul_comm_int
        (conormalPushforwardAlgebra i f) (conormalPushforwardUnitalHom i i' f H) :=
  congrArg Subtype.val
    ((ungradedAlgebraSheafHomEquiv (conormalAlgebra i').algebra
      (conormalAlgebra i').mul_comm_int (conormalPushforwardAlgebra i f)).apply_symm_apply
      ((ungradedCommHomEquiv (conormalAlgebra i').algebra
        (conormalAlgebra i').mul_comm_int (conormalPushforwardAlgebra i f)).symm
        (conormalPushforwardUnitalHom i i' f H)))

/-- **On a homogeneous section, `Stacks.Conormal.conormalUngradedPushforwardHom` is the image
under `H`**, included into the ungraded realization over the preimage open. -/
theorem conormalUngradedPushforwardHom_app_incl (n : ℤ) (W : Y.Opens)
    (x : ((conormalAlgebra i').algebra.piece n).val.obj (op W)) :
    ((conormalUngradedPushforwardHom i i' f H).right.hom.app (op W)).hom
        (ungradedAlgebraSheafIncl Y (conormalAlgebra i').algebra
          (conormalAlgebra i').mul_comm_int n W x) =
      ungradedAlgebraSheafIncl Z (conormalAlgebra i).algebra
        (conormalAlgebra i).mul_comm_int n (f ⁻¹ᵁ W)
        (H.map n (f ⁻¹ᵁ W) W le_rfl x) :=
  (ConcreteCategory.congr_hom
      (NatTrans.congr_app
        (ungradedCommToSheaf_comp_conormalUngradedPushforwardHom i i' f H) (op W))
      ((conormalAlgebra i').algebra.toPresheafGradedAlgebra.incl n x)).trans
    (ungradedTotal_incl (conormalAlgebra i').algebra (conormalPushforwardAlgebra i f)
      (conormalPushforwardUnitalHom i i' f H) n (op W) x)

/-- **Degreewise surjectivity of `H` over an open whose preimage is affine gives surjectivity on
sections of `𝒞_{Y/X',*} ⟶ f_* 𝒞_{Z/X,*}` there.** Over an affine open the sections of the
ungraded realization are the direct sum of the sections of the homogeneous pieces, so every
section of the target is a finite sum of homogeneous ones, and each of those is hit. -/
theorem surjective_conormalUngradedPushforwardHom_app (W : Y.Opens)
    (hW : IsAffineOpen (f ⁻¹ᵁ W))
    (hsurj : ∀ n : ℤ, Function.Surjective (H.map n (f ⁻¹ᵁ W) W le_rfl)) :
    Function.Surjective
      ((conormalUngradedPushforwardHom i i' f H).right.hom.app (op W)).hom := by
  have key : ∀ s : (conormalAlgebra i).algebra.toPresheafGradedAlgebra.Total (op (f ⁻¹ᵁ W)),
      ∃ p, ((conormalUngradedPushforwardHom i i' f H).right.hom.app (op W)).hom p =
        (ungradedCommUnit Z (conormalAlgebra i).algebra
          (conormalAlgebra i).mul_comm_int (f ⁻¹ᵁ W)).hom s := by
    intro s
    induction s using Stacks.GradedAlgebra.incl_induction with
    | zero => exact ⟨0, (map_zero _).trans (map_zero _).symm⟩
    | incl n y =>
        obtain ⟨x, hx⟩ := hsurj n y
        refine ⟨ungradedAlgebraSheafIncl Y (conormalAlgebra i').algebra
          (conormalAlgebra i').mul_comm_int n W x, ?_⟩
        exact (conormalUngradedPushforwardHom_app_incl i i' f H n W x).trans
          (congrArg (ungradedAlgebraSheafIncl Z (conormalAlgebra i).algebra
            (conormalAlgebra i).mul_comm_int n (f ⁻¹ᵁ W)) hx)
    | add s s' hs hs' =>
        obtain ⟨p, hp⟩ := hs
        obtain ⟨p', hp'⟩ := hs'
        exact ⟨p + p', (map_add _ _ _).trans
          ((congrArg₂ (· + ·) hp hp').trans (map_add _ _ _).symm)⟩
  intro t
  obtain ⟨s, hs⟩ := (bijective_ungradedCommUnit_of_isAffineOpen Z (conormalAlgebra i).algebra
    (conormalAlgebra i).mul_comm_int hW).2 t
  obtain ⟨p, hp⟩ := key s
  exact ⟨p, hp.trans hs⟩

/-- `Stacks.Conormal.surjective_conormalUngradedPushforwardHom_app` in the
`Stacks.RelativeSpec.gradedAlgebraSheaf` spelling the normal cone uses: the two spellings of the
ungraded realization differ by an isomorphism. -/
theorem surjective_conormalAlgebraSheafPushforwardHom_app (W : Y.Opens)
    (hW : IsAffineOpen (f ⁻¹ᵁ W))
    (hsurj : ∀ n : ℤ, Function.Surjective (H.map n (f ⁻¹ᵁ W) W le_rfl)) :
    Function.Surjective
      ((conormalAlgebraSheafPushforwardHom i i' f H).right.hom.app (op W)).hom :=
  ((surjective_right_app_of_iso
      ((algebraPushforward f).mapIso (ungradedAlgebraSheafIsoGradedAlgebraSheaf Z
        (conormalAlgebra i).algebra (conormalAlgebra i).mul_comm_int)) (op W)).comp
    (surjective_conormalUngradedPushforwardHom_app i i' f H W hW hsurj)).comp
  (surjective_right_app_of_iso (ungradedAlgebraSheafIsoGradedAlgebraSheaf Y
    (conormalAlgebra i').algebra (conormalAlgebra i').mul_comm_int).symm (op W))

variable [(conormalAlgebraSheaf i).IsQuasicoherent]

/-- The defining factorization of `Stacks.Conormal.normalConePushforwardHom`, as a lemma: the
identification of `𝒞_{Z/X,*}` with the pushed-forward structure sheaf of the normal cone is
`Stacks.AffineAlgebraEquivalence.pushforwardAlgebraIso`. -/
theorem normalConePushforwardHom_eq : normalConePushforwardHom i i' f H =
    conormalAlgebraSheafPushforwardHom i i' f H ≫
      (algebraPushforward f).map
        (X := conormalAlgebraSheaf i)
        (Y := pushforwardAlgebra (relativeSpecToBase (conormalAlgebraSheaf i)))
        (pushforwardAlgebraIso (conormalAlgebraSheaf i)).inv := rfl

/-- **The algebra component of the pair defining `Stacks.Conormal.normalConeMap` is surjective on
sections** over an open of the base whose preimage is affine, as soon as `H` is surjective there
in every degree. -/
theorem surjective_normalConePushforwardHom_app (W : Y.Opens)
    (hW : IsAffineOpen (f ⁻¹ᵁ W))
    (hsurj : ∀ n : ℤ, Function.Surjective (H.map n (f ⁻¹ᵁ W) W le_rfl)) :
    Function.Surjective
      ((normalConePushforwardHom i i' f H).right.hom.app (op W)).hom := by
  rw [normalConePushforwardHom_eq i i' f H]
  exact surjective_right_app_comp _ _ (op W)
    (surjective_conormalAlgebraSheafPushforwardHom_app i i' f H W hW hsurj)
    (surjective_right_app_of_iso ((algebraPushforward f).mapIso
      (pushforwardAlgebraIso (conormalAlgebraSheaf i)).symm) (op W))

variable [(conormalAlgebraSheaf i').IsQuasicoherent]

/-- **The morphism of normal cones attached to a degreewise surjective morphism of conormal
graded algebras is a closed immersion.** Surjectivity is asked for on sections over a family `V`
of affine opens covering the base `Y` whose preimages in `Z` are affine — which is where the
conormal algebra's sections are computable — and the conclusion is
`Stacks.RelativeSpec.isClosedImmersion_pairToHom` for the pair that defines
`Stacks.Conormal.normalConeMap`: the inverse image of `V a` in `C_{Z/X}` is affine because it is
the inverse image of the affine open `f⁻¹(V a)` of `Z` under the projection of a relative
spectrum. -/
theorem isClosedImmersion_normalConeMap {κ : Type*} (V : κ → Y.affineOpens)
    (hV : ⨆ a, (V a).1 = ⊤) (haff : ∀ a, IsAffineOpen (f ⁻¹ᵁ (V a).1))
    (hsurj : ∀ (a : κ) (n : ℤ),
      Function.Surjective (H.map n (f ⁻¹ᵁ (V a).1) (V a).1 le_rfl)) :
    IsClosedImmersion (normalConeMap i i' f H) :=
  Stacks.RelativeSpec.isClosedImmersion_pairToHom (s := normalConeSituation i') _ V hV
    (fun a => Stacks.RelativeSpec.isAffineOpen_toBase_preimage (normalConeSituation i)
      ⟨f ⁻¹ᵁ (V a).1, haff a⟩)
    (fun a => surjective_normalConePushforwardHom_app i i' f H (V a).1 (haff a) (hsurj a))

end Sections

/-! ### A chain of closed immersions -/

/-- A closed immersion restricts to a closed immersion over the inverse image of any open of the
target: being a closed immersion is local on the target. -/
theorem isClosedImmersion_resLE_self {W T : Scheme.{u}} (j : W ⟶ T) [IsClosedImmersion j]
    (U : T.Opens) : IsClosedImmersion (j.resLE U (j ⁻¹ᵁ U) le_rfl) := by
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  infer_instance

section Nested

variable {Z Y X : Scheme.{u}} (fZ : Z ⟶ Y) (g : Y ⟶ X)
  [IsClosedImmersion fZ] [IsClosedImmersion g]

/-- **On an affine chart `U` of `X` the `n`-th power of the ideal of `Z` in `X` surjects onto the
`n`-th power of the ideal of `Z` in `Y`.** The ring map `Γ(X, U) ⟶ Γ(Y, g⁻¹U)` is surjective
because `g` is a closed immersion, and it carries the one ideal onto the other because the two
ideals are kernels of maps that compose; `Ideal.map_pow` passes to the powers. -/
theorem exists_mem_chartIdealPow (U : X.affineOpens) (n : ℕ) (b : Γ(Y, g ⁻¹ᵁ U.1))
    (hb : b ∈ chartIdeal fZ ⟨g ⁻¹ᵁ U.1, U.2.preimage g⟩ ^ n) :
    ∃ a ∈ chartIdeal (fZ ≫ g) U ^ n, (g.app U.1).hom a = b := by
  have hφ : Function.Surjective (g.app U.1).hom := Scheme.Hom.app_surjective g U.1 U.2
  have hker : chartIdeal (fZ ≫ g) U =
      Ideal.comap (g.app U.1).hom (chartIdeal fZ ⟨g ⁻¹ᵁ U.1, U.2.preimage g⟩) := rfl
  have hmap : Ideal.map (g.app U.1).hom (chartIdeal (fZ ≫ g) U ^ n) =
      chartIdeal fZ ⟨g ⁻¹ᵁ U.1, U.2.preimage g⟩ ^ n := by
    rw [Ideal.map_pow, hker, Ideal.map_comap_of_surjective _ hφ]
  exact (Ideal.mem_map_iff_of_surjective _ hφ).1 (hmap ▸ hb)

/-- **The canonical morphism of conormal graded algebras `𝒞_{Z/X,*} ⟶ 𝒞_{Z/Y,*}** of a chain of
closed immersions `Z ⟶ Y ⟶ X`, written with the composite `fZ ≫ g` for the outer immersion so
that the conormal charts of the two ends agree by `rfl`. -/
abbrev nestedConormalHom : ConormalAlgebraHom fZ (fZ ≫ g) (𝟙 Z) :=
  (conormalAlgebraHom fZ (fZ ≫ g) (𝟙 Z) g (Category.id_comp _)).hom

/-- **`Stacks.Conormal.nestedConormalHom` is surjective on sections over a conormal chart in
every nonnegative degree.** Every section of `𝒞_{Z/Y,n}` over the chart is the class of an
element of the `n`-th power of the ideal of `Z` in the chart of `Y`; that element lifts to the
`n`-th power of the ideal of `Z` in the chart of `X`, and
`Stacks.Conormal.ConormalAlgebraHom.IsCanonical` says the morphism carries the class of the lift
to the class of the element. -/
theorem surjective_nestedConormalHom_map_nat (U : X.affineOpens) (n : ℕ)
    (hFU : fZ ⁻¹ᵁ (g ⁻¹ᵁ U.1) ≤ (𝟙 Z) ⁻¹ᵁ ((fZ ≫ g) ⁻¹ᵁ U.1)) :
    Function.Surjective ((nestedConormalHom fZ g).map (n : ℤ)
      (fZ ⁻¹ᵁ (g ⁻¹ᵁ U.1)) ((fZ ≫ g) ⁻¹ᵁ U.1) hFU) := by
  intro y
  obtain ⟨b, hb⟩ := (conormalAlgebra fZ).localMap_surjective ⟨g ⁻¹ᵁ U.1, U.2.preimage g⟩
    (isClosedImmersion_resLE_self fZ _) n y
  obtain ⟨a, ha, hab⟩ := exists_mem_chartIdealPow fZ g U n b.1 b.2
  refine ⟨(conormalAlgebra (fZ ≫ g)).localMap U
    (isClosedImmersion_resLE_self (fZ ≫ g) _) n ⟨a, ha⟩, Eq.trans ?_ hb⟩
  refine (conormalAlgebraHom fZ (fZ ≫ g) (𝟙 Z) g (Category.id_comp _)).chart
    ⟨g ⁻¹ᵁ U.1, U.2.preimage g⟩ U le_rfl (isClosedImmersion_resLE_self fZ _)
    (isClosedImmersion_resLE_self (fZ ≫ g) _) hFU n ⟨a, ha⟩ b ?_
  rw [Stacks.RelativeSpec.map_homOfLE_self]
  exact hab.symm

/-- **`Stacks.Conormal.nestedConormalHom` is surjective on sections over a conormal chart in
every degree.** In a negative degree the conormal algebra vanishes, so there is nothing to
check. -/
theorem surjective_nestedConormalHom_map (U : X.affineOpens) (n : ℤ)
    (hFU : fZ ⁻¹ᵁ (g ⁻¹ᵁ U.1) ≤ (𝟙 Z) ⁻¹ᵁ ((fZ ≫ g) ⁻¹ᵁ U.1)) :
    Function.Surjective ((nestedConormalHom fZ g).map n
      (fZ ⁻¹ᵁ (g ⁻¹ᵁ U.1)) ((fZ ≫ g) ⁻¹ᵁ U.1) hFU) := by
  rcases lt_or_ge n 0 with hn | hn
  · have hsub := Stacks.subsingleton_of_isZero
      ((conormalAlgebra fZ).negative_isZero n hn) (op (fZ ⁻¹ᵁ (g ⁻¹ᵁ U.1)))
    exact fun _ => ⟨0, Subsingleton.elim _ _⟩
  · lift n to ℕ using hn
    exact surjective_nestedConormalHom_map_nat fZ g U n hFU

variable [(conormalAlgebraSheaf fZ).IsQuasicoherent]
  [(conormalAlgebraSheaf (fZ ≫ g)).IsQuasicoherent]

/-- **The canonical morphism `C_{Z/Y} ⟶ C_{Z/X}` of a chain of closed immersions is a closed
immersion**, written with the composite `fZ ≫ g` for the outer immersion. The charts
`(fZ ≫ g)⁻¹(U)` for `U` an affine open of `X` cover `Z`, are affine, and
`Stacks.Conormal.surjective_nestedConormalHom_map` is the degreewise surjectivity on them that
`Stacks.Conormal.isClosedImmersion_normalConeMap` asks for. -/
theorem isClosedImmersion_normalConeMapOfSquare_comp :
    IsClosedImmersion
      (normalConeMapOfSquare fZ (fZ ≫ g) (𝟙 Z) g (Category.id_comp _)) :=
  isClosedImmersion_normalConeMap fZ (fZ ≫ g) (𝟙 Z) (nestedConormalHom fZ g)
    (fun U : X.affineOpens => ⟨(fZ ≫ g) ⁻¹ᵁ U.1, (U.2.preimage g).preimage fZ⟩)
    ((fZ ≫ g).iSup_preimage_eq_top (iSup_affineOpens_eq_top X))
    (fun U => (U.2.preimage g).preimage fZ)
    (fun U n => surjective_nestedConormalHom_map fZ g U n _)

end Nested

/-- **The canonical morphism `C_{Z/Y} ⟶ C_{Z/X}` of a chain of closed immersions `Z ⟶ Y ⟶ X` is
a closed immersion.** This is the form the statement is met in: the outer closed immersion is a
morphism `iZ` of its own, factored through `Y` by `comm`.

This is [Stacks, Tag 06AE] passed from the conormal sheaves to the cones: the canonical morphism
of conormal graded algebras is surjective in every degree on the conormal charts
(`Stacks.Conormal.surjective_nestedConormalHom_map`), and the relative spectrum of a surjection
is a closed immersion (`Stacks.RelativeSpec.isClosedImmersion_pairToHom`). -/
theorem isClosedImmersion_normalConeMapOfSquare_of_factorization {Z Y X : Scheme.{u}}
    (fZ : Z ⟶ Y) (g : Y ⟶ X) (iZ : Z ⟶ X) [IsClosedImmersion fZ] [IsClosedImmersion g]
    [IsClosedImmersion iZ] [(conormalAlgebraSheaf fZ).IsQuasicoherent]
    [(conormalAlgebraSheaf iZ).IsQuasicoherent] (comm : 𝟙 Z ≫ iZ = fZ ≫ g) :
    IsClosedImmersion (normalConeMapOfSquare fZ iZ (𝟙 Z) g comm) := by
  obtain rfl : iZ = fZ ≫ g := (Category.id_comp iZ).symm.trans comm
  exact isClosedImmersion_normalConeMapOfSquare_comp fZ g

end Stacks.Conormal

end
