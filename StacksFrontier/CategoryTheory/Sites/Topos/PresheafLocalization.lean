module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import Mathlib.CategoryTheory.Sites.InducedTopology
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Topos.LocalizationOfTopoi

/-!
# Localization of a site at a presheaf of sets

Let `(C, J)` be a site. Stacks 0791 localizes `C` at a *sheaf* `F` of sets: the site `C/F` has as
objects the pairs `(U, s)` with `s ∈ F(U)` — by the Yoneda lemma, `CostructuredArrow yoneda F` —
and a family `{(U_i, s_i) ⟶ (U, s)}` is a covering exactly when `{U_i ⟶ U}` is a covering of `C`.
Nothing in that construction uses the sheaf condition, so it applies verbatim to a *presheaf* `G`,
and this file records the comparison that makes the resulting site the expected one:

if `η : G ⟶ F` is locally injective and locally surjective — the case of interest being
`η = toSheafify J G : G ⟶ G^#` — then the functor `C/G ⥤ C/F` induced by `η` exhibits `C/G` as a
*dense subsite* of `C/F`, hence induces an equivalence `Sh(C/G) ≌ Sh(C/F)`.

Taking `F = G^#` and composing with Stacks 0791 for the sheaf `G^#` gives `Sh(C/G) ≌ Sh(C)/G^#`:
the topos of sheaves on the localization of `C` at the presheaf `G` is the localization of the
topos `Sh(C)` at the sheaf `G^#`. That identification is the content of Stacks 09X6.

## Main results

* `Stacks.Sites.PresheafLocalization.isDenseSubsite`: for `η : G ⟶ F` locally injective and locally
  surjective, `CostructuredArrow.map η : C/G ⥤ C/F` is a dense subsite inclusion for the topologies
  of Stacks 0791 on either side. Its three components are recorded separately as `isCoverDense`,
  `isLocallyFull` and `isLocallyFaithful`.
* `Stacks.Sites.PresheafLocalization.sheafEquiv`: the induced equivalence `Sh(C/G) ≌ Sh(C/F)` on
  sheaves with values in any category with the relevant limits.
* `Stacks.Sites.PresheafLocalization.nonempty_sheafEquiv_over_sheafification`: on a small site,
  `Sh(C/G) ≌ Sh(C)/G^#`, obtained by composing `sheafEquiv` at `η = toSheafify J G` with Stacks
  0791 for the sheaf `G^#`.

## Implementation notes

The covering sieves of `C/G` are the sieves whose image under `j = CostructuredArrow.proj yoneda G`
is covering (`mem_restrictedTopology_iff`); the key point is that `j` is a discrete fibration, so
that `Sieve.functorPushforward j` and `Sieve.functorPullback j` are mutually inverse and commute
with pullback. Those facts hold for an arbitrary presheaf and are established in
`StacksFrontier.CategoryTheory.Sites.Topos.LocalizationOfTopoi`.

`sheafEquiv` carries the limit hypothesis `∀ X, HasLimitsOfShape (StructuredArrow X _) A` required
by `CategoryTheory.Functor.IsDenseSubsite.sheafEquiv` rather than fixing `A = Type v`, which would
force `u ≤ v`. The small-site hypothesis on `nonempty_sheafEquiv_over_sheafification` is what makes
that instance and `HasSheafify J (Type u)` available for sheaves of types.

## References

* [Stacks 09X6](https://stacks.math.columbia.edu/tag/09X6) for the site `C/G` at a presheaf `G`.
* [Stacks 0791](https://stacks.math.columbia.edu/tag/0791) for the site `C/F` at a sheaf `F`.
* [Stacks 09VU](https://stacks.math.columbia.edu/tag/09VU) for hypercoverings of a presheaf.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open CategoryTheory.Stacks.Topos.Localized

namespace Stacks.Sites.PresheafLocalization

universe w w' v u

section Site

variable {C : Type u} [Category.{v} C] (G : Cᵒᵖ ⥤ Type v) (J : GrothendieckTopology C)

/-- **Stacks 09X6**, the covering sieves of the localization of `C` at a presheaf `G`: a sieve of
an object `(U, s)` of `C/G` belongs to `j.restrictedTopology J`, for
`j = CostructuredArrow.proj yoneda G`, exactly when its image under `j` is a covering sieve of
`U`. -/
@[stacks 09X6 "The remark's instruction to define `C/G` for a PRESHEAF of sets `G` exactly as in
  Stacks 0791: the coverings of `C/G` are those coming from coverings of `C`, and the topology they
  generate is already `j.restrictedTopology J`, with no sheaf hypothesis on `G`. Carried: nothing.
  Claimed: this covering characterisation, which is what fixes the topology appearing in
  `nonempty_sheafEquiv_over_sheafification`. Disclaimed: fibre products and equalizers of `C/G`
  (Mathlib's `CostructuredArrow.hasLimitsOfShape_of_isConnected`), the hypercovering
  correspondence, and the `RΓ` transfer statements."]
lemma mem_restrictedTopology_iff (X : CostructuredArrow (yoneda (C := C)) G) (S : Sieve X) :
    S ∈ (CostructuredArrow.proj yoneda G).restrictedTopology J X ↔
      S.functorPushforward (CostructuredArrow.proj yoneda G) ∈ J X.left := by
  rw [restrictedTopology_eq_topology]
  exact mem_topology_iff G J X S

/-- The element of `G` attached to the canonical lift of `g : X ⟶ Y.left`. -/
private lemma yonedaEquiv_lift {X : C} {Y : CostructuredArrow (yoneda (C := C)) G}
    (g : X ⟶ Y.left) :
    yonedaEquiv (yoneda.map g ≫ Y.hom) = G.map g.op (yonedaEquiv Y.hom) :=
  (yonedaEquiv_naturality _ _).symm

/-- A morphism of `C` underlies a morphism of `C/G` exactly when it carries the element of `G`
attached to the target to the one attached to the source. -/
private lemma hom_condition_iff {X Y : CostructuredArrow (yoneda (C := C)) G}
    (g : X.left ⟶ Y.left) :
    yoneda.map g ≫ Y.hom = X.hom ↔
      G.map g.op (yonedaEquiv Y.hom) = yonedaEquiv X.hom := by
  rw [← yonedaEquiv_lift, yonedaEquiv.apply_eq_iff_eq]

end Site

section Comparison

variable {C : Type u} [Category.{v} C] {G F : Cᵒᵖ ⥤ Type v} (J : GrothendieckTopology C)
  (η : G ⟶ F)

/-- The projection of `C/G` to `C` factors the projection of `C/F` through
`CostructuredArrow.map η`. -/
private lemma map_comp_proj :
    CostructuredArrow.map (S := yoneda (C := C)) η ⋙
        CostructuredArrow.proj (yoneda (C := C)) F =
      CostructuredArrow.proj (yoneda (C := C)) G :=
  rfl

/-- Morphisms of `C/F` are determined by their underlying morphism of `C`, so `C/G ⥤ C/F` is
faithful. -/
instance instFaithful : (CostructuredArrow.map (S := yoneda (C := C)) η).Faithful where
  map_injective {_ _} f₁ f₂ h := by
    ext
    exact congrArg (·.left) h

/-- The element of `F` attached to the image in `C/F` of an object of `C/G`. -/
private lemma yonedaEquiv_map_obj (X : CostructuredArrow (yoneda (C := C)) G) :
    yonedaEquiv ((CostructuredArrow.map η).obj X).hom =
      η.app (op X.left) (yonedaEquiv X.hom) :=
  yonedaEquiv_comp _ _

/-- Pushing a sieve of `C/G` forward to `C` along `j` is the same as pushing it to `C/F` and then
to `C`. -/
private lemma functorPushforward_map_proj {X : CostructuredArrow (yoneda (C := C)) G}
    (S : Sieve X) :
    (S.functorPushforward (CostructuredArrow.map η)).functorPushforward
        (CostructuredArrow.proj (yoneda (C := C)) F) =
      S.functorPushforward (CostructuredArrow.proj (yoneda (C := C)) G) := by
  rw [← Sieve.functorPushforward_comp]
  rfl

/-- Membership in the topology of `C/F` of a sieve pushed forward from `C/G`, read on `C`. -/
private lemma mem_restrictedTopology_functorPushforward_map_iff
    {X : CostructuredArrow (yoneda (C := C)) G} (S : Sieve X) :
    S.functorPushforward (CostructuredArrow.map η) ∈
        (CostructuredArrow.proj yoneda F).restrictedTopology J
          ((CostructuredArrow.map η).obj X) ↔
      S.functorPushforward (CostructuredArrow.proj (yoneda (C := C)) G) ∈ J X.left := by
  rw [mem_restrictedTopology_iff, functorPushforward_map_proj]
  exact Iff.rfl

variable [Presheaf.IsLocallySurjective J η]

/-- **`C/G ⥤ C/F` is cover dense**: every object of `C/F` is covered by objects in the image of
`CostructuredArrow.map η`. -/
instance isCoverDense :
    (CostructuredArrow.map η).IsCoverDense
      ((CostructuredArrow.proj yoneda F).restrictedTopology J) where
  is_cover Y := by
    rw [mem_restrictedTopology_iff]
    refine J.superset_covering ?_ (Presheaf.imageSieve_mem J η (yonedaEquiv Y.hom))
    rintro W f ⟨r, hr⟩
    have hz : yonedaEquiv (((CostructuredArrow.map (S := yoneda (C := C)) η).obj
        (CostructuredArrow.mk (yonedaEquiv.symm r))).hom) = η.app (op W) r :=
      (yonedaEquiv_comp (yonedaEquiv.symm r) η).trans (by rw [Equiv.apply_symm_apply])
    exact (mem_functorPushforward_proj_iff F
      (Sieve.coverByImage (CostructuredArrow.map (S := yoneda (C := C)) η) Y)
      (CostructuredArrow.homMk
        (f := (CostructuredArrow.map (S := yoneda (C := C)) η).obj
          (CostructuredArrow.mk (yonedaEquiv.symm r))) (f' := Y) f
        ((hom_condition_iff F (X := (CostructuredArrow.map (S := yoneda (C := C)) η).obj
          (CostructuredArrow.mk (yonedaEquiv.symm r))) (Y := Y) f).2
          (hz.trans hr).symm))).2
      (Presieve.in_coverByImage _ _)

variable [Presheaf.IsLocallyInjective J η]

/-- **`C/G ⥤ C/F` is locally full**: a morphism of `C/F` between objects coming from `C/G` lies, on
a covering of its source, in the image of `CostructuredArrow.map η`. -/
instance isLocallyFull :
    (CostructuredArrow.map η).IsLocallyFull
      ((CostructuredArrow.proj yoneda F).restrictedTopology J) where
  functorPushforward_imageSieve_mem {U V} f := by
    rw [mem_restrictedTopology_functorPushforward_map_iff]
    have h := (hom_condition_iff F f.left).1 (CostructuredArrow.w f)
    rw [yonedaEquiv_map_obj, yonedaEquiv_map_obj] at h
    have key : η.app (op U.left) (G.map f.left.op (yonedaEquiv V.hom)) =
        η.app (op U.left) (yonedaEquiv U.hom) :=
      (NatTrans.naturality_apply η f.left.op _).trans h
    refine J.superset_covering ?_ (Presheaf.equalizerSieve_mem J η _ _ key)
    intro W k (hk : G.map k.op (G.map f.left.op (yonedaEquiv V.hom)) =
      G.map k.op (yonedaEquiv U.hom))
    have hcond : G.map (k ≫ f.left).op (yonedaEquiv V.hom) =
        yonedaEquiv (yoneda.map k ≫ U.hom) := by
      rw [op_comp, Functor.map_comp_apply, yonedaEquiv_lift]
      exact hk
    refine (mem_functorPushforward_proj_iff G _ (liftHom G U k)).2
      ⟨CostructuredArrow.homMk
        (f := (CostructuredArrow.mk (yoneda.map k ≫ U.hom) :
          CostructuredArrow (yoneda (C := C)) G)) (f' := V) (k ≫ f.left)
        ((hom_condition_iff G (X := (CostructuredArrow.mk (yoneda.map k ≫ U.hom) :
          CostructuredArrow (yoneda (C := C)) G)) (Y := V) (k ≫ f.left)).2 hcond), ?_⟩
    ext
    simp

/-- **`C/G ⥤ C/F` is locally faithful**: two morphisms of `C/G` with the same image in `C/F` agree
on a covering of their source. -/
instance isLocallyFaithful :
    (CostructuredArrow.map η).IsLocallyFaithful
      ((CostructuredArrow.proj yoneda F).restrictedTopology J) where
  functorPushforward_equalizer_mem f₁ f₂ e := by
    obtain rfl := (CostructuredArrow.map (S := yoneda (C := C)) η).map_injective e
    simp

/-- **`C/G` is a dense subsite of `C/F`** when `η : G ⟶ F` is locally injective and locally
surjective, for the topologies of Stacks 0791 on either side. -/
instance isDenseSubsite :
    (CostructuredArrow.map η).IsDenseSubsite
      ((CostructuredArrow.proj yoneda G).restrictedTopology J)
      ((CostructuredArrow.proj yoneda F).restrictedTopology J) where
  functorPushforward_mem_iff {X S} := by
    rw [mem_restrictedTopology_functorPushforward_map_iff, mem_restrictedTopology_iff]

/-- **The topos of sheaves on the localization of `C` at a presheaf of sets depends on the presheaf
only up to local bijection.** For `η : G ⟶ F` locally injective and locally surjective, the
equivalence `Sh(C/G) ≌ Sh(C/F)` of categories of `A`-valued sheaves induced by the dense subsite
inclusion `C/G ⥤ C/F`. -/
def sheafEquiv (A : Type w) [Category.{w'} A]
    [∀ X : (CostructuredArrow (yoneda (C := C)) F)ᵒᵖ,
      HasLimitsOfShape (StructuredArrow X (CostructuredArrow.map η).op) A] :
    Sheaf ((CostructuredArrow.proj yoneda G).restrictedTopology J) A ≌
      Sheaf ((CostructuredArrow.proj yoneda F).restrictedTopology J) A :=
  Functor.IsDenseSubsite.sheafEquiv _ _ (CostructuredArrow.map η) A

end Comparison

section Sheafification

variable {C : Type u} [Category.{u} C] (G : Cᵒᵖ ⥤ Type u) (J : GrothendieckTopology C)

/-- **Stacks 09X6**, the parenthetical claim: on a small site, the topos of sheaves on the
localization of `C` at a presheaf of sets `G` is the localization of the topos `Sh(C)` at the sheaf
`G^#`, that is, `Sh(C/G)` is equivalent to the slice category `Sh(C)/G^#`. -/
@[stacks 09X6 "The parenthetical claim of the remark: the site `C/G` of pairs `(U, s)` with
  `s ∈ G(U)` for a PRESHEAF of sets `G`, with the coverings of `C`, satisfies
  `Sh(C/G) = Sh(C)/G^#`. Carried: Stacks 0791 (`Presheaf.IsSheaf.exists_sheafEquivalence_\
  costructuredArrow_yoneda`) for the SHEAF `G^#`, supplying the right-hand equivalence.
  Claimed: the equivalence of categories, for a small site. Disclaimed: the rest of the remark —
  that `C/G` is a site with fibre products and equalizers (Mathlib's
  `CostructuredArrow.hasLimitsOfShape_of_isConnected`), that hypercoverings of `G` (Stacks 09VU)
  correspond to hypercoverings of `C/G`, and every `RΓ` transfer statement.",
  sga "3 IV 4.5.4" "more general",
  sga "4 III 5.4" "partial"]
theorem nonempty_sheafEquiv_over_sheafification :
    Nonempty (Sheaf ((CostructuredArrow.proj yoneda G).restrictedTopology J) (Type u) ≌
      Over ((presheafToSheaf J (Type u)).obj G)) := by
  obtain ⟨-, -, _, _, E, -⟩ :=
    ((presheafToSheaf J (Type u)).obj G).property.exists_sheafEquivalence_costructuredArrow_yoneda
  exact ⟨(sheafEquiv J (toSheafify J G) (Type u)).trans E⟩

end Sheafification

end Stacks.Sites.PresheafLocalization

end
