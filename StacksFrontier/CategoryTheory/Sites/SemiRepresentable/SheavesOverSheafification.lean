module

public import Mathlib.CategoryTheory.LocallyCartesianClosed.Over
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverRepresentable
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.Sheaves
public import StacksCore.Tactic.StacksAttribute

/-!
# Sheaves on the site of a semi-representable object as sheaves over its associated sheaf

Let `(C, J)` be a site and `K = ⨿ i, K.obj i` a semi-representable object of `C`, so that
`Sh(C / K)` is the product `∏ i, Sh(C / K.obj i)` of the sheaf categories of the component
slices. Stacks 0D87 part (1) asserts that the lower shriek functor `j_!` is an equivalence
`Sh(C / K) ≌ Sh(C) / F(K)^♯`, where `F(K) = ∐ i, h_{K.obj i}` is the presheaf represented by `K`.

The functor is built componentwise: `j_!` on the component `i` is the one-object lower shriek
functor `CategoryTheory.OverShriek.sheafFunctorToOver` of Stacks 00Y1, landing in
`Sh(C) / h_{K.obj i}^♯`, and the resulting family is assembled into a single object over
`F(K)^♯` by taking the coproduct. Both steps are equivalences: the first because Stacks 00Y1 is,
componentwise, and the second because the coproduct of sheaves defining `F(K)^♯` is a van Kampen
colimit, so that assembling a family over its summands is the quasi-inverse of pulling back
along its injections.

## Main definitions

* `CategoryTheory.SemiRepresentable.formalCoproductSheafification`: the associated sheaf
  `F(K)^♯` of the presheaf represented by `K`, with
  `CategoryTheory.SemiRepresentable.formalCoproductSheafificationι` its injections.
* `CategoryTheory.SemiRepresentable.sheafCoproductToOver`: a family of sheaves over the
  sheafified components, assembled into one sheaf over `F(K)^♯`.
* `CategoryTheory.SemiRepresentable.sheafFunctorToOver`: the lower shriek functor
  `Sh(C / K) ⥤ Sh(C) / F(K)^♯`, equipped with its structural map.
* `CategoryTheory.SemiRepresentable.componentwiseRestriction`: the restriction functor
  `j^{-1} : Sh(C) ⥤ Sh(C / K)`, componentwise `GrothendieckTopology.overPullback`.

## Main results

* `CategoryTheory.SemiRepresentable.isVanKampenColimit_sheafComponentCocone`: the sheafified
  component injections exhibit `F(K)^♯` as a van Kampen coproduct.
* `CategoryTheory.SemiRepresentable.isEquivalence_sheafCoproductToOver`: assembling is an
  equivalence `∏ i, Sh(C) / h_{K.obj i}^♯ ≌ Sh(C) / F(K)^♯`.
* `CategoryTheory.SemiRepresentable.isEquivalence_sheafFunctorToOver` and
  `CategoryTheory.SemiRepresentable.sheafEquivalence`: **Stacks 0D87 part (1)**.
* `CategoryTheory.SemiRepresentable.sheafFunctorToOverForgetAdjunction`: the sheaf level `j_!`,
  forgetting its structural map, is left adjoint to componentwise restriction.
* `CategoryTheory.SemiRepresentable.componentwiseRestrictionCompSheafFunctorToOverIso` and
  `CategoryTheory.SemiRepresentable.componentwiseRestriction_comp_sheafEquivalence_iso_toOver`:
  **Stacks 0D87 part (2)**.

## Implementation notes

The coefficient universe here is the morphism universe `v` of `C`, which is where the
one-component statement Stacks 00Y1 is available and where `FormalCoproduct.yoneda` takes its
values. Sheafification need not exist there, and need not be left exact when it does, so the
statements carry the hypotheses they use: `HasWeakSheafify` for the constructions, and
`HasSheafify` together with `GrothendieckTopology.WEqualsLocallyBijective` for the equivalence.
The second of those is what Stacks 00Y1 runs on and is *not* implied by either sheafification
hypothesis at an independent coefficient universe; at the enlarged universe `Type (max u v)`,
where sheafification is the plus construction, both are instances.

## References

* [Stacks Project, Tag 0D87](https://stacks.math.columbia.edu/tag/0D87)
* [Stacks Project, Tag 00Y1](https://stacks.math.columbia.edu/tag/00Y1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SemiRepresentable

universe u v

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C) [HasWeakSheafify J (Type v)] (K : FormalCoproduct.{v} C)

/-- Sheaves on the localization of `C` at the semi-representable object `K = ⨿ i, K.obj i`,
presented as the product of the sheaf categories of the component slices. -/
abbrev SheafOverFormalCoproduct := (i : K.I) → Sheaf (J.over (K.obj i)) (Type v)

/-- The associated sheaf `F(K)^♯` of the presheaf `F(K) = ∐ i, h_{K.obj i}` represented by a
formal coproduct `K`. -/
noncomputable abbrev formalCoproductSheafification : Sheaf J (Type v) :=
  (presheafToSheaf J (Type v)).obj ((FormalCoproduct.yoneda (C := C)).obj K)

/-- The canonical injection of a sheafified component into the sheafified formal coproduct. -/
noncomputable def formalCoproductSheafificationι (i : K.I) :
    (presheafToSheaf J (Type v)).obj (yoneda.obj (K.obj i)) ⟶
      formalCoproductSheafification J K :=
  (presheafToSheaf J (Type v)).map
    (Limits.Sigma.ι (fun i : K.I => yoneda.obj (K.obj i)) i)

/-- Assemble a family of sheaves over the sheafified components by taking its coproduct, with
structural map induced by the sheafified coproduct injections. -/
noncomputable def sheafCoproductToOver :
    ((i : K.I) → Over ((presheafToSheaf J (Type v)).obj (yoneda.obj (K.obj i)))) ⥤
      Over (formalCoproductSheafification J K) where
  obj F := Over.mk (Limits.Sigma.desc fun i => (F i).hom ≫ formalCoproductSheafificationι J K i)
  map f := Over.homMk (Limits.Sigma.map fun i => (f i).left) (by
    apply Limits.Sigma.hom_ext
    intro i
    simp)
  map_id _ := Over.OverMorphism.ext Limits.Sigma.map_id
  map_comp f g := by
    apply Over.OverMorphism.ext
    apply Limits.Sigma.hom_ext
    intro i
    simp

/-- The cocone on the sheafified components whose apex is `F(K)^♯` and whose injections are the
sheafified coproduct injections. -/
noncomputable def sheafComponentCocone :
    Cocone (Discrete.functor fun i : K.I =>
      (presheafToSheaf J (Type v)).obj (yoneda.obj (K.obj i))) where
  pt := formalCoproductSheafification J K
  ι := Discrete.natTrans fun i => formalCoproductSheafificationι J K i.as

/-- `F(K)^♯` is the coproduct of the sheafified components: sheafification is a left adjoint, so
it carries the coproduct defining `F(K)` to a coproduct. -/
noncomputable def isColimitSheafComponentCocone : IsColimit (sheafComponentCocone J K) := by
  let H₀ : K.I → Cᵒᵖ ⥤ Type v := fun i => yoneda.obj (K.obj i)
  let Psh := presheafToSheaf J (Type v)
  let c := Limits.Sigma.cocone (Discrete.functor H₀)
  have hc : IsColimit (Psh.mapCocone c) := isColimitOfPreserves Psh (coproductIsCoproduct' _)
  let e : (Discrete.functor fun i : K.I => Psh.obj (H₀ i)) ≅ Discrete.functor H₀ ⋙ Psh :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro i j f
      obtain rfl := Discrete.ext (Discrete.eq_of_hom f)
      simp)
  refine IsColimit.ofIsoColimit ((IsColimit.precomposeHomEquiv e (Psh.mapCocone c)).symm hc)
    (Cocone.ext (Iso.refl _) ?_)
  intro i
  simp only [sheafComponentCocone, formalCoproductSheafificationι, e, c, Psh, H₀,
    Discrete.natTrans_app, Iso.refl_hom]
  exact Category.comp_id _

section

variable [HasSheafify J (Type v)]

/-- The sheafified component injections exhibit `F(K)^♯` as a **van Kampen** coproduct. This is
the arbitrary-index statement: Mathlib's `CategoryTheory.FinitaryExtensive` covers only finite
coproducts, while `K.I` is an arbitrary type. -/
theorem isVanKampenColimit_sheafComponentCocone :
    IsVanKampenColimit (sheafComponentCocone J K) := by
  let H : K.I → Sheaf J (Type v) :=
    fun i => (presheafToSheaf J (Type v)).obj (yoneda.obj (K.obj i))
  have hd := isColimitSheafComponentCocone J K
  exact (isVanKampenColimit_sheafCoproduct J H).of_iso
    (Cocone.ext ((coproductIsCoproduct' (Discrete.functor H)).coconePointUniqueUpToIso hd)
      (IsColimit.comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct' (Discrete.functor H)) hd))

/-- Assembling a family of sheaves over the sheafified components is the general assembling
functor of a van Kampen coproduct, for the cocone `sheafComponentCocone`. -/
noncomputable def assembleOverSheafComponentCoconeIso :
    assembleOver (sheafComponentCocone J K) ≅ sheafCoproductToOver J K := by
  refine NatIso.ofComponents (fun _ => Iso.refl _) ?_
  intro F G f
  apply Over.OverMorphism.ext
  simp only [Over.comp_left]
  apply Limits.Sigma.hom_ext
  intro i
  simp [assembleOver, sheafCoproductToOver]

/-- **Assembling the components is an equivalence** `∏ i, Sh(C) / h_{K.obj i}^♯ ≌ Sh(C)/F(K)^♯`.
This is the sentence *"hence `Sh(C)/F(K)^♯` is the product of the categories
`Sh(C)/h_{U_i}^♯`"* of the proof of Stacks 0D87, and it is where van Kampen descent for an
arbitrary index type is used. -/
theorem isEquivalence_sheafCoproductToOver : (sheafCoproductToOver J K).IsEquivalence :=
  @Functor.isEquivalence_of_iso _ _ _ _ _ _ (assembleOverSheafComponentCoconeIso J K)
    (isEquivalence_assembleOver (sheafComponentCocone J K)
      (isVanKampenColimit_sheafComponentCocone J K))

end

/-- The lower shriek functor from sheaves on the localization at `K` to sheaves on `C`, together
with its canonical structural map to `F(K)^♯`. On the component indexed by `i` this is the
one-object lower shriek functor for `C / K.obj i`. -/
noncomputable def sheafFunctorToOver :
    SheafOverFormalCoproduct J K ⥤ Over (formalCoproductSheafification J K) :=
  Functor.pi (fun i => CategoryTheory.OverShriek.sheafFunctorToOver (U := K.obj i) J) ⋙
    sheafCoproductToOver J K

section

variable [HasSheafify J (Type v)] [J.WEqualsLocallyBijective (Type v)]

/-- **Stacks 0D87 part (1).** The lower shriek functor `j_!` identifies sheaves on the
localization of `C` at a semi-representable object `K` with sheaves over the associated sheaf
`F(K)^♯`.

Following the source: `Sh(C / K)` is the product of the `Sh(C / K.obj i)` — which is how
`SheafOverFormalCoproduct` presents it — and `Sh(C)/F(K)^♯` is the product of the
`Sh(C)/h_{K.obj i}^♯` by `isEquivalence_sheafCoproductToOver`, so the statement follows from
Stacks 00Y1 for each component. -/
@[stacks 0D87 "(1): the functor j_! is an equivalence Sh(C/K) to Sh(C)/F(K)^sharp",
  sga "4 III 5.4" "special case"]
theorem isEquivalence_sheafFunctorToOver : (sheafFunctorToOver J K).IsEquivalence := by
  have := isEquivalence_sheafCoproductToOver J K
  exact inferInstanceAs (Functor.IsEquivalence (_ ⋙ _))

/-- **Stacks 0D87 part (1)**, as an equivalence of categories
`Sh(C / K) ≌ Sh(C) / F(K)^♯`. Its functor is `sheafFunctorToOver`, the sheaf level `j_!` viewed
as a functor into the slice (`sheafEquivalence_functor`). -/
@[stacks 0D87 "(1): the resulting equivalence of categories Sh(C/K) to Sh(C)/F(K)^sharp"]
noncomputable def sheafEquivalence :
    SheafOverFormalCoproduct J K ≌ Over (formalCoproductSheafification J K) := by
  have := isEquivalence_sheafFunctorToOver J K
  exact (sheafFunctorToOver J K).asEquivalence

/-- The functor of `sheafEquivalence` is the lower shriek functor. -/
theorem sheafEquivalence_functor :
    (sheafEquivalence J K).functor = sheafFunctorToOver J K := rfl

end

/-! ### Stacks 0D87 part (2): restriction is "product with `F(K)^♯`"

Restriction `j^{-1} : Sh(C) ⥤ Sh(C / K)` is, in the componentwise presentation, the product of
the one-object restriction functors `GrothendieckTopology.overPullback`; this is
`componentwiseRestriction`. Part (2) says that under the identification of part (1) it becomes
`F ↦ (F × F(K)^♯ ⟶ F(K)^♯)`, which is Mathlib's `CategoryTheory.toOver (F(K)^♯)`.

Both functors are *right adjoints*: `toOver A` of `Over.forget A` (Mathlib's `forgetAdjToOver`),
and `j^{-1}` transported along the equivalence of part (1) of `Over.forget A` as well, because
`j_! ⋙ Over.forget A` is left adjoint to `j^{-1}`. So part (2) is uniqueness of right adjoints,
exactly as part (1) was Stacks 00Y1 componentwise; this is the semi-representable form of the
argument the source gives for the one-object case, Stacks 03EE.

The adjunction `j_! ⋙ Over.forget A ⊣ j^{-1}` is assembled from the component adjunctions
`j_{i!} ⊣ j_i^{-1}` of Stacks 00XS by
`Hom(∐ᵢ j_{i!}Fᵢ, G) = ∏ᵢ Hom(j_{i!}Fᵢ, G) = ∏ᵢ Hom(Fᵢ, G|_{K.obj i})`,
the first bijection being the universal property of the coproduct. -/

/-- The sheaf level lower shriek `j_{i!} : Sh(C / K.obj i) ⥤ Sh(C)` on the component indexed by
`i`, i.e. the one-object functor of Stacks 00Y1 with its structural map to `h_{K.obj i}^♯`
forgotten. -/
noncomputable abbrev componentShriek (i : K.I) :
    Sheaf (J.over (K.obj i)) (Type v) ⥤ Sheaf J (Type v) :=
  CategoryTheory.OverShriek.sheafFunctorToOver (U := K.obj i) J ⋙
    Over.forget ((presheafToSheaf J (Type v)).obj (yoneda.obj (K.obj i)))

/-- **Stacks 00XS on the component indexed by `i`**: `j_{i!} ⊣ j_i^{-1}`.

This is the composite of the presheaf level adjunction of Stacks 03CD with sheafification,
restricted along the inclusion of sheaves on `C / K.obj i` into presheaves; writing it this way
needs no sheafification hypothesis on the localized site `C / K.obj i`. -/
noncomputable def componentShriekAdjunction (i : K.I) :
    componentShriek J K i ⊣ J.overPullback (Type v) (K.obj i) :=
  ((CategoryTheory.OverShriek.presheafAdjunction (U := K.obj i)).comp
      (sheafificationAdjunction J (Type v))).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf (J.over (K.obj i)) (Type v))
    (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

/-- Restriction `j^{-1} : Sh(C) ⥤ Sh(C / K)` of a sheaf on `C` to each localized site
`C / K.obj i`, i.e. the inverse-image functor for the localization at the semi-representable
object `K`, in the componentwise presentation of `SheafOverFormalCoproduct`. -/
def componentwiseRestriction : Sheaf J (Type v) ⥤ SheafOverFormalCoproduct J K :=
  Functor.pi' (fun i => J.overPullback (Type v) (K.obj i))

/-- Assembling a family of sheaves on the component slices by taking the coproduct of their lower
shrieks: `F ↦ ∐ i, j_{i!}(F i)`. This is `sheafFunctorToOver` followed by `Over.forget`, written
so that its value on `F` *is* the coproduct (`componentShriekSigmaIso`).

This is deliberately an `abbrev` rather than a `def`: a goal mentioning both this spelling and
`sheafFunctorToOver J K ⋙ Over.forget (formalCoproductSheafification J K)` is type-correct only
if the two carriers are interchangeable at `reducible` transparency, and with a plain `def` they
are not — `rw` and `simp` then silently refuse to fire on the adjunction's naturality squares. -/
noncomputable abbrev componentShriekSigma :
    SheafOverFormalCoproduct J K ⥤ Sheaf J (Type v) :=
  { obj := fun F => ∐ fun i => (componentShriek J K i).obj (F i)
    map := fun f => Limits.Sigma.map fun i => (componentShriek J K i).map (f i)
    map_id := fun _ => by
      apply Limits.Sigma.hom_ext
      intro i
      simp
    map_comp := fun _ _ => by
      apply Limits.Sigma.hom_ext
      intro i
      simp }

/-- The hom-set bijection `Hom(∐ i, j_{i!}(F i), G) ≃ Hom(F, j^{-1}G)` of
`componentShriekSigmaAdjunction`: the universal property of the coproduct followed by the
component adjunctions. -/
noncomputable def componentShriekSigmaHomEquiv (F : SheafOverFormalCoproduct J K)
    (G : Sheaf J (Type v)) :
    ((componentShriekSigma J K).obj F ⟶ G) ≃ (F ⟶ (componentwiseRestriction J K).obj G) where
  toFun f i := (componentShriekAdjunction J K i).homEquiv (F i) G
    (Limits.Sigma.ι (fun j => (componentShriek J K j).obj (F j)) i ≫ f)
  invFun f := Limits.Sigma.desc
    (fun i => ((componentShriekAdjunction J K i).homEquiv (F i) G).symm (f i))
  left_inv _ := by
    apply Limits.Sigma.hom_ext
    intro i
    simp
  right_inv _ := by
    funext i
    simp only [Limits.Sigma.ι_desc]
    exact Equiv.apply_symm_apply _ _

/-- `componentShriekSigmaHomEquiv` evaluated at a component. -/
@[simp]
lemma componentShriekSigmaHomEquiv_apply (F : SheafOverFormalCoproduct J K)
    (G : Sheaf J (Type v)) (f : (componentShriekSigma J K).obj F ⟶ G) (i : K.I) :
    componentShriekSigmaHomEquiv J K F G f i =
      (componentShriekAdjunction J K i).homEquiv (F i) G
        (Limits.Sigma.ι (fun j => (componentShriek J K j).obj (F j)) i ≫ f) := rfl

/-- The inverse of `componentShriekSigmaHomEquiv` is the map out of the coproduct. -/
@[simp]
lemma componentShriekSigmaHomEquiv_symm_apply (F : SheafOverFormalCoproduct J K)
    (G : Sheaf J (Type v)) (f : F ⟶ (componentwiseRestriction J K).obj G) :
    (componentShriekSigmaHomEquiv J K F G).symm f =
      Limits.Sigma.desc
        (fun i => ((componentShriekAdjunction J K i).homEquiv (F i) G).symm (f i)) := rfl

/-- **Assembling the componentwise lower shrieks is left adjoint to componentwise restriction.**
Both naturality squares reduce, component by component, to the corresponding square of
`componentShriekAdjunction`. -/
noncomputable def componentShriekSigmaAdjunction :
    componentShriekSigma J K ⊣ componentwiseRestriction J K :=
  Adjunction.mkOfHomEquiv
    { homEquiv := componentShriekSigmaHomEquiv J K
      homEquiv_naturality_left_symm := by
        intro F' F G f g
        apply Limits.Sigma.hom_ext
        intro i
        rw [componentShriekSigmaHomEquiv_symm_apply, componentShriekSigmaHomEquiv_symm_apply]
        simp only [Limits.Sigma.ι_desc, Limits.Sigma.ι_map_assoc, Pi.comp_apply]
        exact (componentShriekAdjunction J K i).homEquiv_naturality_left_symm (f i) (g i)
      homEquiv_naturality_right := by
        intro F G G' f g
        funext i
        rw [Pi.comp_apply, componentShriekSigmaHomEquiv_apply,
          componentShriekSigmaHomEquiv_apply]
        simp only [componentwiseRestriction, Functor.pi'_map]
        exact (componentShriekAdjunction J K i).homEquiv_naturality_right
          (Limits.Sigma.ι (fun j => (componentShriek J K j).obj (F j)) i ≫ f) g }

/-- Forgetting its structural map, `j_!` is the coproduct of the componentwise lower shrieks. The
two functors agree on objects and on morphisms, so the isomorphism is the identity. -/
noncomputable def componentShriekSigmaIso :
    componentShriekSigma J K ≅
      sheafFunctorToOver J K ⋙ Over.forget (formalCoproductSheafification J K) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro _ _ _
    simp only [Iso.refl_hom]
    rfl)

/-- **Stacks 00XS for the semi-representable object `K`**: the sheaf level `j_!`, with its
structural map to `F(K)^♯` forgotten, is left adjoint to componentwise restriction `j^{-1}`. -/
@[sga "4 III 1.7" "special case"]
noncomputable def sheafFunctorToOverForgetAdjunction :
    sheafFunctorToOver J K ⋙ Over.forget (formalCoproductSheafification J K) ⊣
      componentwiseRestriction J K :=
  (componentShriekSigmaAdjunction J K).ofNatIsoLeft (componentShriekSigmaIso J K)

section

variable [HasSheafify J (Type v)] [J.WEqualsLocallyBijective (Type v)]

/-- **Stacks 0D87 part (2).** Under the identification of part (1), restriction
`j^{-1} : Sh(C) ⥤ Sh(C / K)` is `F ↦ (F × F(K)^♯ ⟶ F(K)^♯)`, i.e. Mathlib's
`CategoryTheory.toOver (F(K)^♯)`.

Following the source: `toOver A` is right adjoint to `Over.forget A`, and so is
`j^{-1} ⋙ j_!` read in the slice, because `j_! ⋙ Over.forget A ⊣ j^{-1}`
(`sheafFunctorToOverForgetAdjunction`) and `j_!` is an equivalence by part (1). Uniqueness of
right adjoints identifies them. -/
@[stacks 0D87 "(2): j^{-1} corresponds to F maps to (F times F(K)^sharp over F(K)^sharp)"]
noncomputable def componentwiseRestrictionCompSheafFunctorToOverIso :
    componentwiseRestriction J K ⋙ sheafFunctorToOver J K ≅
      toOver (formalCoproductSheafification J K) :=
  Adjunction.rightAdjointUniq
    ((((sheafEquivalence J K).symm.toAdjunction.comp
        (sheafFunctorToOverForgetAdjunction J K)).ofNatIsoLeft
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (sheafEquivalence J K).counitIso _ ≪≫
        Functor.leftUnitor _)))
    (forgetAdjToOver _)

/-- **Stacks 0D87 part (2)**, stated through the equivalence of categories of part (1): under
`sheafEquivalence`, componentwise restriction corresponds to `toOver (F(K)^♯)`. -/
@[stacks 0D87 "(2): under the equivalence of (1), j^{-1} is toOver of F(K)^sharp"]
theorem componentwiseRestriction_comp_sheafEquivalence_iso_toOver :
    Nonempty (componentwiseRestriction J K ⋙ (sheafEquivalence J K).functor ≅
      toOver (formalCoproductSheafification J K)) :=
  ⟨componentwiseRestrictionCompSheafFunctorToOverIso J K⟩

end

end CategoryTheory.SemiRepresentable

end
