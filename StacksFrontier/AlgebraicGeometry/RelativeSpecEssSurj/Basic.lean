module

public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.Equivalence
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.Over
public import StacksFrontier.CategoryTheory.IsIsoOfEqIsoHom
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Essential surjectivity of the pushforward functor, and the anti-equivalence

Let `S` be a scheme and let `A` be a quasi-coherent sheaf of commutative `𝒪_S`-algebras. The
relative spectrum `relativeSpec A`, affine over `S` through `relativeSpecToBase A`, satisfies
`(relativeSpecToBase A)_* 𝒪 ≅ A` as sheaves of `𝒪_S`-algebras. Hence the fully faithful functor
`X ↦ f_* 𝒪_X` of `AffineAlgebraEquivalence2` is essentially surjective, and therefore is the
anti-equivalence between the schemes affine over `S` and the quasi-coherent `𝒪_S`-algebras.

## Main definitions

* `sectionsIso` is the isomorphism `Γ(relativeSpec A, relativeSpecToBase A ⁻¹ᵁ U) ≅ A(U)` for an
  affine open `U` of `S`.
* `pushforwardSheafIso` assembles those isomorphisms into an isomorphism of sheaves of rings, and
  `pushforwardAlgebraIso` upgrades it to an isomorphism of algebra sheaves
  `(relativeSpecToBase A)_* 𝒪 ≅ A`.
* `affineQuasicoherentEquivalence` is the resulting anti-equivalence, and
  `pushforwardIsoOfEquivalence` identifies its functor with pushforward of structure sheaves.

## Main results

* `essSurj_affineQuasicoherentPushforwardFunctor`: the functor `X ↦ f_* 𝒪_X` from the schemes
  affine over `S` to the quasi-coherent `𝒪_S`-algebras is essentially surjective.
* `pushforwardIsoOfEquivalence_naturality`: that identification is natural, the anti-equivalence
  acting on a morphism over `S` by the canonical contravariant map on pushed-forward structure
  sheaves.

## Implementation notes

For an affine open `U` of `S`, the preimage `relativeSpecToBase A ⁻¹ᵁ U` is the range of the open
immersion `Spec A(U) ⟶ relativeSpec A` given by the colimit inclusion
(`toBase_preimage_eq_opensRange`), so the sections of the structure sheaf of `relativeSpec A` over
that preimage are the global sections of `Spec A(U)`: this is `isIso_ι_appLE`, deduced from
`AlgebraicGeometry.Scheme.Hom.isIso_app` and the fact that the colimit inclusion pulls the
preimage back to the whole of `Spec A(U)`. Composing with `AlgebraicGeometry.Scheme.ΓSpecIso`
gives `sectionsIso`.

Naturality in `U` splits into a part that only concerns the gluing datum,
`ι_appLE_naturality` — proved from `AlgebraicGeometry.Scheme.Hom.map_appLE`,
`AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE` and the colimit relation
`CategoryTheory.Limits.colimit.w` — and one application of
`AlgebraicGeometry.Scheme.ΓSpecIso_naturality`. Since the affine opens form a basis,
`TopCat.Sheaf.restrictHomEquivHom` extends the resulting family to a morphism of sheaves of rings
and `TopCat.Sheaf.isIso_iff_isIso_basis` shows it is an isomorphism.

Compatibility with the structure morphisms is checked on the same basis. Over an affine open `U`
it reduces, by `toBase_app_comp_ι_appLE`, to the statement
`ιTopIso_comp_specMap_isoSpec_inv_appTop` about a single affine open, which is in turn
`AlgebraicGeometry.IsAffineOpen.isoSpec_inv_appTop` together with the identification
`ιTopIso_comp_topIso_hom` of `ιTopIso` with the inverse of
`AlgebraicGeometry.Scheme.Opens.topIso`.

Throughout, an affine open of `S` is bound at the type `S.directedAffineCover.I₀`, which is only
definitionally `S.affineOpens`, and converted with the `coverOpen` abbreviation: instance search
does not cross that identification, so neither the open-immersion instance for the colimit
inclusions nor the affineness of the fibres is available for an `S.affineOpens`-typed index.

## References

* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.AffineAlgebraEquivalence

/-! ### Generalities -/

/-- An isomorphism of presheaves of rings between two mutually nested opens: the restriction
maps along `U ≤ V` and `V ≤ U` are mutually inverse. -/
public theorem isIso_map_homOfLE {X : Scheme.{u}} {U V : X.Opens} (h : U ≤ V) (h' : V ≤ U) :
    IsIso (X.presheaf.map (homOfLE h).op) :=
  ⟨⟨X.presheaf.map (homOfLE h').op,
    Stacks.RelativeSpec.map_homOfLE_comp_self X.presheaf h' h,
    Stacks.RelativeSpec.map_homOfLE_comp_self X.presheaf h h'⟩⟩

/-- The canonical map from the sections over an open to the global sections of the corresponding
open subscheme is inverse to `AlgebraicGeometry.Scheme.Opens.topIso`. -/
public theorem ιTopIso_comp_topIso_hom {X : Scheme.{u}} (U : X.Opens) :
    ιTopIso U ≫ U.topIso.hom = 𝟙 Γ(X, U) := by
  have h : ∀ f : op U ⟶ op U, X.presheaf.map f = 𝟙 Γ(X, U) := fun f ↦ by
    rw [Subsingleton.elim f (𝟙 (op U)), X.presheaf.map_id]
  simp only [Scheme.Opens.ι_appLE, homOfLE_leOfHom, Scheme.Opens.topIso_hom]
  exact Eq.trans (X.presheaf.map_comp _ _).symm (h _)

/-- The composite of `ιTopIso U` with `AlgebraicGeometry.Scheme.Opens.topIso`, in the form in
which it is cancelled from a longer composite. -/
public theorem ιTopIso_comp_topIso_hom_comp {X : Scheme.{u}} (U : X.Opens)
    {P : CommRingCat.{u}} (g : Γ(X, U) ⟶ P) : ιTopIso U ≫ U.topIso.hom ≫ g = g := by
  rw [← Category.assoc, ιTopIso_comp_topIso_hom, Category.id_comp]

/-- For an affine open `U` of `X` and a ring map `φ : Γ(X, U) ⟶ R`, the morphism of schemes
`Spec R ⟶ U.toScheme` attached to `φ` induces `φ` back on sections over `U`. -/
public theorem ιTopIso_comp_specMap_isoSpec_inv_appTop {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) {R : CommRingCat.{u}} (φ : Γ(X, U) ⟶ R) :
    ιTopIso U ≫ (Spec.map φ ≫ hU.isoSpec.inv).appTop ≫ (Scheme.ΓSpecIso R).hom = φ := by
  rw [show (Spec.map φ ≫ hU.isoSpec.inv).appTop
      = hU.isoSpec.inv.appTop ≫ (Spec.map φ).appTop from rfl]
  simp only [Category.assoc]
  rw [Scheme.ΓSpecIso_naturality, IsAffineOpen.isoSpec_inv_appTop]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_assoc, ιTopIso_comp_topIso_hom_comp]

/-! ### Sections of a relative gluing datum over the preimage of an affine open -/

section

variable {S : Scheme.{u}} (d : Scheme.Cover.RelativeGluingData S.directedAffineCover)

/-- The affine opens of `S`, indexed by the directed affine cover, form a basis. -/
public theorem isBasis_coverOpen :
    Opens.IsBasis (Set.range (fun U : S.directedAffineCover.I₀ ↦ (coverOpen U : S.Opens))) := by
  convert S.isBasis_affineOpens using 2
  exact Subtype.range_coe

/-- The preimage of an affine open of the base under the structure morphism of a relative gluing
datum is the range of the corresponding colimit inclusion. -/
public theorem toBase_preimage_eq_opensRange (U : S.directedAffineCover.I₀) :
    d.toBase ⁻¹ᵁ (coverOpen U : S.Opens) = (colimit.ι d.functor U).opensRange := by
  have h2 : (S.directedAffineCover.f U).opensRange = (coverOpen U : S.Opens) :=
    Scheme.Opens.opensRange_ι _
  have h := d.toBase_preimage_eq_opensRange_ι U
  rwa [h2] at h

/-- The colimit inclusion of the fibre over an affine open `U` of the base pulls the preimage of
`U` back to the whole fibre. -/
public theorem le_ι_preimage (U : S.directedAffineCover.I₀) :
    (⊤ : (d.functor.obj U).Opens) ≤
      colimit.ι d.functor U ⁻¹ᵁ (d.toBase ⁻¹ᵁ (coverOpen U : S.Opens)) := by
  rw [toBase_preimage_eq_opensRange, Scheme.Hom.preimage_opensRange]

/-- The sections of the glued scheme over the preimage of an affine open `U` of the base are the
global sections of the fibre over `U`. -/
public theorem isIso_ι_appLE (U : S.directedAffineCover.I₀) :
    IsIso ((colimit.ι d.functor U).appLE (d.toBase ⁻¹ᵁ (coverOpen U : S.Opens)) ⊤
      (le_ι_preimage d U)) := by
  have h1 : IsIso ((colimit.ι d.functor U).app (d.toBase ⁻¹ᵁ (coverOpen U : S.Opens))) :=
    Scheme.Hom.isIso_app _ _ (toBase_preimage_eq_opensRange d U).le
  have h2 : IsIso ((d.functor.obj U).presheaf.map (homOfLE (le_ι_preimage d U)).op) :=
    isIso_map_homOfLE _ le_top
  exact IsIso.comp_isIso

/-- The structure morphism of a relative gluing datum, read on sections over an affine open `U`
of the base and then restricted to the fibre over `U`, is the component of the natural
transformation of the datum, transported along `ιTopIso`. -/
@[reassoc]
public theorem toBase_app_comp_ι_appLE (U : S.directedAffineCover.I₀) :
    d.toBase.app (coverOpen U : S.Opens) ≫ (colimit.ι d.functor U).appLE
          (d.toBase ⁻¹ᵁ (coverOpen U : S.Opens)) ⊤ (le_ι_preimage d U)
      = ιTopIso (coverOpen U : S.Opens) ≫ (d.natTrans.app U).appTop := by
  have e₂ : (⊤ : (d.functor.obj U).Opens) ≤ d.natTrans.app U ⁻¹ᵁ ⊤ :=
    (Scheme.Hom.preimage_top _).symm.le
  calc d.toBase.app (coverOpen U : S.Opens) ≫ (colimit.ι d.functor U).appLE
          (d.toBase ⁻¹ᵁ (coverOpen U : S.Opens)) ⊤ (le_ι_preimage d U)
      = (colimit.ι d.functor U ≫ d.toBase).appLE (coverOpen U : S.Opens) ⊤
          (le_ι_preimage d U) := (Scheme.Hom.comp_appLE _ _ _ _ _).symm
    _ = (d.natTrans.app U ≫ (coverOpen U : S.Opens).ι).appLE (coverOpen U : S.Opens) ⊤
          (le_preimage_of_comp_ι _) := appLE_congr_hom (d.ι_toBase U) _ _
    _ = ιTopIso (coverOpen U : S.Opens) ≫ (d.natTrans.app U).appLE ⊤ ⊤ e₂ :=
          (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    _ = ιTopIso (coverOpen U : S.Opens) ≫ (d.natTrans.app U).appTop := by
          rw [appLE_top_top]

/-- The identifications of the sections of the glued scheme over the preimages of the affine
opens of the base with the global sections of the fibres are natural. -/
@[reassoc]
public theorem ι_appLE_naturality {U V : S.directedAffineCover.I₀} (h : U ⟶ V) :
    d.glued.presheaf.map ((Opens.map d.toBase.base).map
          (homOfLE (leOfHom h) : (coverOpen U : S.Opens) ⟶ (coverOpen V : S.Opens))).op ≫
        (colimit.ι d.functor U).appLE (d.toBase ⁻¹ᵁ (coverOpen U : S.Opens)) ⊤
          (le_ι_preimage d U)
      = (colimit.ι d.functor V).appLE (d.toBase ⁻¹ᵁ (coverOpen V : S.Opens)) ⊤
            (le_ι_preimage d V) ≫ (d.functor.map h).appTop := by
  have e₂ : (⊤ : (d.functor.obj U).Opens) ≤ d.functor.map h ⁻¹ᵁ ⊤ :=
    (Scheme.Hom.preimage_top _).symm.le
  rw [Scheme.Hom.map_appLE, ← appLE_top_top (d.functor.map h) e₂,
    Scheme.Hom.appLE_comp_appLE]
  exact appLE_congr_hom (colimit.w d.functor h).symm _ _

end

/-! ### The identification of the pushed-forward structure sheaf with the algebra -/

section

variable {S : Scheme.{u}} (A : Stacks.RelativeSpec.AlgebraSheaf S)
  [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent A]

/-- The isomorphism `Γ(relativeSpec A, relativeSpecToBase A ⁻¹ᵁ U) ≅ A(U)` for an affine open `U`
of the base. -/
public noncomputable def sectionsIso (U : S.directedAffineCover.I₀) :
    Γ((relativeSpecGluingData A).glued,
        (relativeSpecGluingData A).toBase ⁻¹ᵁ (coverOpen U : S.Opens)) ≅
      A.right.obj.obj (op (coverOpen U : S.Opens)) :=
  letI := isIso_ι_appLE (relativeSpecGluingData A) U
  asIso ((colimit.ι (relativeSpecGluingData A).functor U).appLE
      ((relativeSpecGluingData A).toBase ⁻¹ᵁ (coverOpen U : S.Opens)) ⊤
      (le_ι_preimage (relativeSpecGluingData A) U)) ≪≫
    Scheme.ΓSpecIso (A.right.obj.obj (op (coverOpen U : S.Opens)))

/-- The forward map of `sectionsIso`. -/
public theorem sectionsIso_hom (U : S.directedAffineCover.I₀) :
    (sectionsIso A U).hom =
      (colimit.ι (relativeSpecGluingData A).functor U).appLE
          ((relativeSpecGluingData A).toBase ⁻¹ᵁ (coverOpen U : S.Opens)) ⊤
          (le_ι_preimage (relativeSpecGluingData A) U) ≫
        (Scheme.ΓSpecIso (A.right.obj.obj (op (coverOpen U : S.Opens)))).hom :=
  rfl

/-- The isomorphisms `sectionsIso` are natural in the affine open. -/
public theorem sectionsIso_naturality {U V : S.directedAffineCover.I₀} (h : U ⟶ V) :
    ((TopCat.Presheaf.pushforward CommRingCat (relativeSpecGluingData A).toBase.base).obj
        (relativeSpecGluingData A).glued.presheaf).map
          (homOfLE (leOfHom h) : (coverOpen U : S.Opens) ⟶ (coverOpen V : S.Opens)).op ≫
        (sectionsIso A U).hom
      = (sectionsIso A V).hom ≫ secRes A h :=
  have hmap : ((relativeSpecGluingData A).functor.map h).appTop ≫
        (Scheme.ΓSpecIso (A.right.obj.obj (op (coverOpen U : S.Opens)))).hom
      = (Scheme.ΓSpecIso (A.right.obj.obj (op (coverOpen V : S.Opens)))).hom ≫ secRes A h :=
    Scheme.ΓSpecIso_naturality (secRes A h)
  Eq.trans
    (ι_appLE_naturality_assoc (relativeSpecGluingData A) h
      (Scheme.ΓSpecIso (A.right.obj.obj (op (coverOpen U : S.Opens)))).hom)
    (Eq.trans (whisker_eq _ hmap) (Category.assoc _ _ _).symm)

/-- Over an affine open `U` of the base, `sectionsIso` carries the structure morphism of the
relative spectrum to the structure morphism of the algebra. -/
public theorem structureMap_comp_sectionsIso (U : S.directedAffineCover.I₀) :
    (relativeSpecGluingData A).toBase.app (coverOpen U : S.Opens) ≫ (sectionsIso A U).hom
      = A.hom.hom.app (op (coverOpen U : S.Opens)) :=
  Eq.trans
    (toBase_app_comp_ι_appLE_assoc (relativeSpecGluingData A) U
      (Scheme.ΓSpecIso (A.right.obj.obj (op (coverOpen U : S.Opens)))).hom)
    (ιTopIso_comp_specMap_isoSpec_inv_appTop (coverOpen U).2
      (A.hom.hom.app (op (coverOpen U : S.Opens))))

/-- The pushforward to the base of the structure sheaf of the relative spectrum. -/
public noncomputable abbrev relativeSpecPushforward : TopCat.Sheaf CommRingCat.{u} S :=
  (TopCat.Sheaf.pushforward CommRingCat (relativeSpecGluingData A).toBase.base).obj
    (relativeSpecGluingData A).glued.sheaf

/-- The morphism of presheaves of rings from the pushed-forward structure sheaf of the relative
spectrum to the algebra, extending the isomorphisms `sectionsIso` from the basis of affine
opens. -/
public noncomputable def pushforwardSheafHom :
    (relativeSpecPushforward A).obj ⟶ A.right.obj :=
  TopCat.Sheaf.restrictHomEquivHom (relativeSpecPushforward A).obj A.right isBasis_coverOpen
    { app := fun U ↦ (sectionsIso A U.unop).hom
      naturality := fun _ _ φ ↦ sectionsIso_naturality A (homOfLE (leOfHom φ.unop.hom)) }

/-- Over an affine open of the base, `pushforwardSheafHom` is `sectionsIso`. -/
public theorem pushforwardSheafHom_app (U : S.directedAffineCover.I₀) :
    (pushforwardSheafHom A).app (op (coverOpen U : S.Opens)) = (sectionsIso A U).hom :=
  TopCat.Sheaf.extend_hom_app _ _ _ _ U

/-- The isomorphism of sheaves of rings `(relativeSpecToBase A)_* 𝒪 ≅ A`. -/
public noncomputable def pushforwardSheafIso : relativeSpecPushforward A ≅ A.right :=
  haveI : IsIso (⟨pushforwardSheafHom A⟩ : relativeSpecPushforward A ⟶ A.right) :=
    TopCat.Sheaf.isIso_iff_isIso_basis isBasis_coverOpen
      fun U ↦ CategoryTheory.isIso_of_eq_iso_hom (sectionsIso A U) (pushforwardSheafHom_app A U)
  asIso (⟨pushforwardSheafHom A⟩ : relativeSpecPushforward A ⟶ A.right)

/-- Over an affine open of the base, `pushforwardSheafIso` is `sectionsIso`. -/
public theorem pushforwardSheafIso_hom_app (U : S.directedAffineCover.I₀) :
    (pushforwardSheafIso A).hom.hom.app (op (coverOpen U : S.Opens)) = (sectionsIso A U).hom :=
  pushforwardSheafHom_app A U

/-- The isomorphism `pushforwardSheafIso` is compatible with the structure morphisms. -/
public theorem structureMap_comp_pushforwardSheafIso :
    (pushforwardAlgebra (relativeSpecGluingData A).toBase).hom ≫ (pushforwardSheafIso A).hom
      = A.hom := by
  apply CategoryTheory.Sheaf.hom_ext
  refine TopCat.Sheaf.hom_ext S.presheaf A.right isBasis_coverOpen fun U ↦ ?_
  exact Eq.trans
    (congrArg (fun k ↦ (relativeSpecGluingData A).toBase.app (coverOpen U : S.Opens) ≫ k)
      (pushforwardSheafIso_hom_app A U))
    (structureMap_comp_sectionsIso A U)

/-- **Stacks Project, Tag 01LX(3).** The isomorphism of sheaves of `𝒪_S`-algebras
`(relativeSpecToBase A)_* 𝒪 ≅ A`. Its inverse is the universal map
`A ⟶ (relativeSpecToBase A)_* 𝒪` of the relative spectrum, so this says that the universal map
is an isomorphism; it is also the essential surjectivity of the pushforward functor. -/
@[stacks 01LX "universal_map_iso", sga "3 I 4.2" "A ≅ π_*O_Spec(A)"]
public noncomputable def pushforwardAlgebraIso : pushforwardAlgebra (relativeSpecToBase A) ≅ A :=
  Under.isoMk (pushforwardSheafIso A) (structureMap_comp_pushforwardSheafIso A)

end

/-! ### The anti-equivalence -/

/-- The functor `X ↦ f_* 𝒪_X` from the schemes affine over `S` to the quasi-coherent
`𝒪_S`-algebras is essentially surjective: the preimage of `A` is the relative spectrum of `A`. -/
public instance essSurj_affineQuasicoherentPushforwardFunctor (S : Scheme.{u}) :
    (affineQuasicoherentPushforwardFunctor S).EssSurj where
  mem_essImage A :=
    letI := A.property
    ⟨op (relativeSpecAffineOver A.obj),
      ⟨(IsQuasicoherentAlgebra S).ι.preimageIso (pushforwardAlgebraIso A.obj)⟩⟩

/-- The anti-equivalence between the schemes affine over `S` and the quasi-coherent
`𝒪_S`-algebras. -/
@[sga "3 I 4.2"]
public noncomputable def affineQuasicoherentEquivalence (S : Scheme.{u}) :
    (AffineOver S)ᵒᵖ ≌ QuasicoherentAlgebra S :=
  equivalenceOfEssSurj S

/-- Under the anti-equivalence, an object `X` affine over `S` corresponds to `f_* 𝒪_X`. -/
public noncomputable def pushforwardIsoOfEquivalence (S : Scheme.{u}) (X : AffineOver S) :
    (IsQuasicoherentAlgebra S).ι.obj ((affineQuasicoherentEquivalence S).functor.obj (.op X)) ≅
      pushforwardAlgebra X.obj.hom :=
  Iso.refl _

/-- The identification of the anti-equivalence with pushforward of structure sheaves is natural:
the anti-equivalence acts on a morphism over `S` by the canonical contravariant map on
pushed-forward structure sheaves. -/
public theorem pushforwardIsoOfEquivalence_naturality (S : Scheme.{u}) {X Y : AffineOver S}
    (f : X ⟶ Y) :
    (IsQuasicoherentAlgebra S).ι.map ((affineQuasicoherentEquivalence S).functor.map f.op) ≫
        (pushforwardIsoOfEquivalence S X).hom
      = (pushforwardIsoOfEquivalence S Y).hom ≫
        pushforwardAlgebraMap ((IsAffineHomOver S).ι.map f) :=
  Eq.trans (Category.comp_id _)
    (Eq.trans (pushforwardIso_rfl_naturality S f) (Category.id_comp _).symm)

end Stacks.AffineAlgebraEquivalence

end
