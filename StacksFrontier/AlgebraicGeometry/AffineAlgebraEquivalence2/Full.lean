module

public import Mathlib.AlgebraicGeometry.Gluing
public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.AffineOpenHom
public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.Over

/-!
# Fullness of the pushforward functor on schemes affine over a base

Let `S` be a scheme and let `Y` be a scheme affine over `S`. Every morphism
`Y.hom_* 𝒪_Y ⟶ X.hom_* 𝒪_X` of sheaves of `𝒪_S`-algebras comes from a morphism `X ⟶ Y` of
schemes over `S`.

## Main definitions

* `localHom` is the morphism `X.hom ⁻¹ᵁ V ⟶ Y` attached to an algebra map over an affine open
  `V` of the base.

## Main results

* `localHom_comp_hom`, `homOfLE_comp_localHom` and `localHom_comp_eq`: the local morphisms are
  morphisms over the base, are compatible with shrinking the affine open of the base, and agree
  on overlaps.

## References

* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.AffineAlgebraEquivalence

/-! ### The canonical isomorphisms and restriction -/

/-- The canonical isomorphisms `Γ(X, W) ≅ Γ(W.toScheme, ⊤)` are compatible with restriction to
a smaller open. -/
public theorem ιTopIso_comp_homOfLE_appTop {X : Scheme.{u}} {W W' : X.Opens} (h : W' ≤ W) :
    ιTopIso W ≫ (X.homOfLE h).appTop =
      X.presheaf.map (homOfLE h).op ≫ ιTopIso W' := by
  have e₂ : (⊤ : (W'.toScheme).Opens) ≤ X.homOfLE h ⁻¹ᵁ ⊤ := le_top
  have h₁ : ιTopIso W ≫ (X.homOfLE h).appTop
      = (X.homOfLE h ≫ W.ι).appLE W ⊤ (le_preimage_of_comp_ι _) := by
    rw [← appLE_top_top (X.homOfLE h) e₂]
    exact Scheme.Hom.appLE_comp_appLE (X.homOfLE h) W.ι W ⊤ ⊤ W.ι_preimage_self.ge e₂
  rw [h₁, appLE_congr_hom (X.homOfLE_ι h) (le_preimage_of_comp_ι _)
    (W'.ι_preimage_self.ge.trans (W'.ι.preimage_mono h))]
  exact (Scheme.Hom.map_appLE W'.ι W'.ι_preimage_self.ge (homOfLE h).op).symm

/-! ### The local morphisms attached to an algebra map -/

section

variable {S : Scheme.{u}} {X Y : Over S}
  (ψ : pushforwardAlgebra Y.hom ⟶ pushforwardAlgebra X.hom)

/-- The component over an open `V` of the base of a morphism of pushed-forward structure
sheaves: a ring map `Γ(Y, Y.hom ⁻¹ᵁ V) ⟶ Γ(X, X.hom ⁻¹ᵁ V)`. -/
public noncomputable abbrev algHomApp (V : S.Opens) :
    Γ(Y.left, Y.hom ⁻¹ᵁ V) ⟶ Γ(X.left, X.hom ⁻¹ᵁ V) :=
  ψ.right.hom.app (op V)

/-- The components of a morphism of pushed-forward structure sheaves are compatible with the
structure morphisms. -/
public theorem algHomApp_w (V : S.Opens) :
    Y.hom.app V ≫ algHomApp ψ V = X.hom.app V :=
  congrArg (fun α ↦ α.hom.app (op V)) (Under.w ψ)

/-- The components of a morphism of pushed-forward structure sheaves are compatible with
restriction along an inclusion of opens of the base. -/
public theorem algHomApp_naturality {V V' : S.Opens} (h : V' ≤ V) :
    Y.left.presheaf.map (homOfLE (Y.hom.preimage_mono h)).op ≫ algHomApp ψ V' =
      algHomApp ψ V ≫ X.left.presheaf.map (homOfLE (X.hom.preimage_mono h)).op :=
  ψ.right.hom.naturality (homOfLE h).op

variable [IsAffineHom Y.hom]

/-- The morphism `X.hom ⁻¹ᵁ V ⟶ Y` over `V` attached to a morphism of pushed-forward structure
sheaves and an affine open `V` of the base. -/
public noncomputable def localHom {V : S.Opens} (hV : IsAffineOpen V) :
    (X.hom ⁻¹ᵁ V).toScheme ⟶ Y.left :=
  homOfAppLE (hV.preimage Y.hom) (X.hom ⁻¹ᵁ V).toScheme
    (algHomApp ψ V ≫ ιTopIso (X.hom ⁻¹ᵁ V))

/-- The local morphism attached to an affine open `V` of the base lands in `Y.hom ⁻¹ᵁ V`. -/
public theorem localHom_le_preimage {V : S.Opens} (hV : IsAffineOpen V) :
    (⊤ : ((X.hom ⁻¹ᵁ V).toScheme).Opens) ≤ localHom ψ hV ⁻¹ᵁ (Y.hom ⁻¹ᵁ V) :=
  homOfAppLE_le_preimage _ _ _

/-- The sections over `Y.hom ⁻¹ᵁ V` of the local morphism attached to `V`. -/
public theorem localHom_appLE {V : S.Opens} (hV : IsAffineOpen V) :
    (localHom ψ hV).appLE (Y.hom ⁻¹ᵁ V) ⊤ (localHom_le_preimage ψ hV) =
      algHomApp ψ V ≫ ιTopIso (X.hom ⁻¹ᵁ V) :=
  homOfAppLE_appLE _ _ _

/-- The local morphism attached to an affine open `V` of the base is a morphism over `S`. -/
public theorem localHom_comp_hom {V : S.Opens} (hV : IsAffineOpen V) :
    localHom ψ hV ≫ Y.hom = (X.hom ⁻¹ᵁ V).ι ≫ X.hom := by
  have h₁ : (⊤ : ((X.hom ⁻¹ᵁ V).toScheme).Opens) ≤ (localHom ψ hV ≫ Y.hom) ⁻¹ᵁ V := by
    rw [Scheme.Hom.comp_preimage]; exact localHom_le_preimage ψ hV
  have h₂ : (⊤ : ((X.hom ⁻¹ᵁ V).toScheme).Opens) ≤ ((X.hom ⁻¹ᵁ V).ι ≫ X.hom) ⁻¹ᵁ V := by
    rw [Scheme.Hom.comp_preimage, (X.hom ⁻¹ᵁ V).ι_preimage_self]
  refine eq_of_appLE_eq hV h₁ h₂ ?_
  have e₁ : (localHom ψ hV ≫ Y.hom).appLE V ⊤ h₁
      = Y.hom.appLE V (Y.hom ⁻¹ᵁ V) le_rfl ≫
        (localHom ψ hV).appLE (Y.hom ⁻¹ᵁ V) ⊤ (localHom_le_preimage ψ hV) :=
    (Scheme.Hom.appLE_comp_appLE _ Y.hom V (Y.hom ⁻¹ᵁ V) ⊤ le_rfl _).symm
  have e₂ : ((X.hom ⁻¹ᵁ V).ι ≫ X.hom).appLE V ⊤ h₂
      = X.hom.appLE V (X.hom ⁻¹ᵁ V) le_rfl ≫ ιTopIso (X.hom ⁻¹ᵁ V) :=
    (Scheme.Hom.appLE_comp_appLE _ X.hom V (X.hom ⁻¹ᵁ V) ⊤ le_rfl _).symm
  rw [e₁, e₂, localHom_appLE, Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_eq_app,
    ← Category.assoc, algHomApp_w ψ V]

/-- The local morphisms attached to affine opens of the base are compatible with shrinking the
affine open. -/
public theorem homOfLE_comp_localHom {V V' : S.Opens} (hV : IsAffineOpen V)
    (hV' : IsAffineOpen V') (h : V' ≤ V) :
    X.left.homOfLE (X.hom.preimage_mono h) ≫ localHom ψ hV = localHom ψ hV' := by
  have hU : Y.hom ⁻¹ᵁ V' ≤ Y.hom ⁻¹ᵁ V := Y.hom.preimage_mono h
  have h₁ : (⊤ : ((X.hom ⁻¹ᵁ V').toScheme).Opens) ≤
      (X.left.homOfLE (X.hom.preimage_mono h) ≫ localHom ψ hV) ⁻¹ᵁ (Y.hom ⁻¹ᵁ V) := by
    rw [Scheme.Hom.comp_preimage,
      ← Scheme.Hom.preimage_top (X.left.homOfLE (X.hom.preimage_mono h))]
    exact (X.left.homOfLE (X.hom.preimage_mono h)).preimage_mono (localHom_le_preimage ψ hV)
  refine eq_of_appLE_eq (hV.preimage Y.hom) h₁
    ((localHom_le_preimage ψ hV').trans ((localHom ψ hV').preimage_mono hU)) ?_
  have e₂ : (⊤ : ((X.hom ⁻¹ᵁ V').toScheme).Opens) ≤
      X.left.homOfLE (X.hom.preimage_mono h) ⁻¹ᵁ ⊤ := le_top
  have e₁ : (X.left.homOfLE (X.hom.preimage_mono h) ≫ localHom ψ hV).appLE
        (Y.hom ⁻¹ᵁ V) ⊤ h₁
      = (localHom ψ hV).appLE (Y.hom ⁻¹ᵁ V) ⊤ (localHom_le_preimage ψ hV) ≫
        (X.left.homOfLE (X.hom.preimage_mono h)).appTop := by
    rw [← appLE_top_top _ e₂]
    exact (Scheme.Hom.appLE_comp_appLE _ (localHom ψ hV) (Y.hom ⁻¹ᵁ V) ⊤ ⊤ _ e₂).symm
  have e₃ : Y.left.presheaf.map (homOfLE hU).op ≫
        (localHom ψ hV').appLE (Y.hom ⁻¹ᵁ V') ⊤ (localHom_le_preimage ψ hV')
      = (localHom ψ hV').appLE (Y.hom ⁻¹ᵁ V) ⊤
        ((localHom_le_preimage ψ hV').trans ((localHom ψ hV').preimage_mono hU)) :=
    Scheme.Hom.map_appLE _ (localHom_le_preimage ψ hV') (homOfLE hU).op
  rw [e₁, ← e₃, localHom_appLE, localHom_appLE, Category.assoc,
    ιTopIso_comp_homOfLE_appTop (X.hom.preimage_mono h), ← Category.assoc,
    ← Category.assoc, algHomApp_naturality ψ h]

/-! ### Agreement of the local morphisms on overlaps -/

/-- Over a smaller affine open `W` of the base, a morphism factoring through `X.hom ⁻¹ᵁ V`
composed with the local morphism attached to `V` is the local morphism attached to `W`. -/
public theorem resLE_comp_localHom {Z : Scheme.{u}} {V W : S.Opens} (hV : IsAffineOpen V)
    (hW : IsAffineOpen W) (hWV : W ≤ V) (p : Z ⟶ X.left)
    (q : Z ⟶ (X.hom ⁻¹ᵁ V).toScheme) (hq : q ≫ (X.hom ⁻¹ᵁ V).ι = p) :
    (p ⁻¹ᵁ (X.hom ⁻¹ᵁ W)).ι ≫ q ≫ localHom ψ hV =
      p.resLE (X.hom ⁻¹ᵁ W) (p ⁻¹ᵁ (X.hom ⁻¹ᵁ W)) le_rfl ≫ localHom ψ hW := by
  have hr : p.resLE (X.hom ⁻¹ᵁ W) (p ⁻¹ᵁ (X.hom ⁻¹ᵁ W)) le_rfl ≫ (X.hom ⁻¹ᵁ W).ι =
      (p ⁻¹ᵁ (X.hom ⁻¹ᵁ W)).ι ≫ p := Scheme.Hom.resLE_comp_ι p le_rfl
  have hrq : p.resLE (X.hom ⁻¹ᵁ W) (p ⁻¹ᵁ (X.hom ⁻¹ᵁ W)) le_rfl ≫
      X.left.homOfLE (X.hom.preimage_mono hWV) = (p ⁻¹ᵁ (X.hom ⁻¹ᵁ W)).ι ≫ q := by
    rw [← cancel_mono (X.hom ⁻¹ᵁ V).ι]
    simp only [Category.assoc, X.left.homOfLE_ι, hr, hq]
  rw [← Category.assoc, ← hrq, Category.assoc, homOfLE_comp_localHom ψ hV hW hWV]

/-- The local morphisms attached to two affine opens of the base agree on the overlap of their
preimages. -/
public theorem localHom_comp_eq {Z : Scheme.{u}} {V V' : S.Opens} (hV : IsAffineOpen V)
    (hV' : IsAffineOpen V') {q : Z ⟶ (X.hom ⁻¹ᵁ V).toScheme}
    {q' : Z ⟶ (X.hom ⁻¹ᵁ V').toScheme}
    (hq : q ≫ (X.hom ⁻¹ᵁ V).ι = q' ≫ (X.hom ⁻¹ᵁ V').ι) :
    q ≫ localHom ψ hV = q' ≫ localHom ψ hV' := by
  refine Scheme.hom_ext_of_forall _ _ fun z ↦ ?_
  have hz1 : (q ≫ (X.hom ⁻¹ᵁ V).ι).base z ∈ X.hom ⁻¹ᵁ V :=
    le_preimage_of_comp_ι q (show z ∈ (⊤ : Z.Opens) from trivial)
  have hz2 : (q ≫ (X.hom ⁻¹ᵁ V).ι).base z ∈ X.hom ⁻¹ᵁ V' := by
    rw [hq]
    exact le_preimage_of_comp_ι q' (show z ∈ (⊤ : Z.Opens) from trivial)
  obtain ⟨W, hW, hzW, hWle⟩ := Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens
    (show X.hom.base ((q ≫ (X.hom ⁻¹ᵁ V).ι).base z) ∈ V ⊓ V' from ⟨hz1, hz2⟩)
  refine ⟨(q ≫ (X.hom ⁻¹ᵁ V).ι) ⁻¹ᵁ (X.hom ⁻¹ᵁ W), hzW, ?_⟩
  rw [resLE_comp_localHom ψ hV hW (hWle.trans inf_le_left) _ q rfl]
  exact (resLE_comp_localHom ψ hV' hW (hWle.trans inf_le_right) _ q' hq.symm).symm

/-- The preimages of the affine opens of the base cover the source. -/
public theorem isOpenCover_preimage_affineOpens (X : Over S) :
    IsOpenCover fun V : S.affineOpens ↦ X.hom ⁻¹ᵁ (V : S.Opens) :=
  X.hom.iSup_preimage_eq_top (iSup_affineOpens_eq_top S)

/-! ### Gluing the local morphisms -/

/-- The open cover of the source of an object over `S` by the preimages of the affine opens of
`S`. -/
public noncomputable def affinePreimageCover (X : Over S) : X.left.OpenCover :=
  Scheme.openCoverOfIsOpenCover X.left _
    (X.hom.iSup_preimage_eq_top (iSup_affineOpens_eq_top S))

/-- The morphism `X ⟶ Y` obtained by gluing the local morphisms attached to a morphism of
pushed-forward structure sheaves. -/
public noncomputable def gluedHom : X.left ⟶ Y.left :=
  (affinePreimageCover X).glueMorphisms (fun V ↦ localHom ψ V.2)
    fun _ _ ↦ localHom_comp_eq ψ _ _ Limits.pullback.condition

/-- The restriction of the glued morphism to the preimage of an affine open `V` of the base is
the local morphism attached to `V`. -/
@[simp]
public theorem ι_comp_gluedHom (V : S.affineOpens) :
    (X.hom ⁻¹ᵁ (V : S.Opens)).ι ≫ gluedHom ψ = localHom ψ V.2 :=
  (affinePreimageCover X).ι_glueMorphisms _ _ V

/-- The glued morphism is a morphism over `S`. -/
public theorem gluedHom_comp_hom : gluedHom ψ ≫ Y.hom = X.hom := by
  refine (affinePreimageCover X).hom_ext _ _ fun (V : S.affineOpens) ↦ ?_
  show (X.hom ⁻¹ᵁ (V : S.Opens)).ι ≫ gluedHom ψ ≫ Y.hom
    = (X.hom ⁻¹ᵁ (V : S.Opens)).ι ≫ X.hom
  rw [← Category.assoc, ι_comp_gluedHom]
  exact localHom_comp_hom ψ V.2

/-- The morphism of schemes over `S` attached to a morphism of pushed-forward structure
sheaves. -/
public noncomputable def overHomOfAlgebraHom : X ⟶ Y :=
  Over.homMk (gluedHom ψ) (gluedHom_comp_hom ψ)

/-- The sections over an affine open `V` of the base of the glued morphism are the component of
the given algebra map at `V`. -/
public theorem gluedHom_appLE {V : S.Opens} (hV : IsAffineOpen V) :
    (gluedHom ψ).appLE (Y.hom ⁻¹ᵁ V) (X.hom ⁻¹ᵁ V)
        (preimage_le_preimage_preimage (overHomOfAlgebraHom ψ) V) = algHomApp ψ V := by
  have hle : (⊤ : ((X.hom ⁻¹ᵁ V).toScheme).Opens) ≤
      ((X.hom ⁻¹ᵁ V).ι ≫ gluedHom ψ) ⁻¹ᵁ (Y.hom ⁻¹ᵁ V) := by
    rw [Scheme.Hom.comp_preimage, ← (X.hom ⁻¹ᵁ V).ι_preimage_self]
    exact (X.hom ⁻¹ᵁ V).ι.preimage_mono
      (preimage_le_preimage_preimage (overHomOfAlgebraHom ψ) V)
  have key : (gluedHom ψ).appLE (Y.hom ⁻¹ᵁ V) (X.hom ⁻¹ᵁ V)
        (preimage_le_preimage_preimage (overHomOfAlgebraHom ψ) V) ≫ ιTopIso (X.hom ⁻¹ᵁ V)
      = algHomApp ψ V ≫ ιTopIso (X.hom ⁻¹ᵁ V) :=
    calc (gluedHom ψ).appLE (Y.hom ⁻¹ᵁ V) (X.hom ⁻¹ᵁ V)
          (preimage_le_preimage_preimage (overHomOfAlgebraHom ψ) V) ≫ ιTopIso (X.hom ⁻¹ᵁ V)
        = ((X.hom ⁻¹ᵁ V).ι ≫ gluedHom ψ).appLE (Y.hom ⁻¹ᵁ V) ⊤ hle :=
          Scheme.Hom.appLE_comp_appLE (X.hom ⁻¹ᵁ V).ι (gluedHom ψ) (Y.hom ⁻¹ᵁ V)
            (X.hom ⁻¹ᵁ V) ⊤ _ (X.hom ⁻¹ᵁ V).ι_preimage_self.ge
      _ = (localHom ψ hV).appLE (Y.hom ⁻¹ᵁ V) ⊤ (localHom_le_preimage ψ hV) :=
          appLE_congr_hom (ι_comp_gluedHom ψ ⟨V, hV⟩) hle (localHom_le_preimage ψ hV)
      _ = algHomApp ψ V ≫ ιTopIso (X.hom ⁻¹ᵁ V) := localHom_appLE ψ hV
  exact (cancel_mono (ιTopIso (X.hom ⁻¹ᵁ V))).mp key

/-- The morphism of pushed-forward structure sheaves attached to `overHomOfAlgebraHom ψ` is
`ψ`: the functor `X ↦ f_* 𝒪_X` is full on the schemes affine over `S`. -/
public theorem pushforwardAlgebraMap_overHomOfAlgebraHom :
    pushforwardAlgebraMap (overHomOfAlgebraHom ψ) = ψ := by
  have hbasis : Opens.IsBasis (Set.range fun V : S.affineOpens ↦ (V : S.Opens)) := by
    simpa using S.isBasis_affineOpens
  ext1
  apply Sheaf.hom_ext
  refine TopCat.Sheaf.hom_ext (pushforwardAlgebra Y.hom).right.obj
    (pushforwardAlgebra X.hom).right hbasis fun V ↦ ?_
  rw [pushforwardAlgebraMap_app (overHomOfAlgebraHom ψ) (V : S.Opens)
    (preimage_le_preimage_preimage (overHomOfAlgebraHom ψ) (V : S.Opens))]
  exact gluedHom_appLE ψ V.2

end

/-! ### Fullness of the pushforward functor -/

/-- The functor `X ↦ f_* 𝒪_X` on the schemes affine over `S` is full. -/
public instance full_affinePushforwardAlgebraFunctor (S : Scheme.{u}) :
    (affinePushforwardAlgebraFunctor S).Full where
  map_surjective {X Y} f := by
    have hX : IsAffineHom (unop X).obj.hom := X.unop.property
    have hX' : IsAffineHom (unop ((IsAffineHomOver S).ι.op.obj X)).hom := X.unop.property
    exact ⟨(ObjectProperty.homMk (overHomOfAlgebraHom f)).op,
      pushforwardAlgebraMap_overHomOfAlgebraHom f⟩

/-- The functor `X ↦ f_* 𝒪_X` from the schemes affine over `S` to the quasi-coherent
`𝒪_S`-algebras is full. -/
public instance full_affineQuasicoherentPushforwardFunctor (S : Scheme.{u}) :
    (affineQuasicoherentPushforwardFunctor S).Full :=
  Functor.Full.of_comp_faithful_iso (affineQuasicoherentPushforwardFunctorCompι S)

end Stacks.AffineAlgebraEquivalence

end
