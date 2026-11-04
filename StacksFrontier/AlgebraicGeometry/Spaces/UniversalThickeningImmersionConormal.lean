module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChangeFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFirstOrderNeighbourhoodIso
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleFlatTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.InfinitesimalNeighbourhoodExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RepresentableComparison

/-!
# The conormal sheaf of an immersion as a formally unramified morphism

Let `S` be a scheme and let `i : Z ⟶ X` be an immersion of algebraic spaces over `S`, presented by
an open subspace `U ⊆ X` in which `Z` is a closed subspace. The immersion is formally unramified
(the first clause of [Stacks Project, Tag 0608]), so it has a conormal sheaf in the sense of
[Stacks Project, Tag 0607], the conormal sheaf of `Z` in a universal first order thickening
`Z ⊂ Z'` of `Z` over `X`. It also has a conormal sheaf as an immersion, [Stacks Project, Tag 04CN],
the conormal module of the closed subspace `Z ⊆ U`. This file proves the third clause of
[Stacks Project, Tag 0608]: the two agree.

## Main definitions

* `AlgebraicGeometry.Space.conormalModulePullbackIsoOfIso`: an isomorphism of algebraic spaces
  identifies the conormal module of a closed subspace with that of its inverse image.
* `AlgebraicGeometry.Space.UniversalFirstOrderThickening.conormalSheafIso`: the conormal sheaf
  of [Stacks Project, Tag 0607] does not depend on the universal first order thickening.
* `AlgebraicGeometry.Space.infinitesimalNeighbourhoodThickening`: the first order infinitesimal
  neighbourhood of an immersion, as a universal first order thickening.
* `AlgebraicGeometry.Space.conormalSheafIsoConormalModuleOfKerEqKerSq`: the comparison, given
  the first order infinitesimal neighbourhood.
* `AlgebraicGeometry.Space.conormalSheafIsoConormalModule`: the conormal sheaf of
  [Stacks Project, Tag 0607] of an immersion is its conormal module, the third clause of
  [Stacks Project, Tag 0608].

## Main results

* `AlgebraicGeometry.Space.UniversalFirstOrderThickening.closedSub_eq_preimageSubspace`: the
  smaller space of one universal first order thickening is the inverse image of that of another
  along the canonical isomorphism.

## Implementation notes

The conormal sheaf of [Stacks Project, Tag 0607] is attached in this library to a datum
`AlgebraicGeometry.Space.UniversalFirstOrderThickening`, not to the morphism alone, so the
comparison is stated for every such datum; by
`AlgebraicGeometry.Space.UniversalFirstOrderThickening.conormalSheafIso` the choice of datum is
immaterial, and by [Stacks Project, Tag 0606]
(`AlgebraicGeometry.Space.nonempty_universalFirstOrderThickening`) one exists.  The conormal sheaf
of the immersion is `AlgebraicGeometry.Space.conormalModule` of `Z` in the open subspace `U`: the
source defines it with `U = X ∖ ∂Z`, and the statement below holds for every open subspace in
which `Z` is closed.

## References

* [Stacks Project, Tag 0608](https://stacks.math.columbia.edu/tag/0608)
* [Stacks Project, Tag 0607](https://stacks.math.columbia.edu/tag/0607)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 05ZX](https://stacks.math.columbia.edu/tag/05ZX)
* [Stacks Project, Tag 04CQ](https://stacks.math.columbia.edu/tag/04CQ)
* [Stacks Project, Tag 060A](https://stacks.math.columbia.edu/tag/060A)
-/

@[expose] public section

open CategoryTheory

universe u

namespace CategoryTheory

/-- **A subfunctor `Z ≤ N` is its own inverse image along the inclusion of `N`**: the
factorization of the inclusion of `Z` through `N`, with inverse the projection of the inverse
image to `Z`. -/
def Subfunctor.preimageIsoOfLe {C : Type*} [Category C] {F : C ⥤ Type*}
    {Z N : Subfunctor F} (hZN : Z ≤ N) : Z.toFunctor ≅ (Z.preimage N.ι).toFunctor where
  hom := Subfunctor.lift (G := Z.preimage N.ι) (Subfunctor.homOfLe hZN) (by
    rintro T _ ⟨w, rfl⟩
    exact w.2)
  inv := Z.fromPreimage N.ι
  hom_inv_id := by
    refine (cancel_mono Z.ι).1 ?_
    rw [Category.assoc, Subfunctor.fromPreimage_ι, ← Category.assoc, Subfunctor.lift_ι,
      Subfunctor.homOfLe_ι, Category.id_comp]
  inv_hom_id := by
    refine (cancel_mono (Z.preimage N.ι).ι).1 ?_
    refine (cancel_mono N.ι).1 ?_
    rw [Category.assoc, Category.assoc, Subfunctor.lift_ι_assoc, Subfunctor.homOfLe_ι,
      Subfunctor.fromPreimage_ι, Category.id_comp]

/-- The identification of `Z` with its inverse image in `N`, followed by the inclusion of that
inverse image, is the inclusion of `Z` in `N`. -/
@[reassoc]
theorem Subfunctor.preimageIsoOfLe_hom_ι
    {C : Type*} [Category C] {F : C ⥤ Type*} {Z N : Subfunctor F} (hZN : Z ≤ N) :
    (Subfunctor.preimageIsoOfLe hZN).hom ≫ (Z.preimage N.ι).ι = Subfunctor.homOfLe hZN :=
  rfl

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An isomorphism of algebraic spaces identifies conormal modules.**  Let `e : Y₁ ≅ Y₂` be an
isomorphism of algebraic spaces, `W₂ ⊆ Y₂` a closed subspace and `W₁ = e⁻¹(W₂)`.  Two morphisms
`s₁ : W ⟶ W₁` and `s₂ : W ⟶ W₂` which agree in `Y₂` pull the two conormal modules back to
isomorphic modules on `W`. -/
noncomputable def conormalModulePullbackIsoOfIso {Y₁ Y₂ W : AlgebraicSpaces B S hS}
    (e : Y₁ ≅ Y₂) (W₂ : ClosedSubspaces B S hS Y₂.1) (W₁ : ClosedSubspaces B S hS Y₁.1)
    (hW : W₁ = preimageSubspace B S hS e.hom W₂)
    (s₁ : W ⟶ ⟨W₁.1.toFunctor, W₁.2.1⟩) (s₂ : W ⟶ ⟨W₂.1.toFunctor, W₂.2.1⟩)
    (hs : s₁.hom ≫ W₁.1.ι ≫ e.hom.hom = s₂.hom ≫ W₂.1.ι) :
    (modulePullback B S hS s₁).obj (conormalModule B S hS Y₁ W₁) ≅
      (modulePullback B S hS s₂).obj (conormalModule B S hS Y₂ W₂) := by
  subst hW
  have hs' : s₁ ≫ preimageProjection B S hS e.hom W₂ = s₂ := by
    apply ObjectProperty.hom_ext
    refine (cancel_mono W₂.1.ι).1 ?_
    rw [ObjectProperty.FullSubcategory.comp_hom, Category.assoc]
    exact (congrArg (s₁.hom ≫ ·) (Subfunctor.fromPreimage_ι W₂.1 e.hom.hom)).trans hs
  have hiso : IsIso e.hom.hom :=
    inferInstanceAs (IsIso ((ObjectProperty.ι _).mapIso e).hom)
  have hflat : (smallEtaleRingedToposHom B S hS e.hom).IsFlat :=
    (isFlat_iff_smallEtaleRingedToposHom_isFlat B S hS e.hom).1
      (isFlat_of_isEtale B S hS (isEtale_of_isIso B S hS e.hom.hom))
  have := isIso_conormalMap_of_isFlat B S hS e.hom W₂ hflat
  exact (modulePullback B S hS s₁).mapIso (asIso (conormalMap B S hS
      (preimageSubspace B S hS e.hom W₂) W₂ e.hom (preimageProjection B S hS e.hom W₂)
      (conormalEtaleRestrictionSquare B S hS e.hom W₂))).symm ≪≫
    (modulePullbackCompIso B S hS s₁ (preimageProjection B S hS e.hom W₂)).app _ ≪≫
    eqToIso (by rw [hs'])

namespace UniversalFirstOrderThickening

variable {B S hS} {Z X : AlgebraicSpaces B S hS} {h : Z ⟶ X}

/-- The canonical morphism between two universal first order thickenings carries the smaller
space of the first into that of the second. -/
theorem canonicalMap_app_mem (t₁ t₂ : UniversalFirstOrderThickening B S hS h)
    {T : (BigFppfOver B S hS)ᵒᵖ} {x : t₁.ambient.obj.obj T} (hx : x ∈ t₁.sub.obj T) :
    (canonicalMap t₁ t₂).hom.app T x ∈ t₂.sub.obj T := by
  have key := ConcreteCategory.congr_hom (NatTrans.congr_app (canonicalMap_restrict t₁ t₂) T)
    (⟨x, hx⟩ : t₁.sub.toFunctor.obj T)
  change (canonicalMap t₁ t₂).hom.app T x = ((subComparison t₁ t₂).app T ⟨x, hx⟩).1 at key
  rw [key]
  exact ((subComparison t₁ t₂).app T ⟨x, hx⟩).2

/-- **The smaller space of a universal first order thickening is the inverse image of that of
another along the canonical isomorphism.** -/
theorem closedSub_eq_preimageSubspace (t₁ t₂ : UniversalFirstOrderThickening B S hS h) :
    t₁.closedSub = preimageSubspace B S hS (canonicalIso t₁ t₂).hom t₂.closedSub := by
  refine Subtype.ext (le_antisymm (fun T x hx => canonicalMap_app_mem t₁ t₂ hx) fun T x hx => ?_)
  have hx' : (canonicalMap t₁ t₂).hom.app T x ∈ t₂.sub.obj T := hx
  have h₁ := canonicalMap_app_mem t₂ t₁ (T := T) hx'
  have h₂ : (canonicalMap t₂ t₁).hom.app T ((canonicalMap t₁ t₂).hom.app T x) = x :=
    ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg InducedCategory.Hom.hom
      (canonicalMap_comp_canonicalMap t₁ t₂)) T) x
  rw [h₂] at h₁
  exact h₁

/-- **The conormal sheaf of [Stacks Project, Tag 0607] does not depend on the universal first
order thickening.** The conormal sheaves of two universal first order thickenings of `h` are
identified along the canonical isomorphism of their ambient spaces. -/
noncomputable def conormalSheafIso (t₁ t₂ : UniversalFirstOrderThickening B S hS h) :
    conormalSheaf B S hS t₁ ≅ conormalSheaf B S hS t₂ :=
  conormalModulePullbackIsoOfIso B S hS (canonicalIso t₁ t₂) t₂.closedSub t₁.closedSub
    (closedSub_eq_preimageSubspace t₁ t₂) t₁.sourceInclusion t₂.sourceInclusion (by
      change t₁.sourceIso.hom ≫ t₁.sub.ι ≫ (canonicalMap t₁ t₂).hom = _
      rw [canonicalMap_restrict, subComparison, Category.assoc, Iso.hom_inv_id_assoc]
      rfl)

end UniversalFirstOrderThickening

/-! ### The first order infinitesimal neighbourhood as a universal thickening -/

section Neighbourhood

variable {B S hS} {X : AlgebraicSpaces B S hS} {U : Subfunctor X.1}

variable (hU : IsOpenSubspace B S hS U)
    {Z N : ClosedSubspaces B S hS (⟨U.toFunctor, hU.1⟩ : AlgebraicSpaces B S hS).1}
    (hN : ∀ V : SmallEtale B S hS U.toFunctor,
      ((BigFppfOver.toScheme B S hS).map (N.2.2.rep.snd V.1.hom)).ker =
        ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd V.1.hom)).ker ^ 2)

/-- **The first order infinitesimal neighbourhood of an immersion, as a universal first order
thickening of it** in the sense of [Stacks Project, Tag 0607]: the ambient space is the
neighbourhood `N`, the smaller space the inverse image of `Z` in `N`, and the universal property
is the second clause of [Stacks Project, Tag 0608]. -/
noncomputable def infinitesimalNeighbourhoodThickening
    (hfu : FormallyUnramified (Z.1.ι ≫ U.ι)) :
    UniversalFirstOrderThickening B S hS
      (ObjectProperty.homMk (Z.1.ι ≫ U.ι) :
        (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ X) where
  formallyUnramified := hfu
  ambient := ⟨N.1.toFunctor, N.2.1⟩
  toBase := ObjectProperty.homMk (N.1.ι ≫ U.ι)
  sub := Z.1.preimage N.1.ι
  isUniversal := isUniversalFirstOrderThickening_infinitesimalNeighbourhood B S hS hU Z N hN
  sourceIso := Subfunctor.preimageIsoOfLe (le_of_ker_eq_ker_pow B S hS Z N hN)
  sourceIso_ι_toBase := by
    change (Subfunctor.preimageIsoOfLe (le_of_ker_eq_ker_pow B S hS Z N hN)).hom ≫
      (Z.1.preimage N.1.ι).ι ≫ N.1.ι ≫ U.ι = Z.1.ι ≫ U.ι
    rw [Subfunctor.preimageIsoOfLe_hom_ι_assoc, Subfunctor.homOfLe_ι_assoc]

include hN in
/-- **The conormal sheaf of a universal first order thickening of an immersion is the conormal
module of `Z` in `U`**, as soon as the first order infinitesimal neighbourhood `N` of `Z` in `U`
is given. -/
noncomputable def conormalSheafIsoConormalModuleOfKerEqKerSq
    (t : UniversalFirstOrderThickening B S hS
      (ObjectProperty.homMk (Z.1.ι ≫ U.ι) :
        (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ X)) :
    conormalSheaf B S hS t ≅ conormalModule B S hS ⟨U.toFunctor, hU.1⟩ Z :=
  have hZN := le_of_ker_eq_ker_pow B S hS Z N hN
  have := isIso_conormalMap_of_ker_eq_ker_sq B S hS (X := ⟨U.toFunctor, hU.1⟩) hN
  let tN := infinitesimalNeighbourhoodThickening hU hN t.formallyUnramified
  let Zn := preimageSubspace B S hS (subspaceInclusion B S hS ⟨U.toFunctor, hU.1⟩ N) Z
  let s₂ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Zn.1.toFunctor, Zn.2.1⟩ :=
    ObjectProperty.homMk (Subfunctor.preimageIsoOfLe hZN).hom
  let f := preimageProjection B S hS (subspaceInclusion B S hS ⟨U.toFunctor, hU.1⟩ N) Z
  have hsf : s₂ ≫ f = 𝟙 _ :=
    ObjectProperty.hom_ext _ (Subfunctor.preimageIsoOfLe hZN).hom_inv_id
  have hW : t.closedSub =
      preimageSubspace B S hS (UniversalFirstOrderThickening.canonicalIso t tN).hom Zn :=
    UniversalFirstOrderThickening.closedSub_eq_preimageSubspace t tN
  have hs : t.sourceInclusion.hom ≫ t.closedSub.1.ι ≫
      (UniversalFirstOrderThickening.canonicalIso t tN).hom.hom = s₂.hom ≫ Zn.1.ι := by
    change t.sourceIso.hom ≫ t.sub.ι ≫ (UniversalFirstOrderThickening.canonicalMap t tN).hom = _
    rw [UniversalFirstOrderThickening.canonicalMap_restrict,
      UniversalFirstOrderThickening.subComparison, Category.assoc, Iso.hom_inv_id_assoc]
    rfl
  conormalModulePullbackIsoOfIso B S hS (UniversalFirstOrderThickening.canonicalIso t tN) Zn
      t.closedSub hW t.sourceInclusion s₂ hs ≪≫
    (modulePullback B S hS s₂).mapIso (asIso (conormalMap B S hS Zn Z
      (subspaceInclusion B S hS ⟨U.toFunctor, hU.1⟩ N) f
      (conormalEtaleRestrictionSquare B S hS
        (subspaceInclusion B S hS ⟨U.toFunctor, hU.1⟩ N) Z))).symm ≪≫
    (modulePullbackCompIso B S hS s₂ f).app (conormalModule B S hS ⟨U.toFunctor, hU.1⟩ Z) ≪≫
    eqToIso (congrArg (fun g : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      ⟨Z.1.toFunctor, Z.2.1⟩ => (modulePullback B S hS g).obj
        (conormalModule B S hS ⟨U.toFunctor, hU.1⟩ Z)) hsf) ≪≫
    (modulePullbackIdIso B S hS ⟨Z.1.toFunctor, Z.2.1⟩).app
      (conormalModule B S hS ⟨U.toFunctor, hU.1⟩ Z)

end Neighbourhood

/-- Let `i : Z ⟶ X` be an immersion of algebraic spaces over `S`, presented by an open subspace
`U ⊆ X` in which `Z` is a closed subspace, and let `Z ⊂ Z'` be a universal first order thickening
of `Z` over `X`. The conormal sheaf of `i` as a formally unramified morphism,
[Stacks Project, Tag 0607], is isomorphic to the conormal sheaf of `i` as an immersion,
[Stacks Project, Tag 04CN], that is to the conormal module of `Z` in `U`. -/
@[stacks 0608 "part (3)"]
noncomputable def conormalSheafIsoConormalModule {X : AlgebraicSpaces B S hS}
    {U : Subfunctor X.1} (hU : IsOpenSubspace B S hS U)
    (Z : ClosedSubspaces B S hS (⟨U.toFunctor, hU.1⟩ : AlgebraicSpaces B S hS).1)
    (t : UniversalFirstOrderThickening B S hS
      (ObjectProperty.homMk (Z.1.ι ≫ U.ι) :
        (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ X)) :
    conormalSheaf B S hS t ≅ conormalModule B S hS ⟨U.toFunctor, hU.1⟩ Z :=
  conormalSheafIsoConormalModuleOfKerEqKerSq hU
    (Classical.choose_spec (exists_ker_eq_ker_sq B S hS ⟨U.toFunctor, hU.1⟩ Z)) t

end AlgebraicGeometry.Space

end
