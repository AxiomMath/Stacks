module

public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.WholeTag
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceBaseChange
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceChangeModule
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.ZeroSectionZeroScheme
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeTensorInf
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.BaseChange
public import StacksFrontier.AlgebraicGeometry.PullbackTensorIso.Composite
public import StacksFrontier.AlgebraicGeometry.PullbackTensorIso.Sections

/-!
# Base change of the data of Tag 0F97

[Stacks, Tag 0F97] asserts, besides the existence of the decomposition
`Stacks.Chow.TensorZeroScheme.Decomposition`, that the whole diagram is compatible with arbitrary
base change. The base-changed decomposition is not a second run of the construction but the
*transport* of the given one: its total space is the fibre product `L ×_Y Y'`, its two closed
subschemes are the inverse images of `D₁` and `D₂`, and its two sections are the pullbacks of
`s₁` and `s₂`. This file proves the statements about the divisor `D`, the comparison of
[Stacks, Tag 01CD] and the sections of a decomposition that this transport involves.

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.subschemeLift`: the factorization of a morphism whose
  kernel contains a given quasi-coherent ideal through the closed subscheme it cuts out.
* `Stacks.Chow.TensorZeroScheme.zeroIdealBaseChangeMap`: the canonical morphism `D' ⟶ D` of the
  zero schemes of `g^*s` and of `s`.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.ker_inclusion_le_sup_left`: **the scheme-theoretic
  intersection of two closed subschemes, read inside the first one**, is the inverse image of the
  ideal of the second along the closed immersion of the first.
* `AlgebraicGeometry.Scheme.Hom.ker_eq_comap_ker_of_isPullback`: in a cartesian square whose
  right edge is a closed immersion, the kernel of the top edge is the inverse image of the kernel
  of that closed immersion.
* `Stacks.PullbackTensorIso.pullbackCompHom_eq`: **the two spellings of the contraction of an
  iterated pullback agree**, the ringed-space comparison being Mathlib's
  `AlgebraicGeometry.Scheme.Modules.pullbackComp`.
* `Stacks.PullbackTensorIso.pullbackTensorSection_of_square`: **the comparison of
  [Stacks, Tag 01CD] is compatible with a commutative square.** This is clause (1) of
  [Stacks, Tag 0F97] for a base-changed decomposition.
* `Stacks.LineBundle.isRegularSection_restrict_of_inf_eq_zeroSection`: **a global section whose
  zero scheme meets a closed subscheme in the zero section of a line bundle over it restricts to
  a regular section of that subscheme.**
* `Stacks.Chow.TensorZeroScheme.comap_zeroIdeal`: **the closed subscheme `i : D → Y` of
  [Stacks, Tag 0F97] commutes with arbitrary base change.**
* `Stacks.Chow.TensorZeroScheme.isPullback_zeroIdealBaseChangeMap`: the same statement as a
  cartesian square, `D' = D ×_Y Y'`.
* `Stacks.Chow.TensorZeroScheme.isRegularSection_restrict_s₂`: the regularity statement above
  read off a decomposition.

## References

* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 0F96](https://stacks.math.columbia.edu/tag/0F96)
* [Stacks Project, Tag 02OO](https://stacks.math.columbia.edu/tag/02OO)
* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.PullbackTensorIso (pullbackTensorSection pullbackCompHom)

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- A morphism whose kernel contains `K` factors through the closed subscheme cut out by `K`. -/
def subschemeLift {W : Scheme.{u}} {K : X.IdealSheafData} (q : W ⟶ X) (hK : K ≤ q.ker) :
    W ⟶ K.subscheme :=
  q.toImage ≫ inclusion hK

/-- The factorization `subschemeLift q hK` followed by the closed immersion of `K` is `q`. -/
@[reassoc (attr := simp)]
theorem subschemeLift_subschemeι {W : Scheme.{u}} {K : X.IdealSheafData} (q : W ⟶ X)
    (hK : K ≤ q.ker) : subschemeLift q hK ≫ K.subschemeι = q := by
  rw [subschemeLift, Category.assoc, inclusion_subschemeι]
  exact q.toImage_imageι

/-- **The scheme-theoretic intersection of two closed subschemes, read inside the first one.**
The kernel of the inclusion `D₁ ∩ D₂ ⟶ D₁` is the inverse image of the ideal of `D₂` along the
closed immersion of `D₁`. -/
theorem ker_inclusion_le_sup_left (I J : X.IdealSheafData) :
    (inclusion (le_sup_left : I ≤ I ⊔ J)).ker = J.comap I.subschemeι := by
  have hfst : (pullback.fst I.subschemeι J.subschemeι).ker = J.comap I.subschemeι :=
    (ker_fst_of_isClosedImmersion J.subschemeι I.subschemeι).trans
      (congrArg (fun K => K.comap I.subschemeι) J.ker_subschemeι)
  have hI : I ≤ (pullback.fst I.subschemeι J.subschemeι ≫ I.subschemeι).ker :=
    I.ker_subschemeι.ge.trans (Scheme.Hom.le_ker_comp _ _)
  have hJ : J ≤ (pullback.fst I.subschemeι J.subschemeι ≫ I.subschemeι).ker := by
    rw [pullback.condition]
    exact J.ker_subschemeι.ge.trans (Scheme.Hom.le_ker_comp _ _)
  obtain ⟨u, hu⟩ : ∃ u : pullback I.subschemeι J.subschemeι ⟶ (I ⊔ J).subscheme,
      u ≫ inclusion (le_sup_left : I ≤ I ⊔ J) = pullback.fst I.subschemeι J.subschemeι := by
    refine ⟨subschemeLift (pullback.fst I.subschemeι J.subschemeι ≫ I.subschemeι)
      (sup_le hI hJ), ?_⟩
    refine (cancel_mono I.subschemeι).1 ?_
    rw [Category.assoc, inclusion_subschemeι, subschemeLift_subschemeι]
  obtain ⟨t, ht⟩ : ∃ t : (I ⊔ J).subscheme ⟶ pullback I.subschemeι J.subschemeι,
      t ≫ pullback.fst I.subschemeι J.subschemeι = inclusion (le_sup_left : I ≤ I ⊔ J) :=
    ⟨pullback.lift (inclusion (le_sup_left : I ≤ I ⊔ J)) (inclusion (le_sup_right : J ≤ I ⊔ J))
      (by rw [inclusion_subschemeι, inclusion_subschemeι]), pullback.lift_fst _ _ _⟩
  refine le_antisymm ?_ ?_
  · have hle := Scheme.Hom.le_ker_comp u (inclusion (le_sup_left : I ≤ I ⊔ J))
    rw [hu] at hle
    exact hle.trans hfst.le
  · have hle := Scheme.Hom.le_ker_comp t (pullback.fst I.subschemeι J.subschemeι)
    rw [ht] at hle
    exact hfst.ge.trans hle

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry

/-- **In a cartesian square whose right edge is a closed immersion, the kernel of the top edge
is the inverse image of the kernel of that closed immersion** along the bottom edge. -/
theorem Scheme.Hom.ker_eq_comap_ker_of_isPullback {P A B W : Scheme.{u}} {a : P ⟶ A} {b : P ⟶ B}
    {c : A ⟶ W} {d : B ⟶ W} (hsq : IsPullback a b c d) [IsClosedImmersion d] :
    a.ker = d.ker.comap c := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion d c, ← hsq.isoPullback_hom_fst]
  exact Scheme.Hom.ker_comp_of_isIso _ _

end AlgebraicGeometry

namespace Stacks.PullbackTensorIso

/-- **The two spellings of the contraction of an iterated pullback agree**: `pullbackCompHom f g M`
is the component at `M` of Mathlib's `AlgebraicGeometry.Scheme.Modules.pullbackComp f g`. -/
theorem pullbackCompHom_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) :
    pullbackCompHom f g M = (Scheme.Modules.pullbackComp f g).hom.app M := by rfl

section Square

variable {W : Scheme.{u}}

/-- The tensor product functor on pairs of modules over `W`, as a functor out of the product. -/
private abbrev tensorSheafFunctor (W : Scheme.{u}) : W.Modules × W.Modules ⥤ W.Modules :=
  Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
    ⟨(W.toRingedSpace).presheaf, (W.toRingedSpace).IsSheaf⟩)

/-- The tensor product of two identities acts as the identity on a product of global sections. -/
private theorem tensorSheafMap_id_app (A B : W.Modules)
    (z : Γ(Stacks.Divisors.tensorModules A B, ⊤)) :
    PresheafOfModules.Hom.app ((tensorSheafFunctor W).map
      ((𝟙 A, 𝟙 B) : ((A, B) : W.Modules × W.Modules) ⟶ (A, B))).val (op ⊤) z = z := by
  have hmap : (tensorSheafFunctor W).map
      ((𝟙 A, 𝟙 B) : ((A, B) : W.Modules × W.Modules) ⟶ (A, B)) = 𝟙 _ :=
    (tensorSheafFunctor W).map_id ((A, B) : W.Modules × W.Modules)
  rw [hmap]
  rfl

/-- A pair of split morphisms of modules acts invertibly on a product of global sections. -/
private theorem tensorSheafMap_cancel {A₁ A₂ B₁ B₂ : W.Modules} {u : A₁ ⟶ A₂} {v : B₁ ⟶ B₂}
    {u' : A₂ ⟶ A₁} {v' : B₂ ⟶ B₁} (hu : u ≫ u' = 𝟙 A₁) (hv : v ≫ v' = 𝟙 B₁)
    (z : Γ(Stacks.Divisors.tensorModules A₁ B₁, ⊤)) :
    PresheafOfModules.Hom.app ((tensorSheafFunctor W).map
        ((u', v') : ((A₂, B₂) : W.Modules × W.Modules) ⟶ (A₁, B₁))).val (op ⊤)
      (PresheafOfModules.Hom.app ((tensorSheafFunctor W).map
        ((u, v) : ((A₁, B₁) : W.Modules × W.Modules) ⟶ (A₂, B₂))).val (op ⊤) z) = z := by
  have hmap : (tensorSheafFunctor W).map
      ((u, v) : ((A₁, B₁) : W.Modules × W.Modules) ⟶ (A₂, B₂)) ≫
      (tensorSheafFunctor W).map
        ((u', v') : ((A₂, B₂) : W.Modules × W.Modules) ⟶ (A₁, B₁)) = 𝟙 _ := by
    rw [← Functor.map_comp]
    exact (congrArg _ (Prod.ext hu hv : _ = 𝟙 (A₁, B₁))).trans ((tensorSheafFunctor W).map_id _)
  have hz : PresheafOfModules.Hom.app ((tensorSheafFunctor W).map
      ((u, v) : ((A₁, B₁) : W.Modules × W.Modules) ⟶ (A₂, B₂)) ≫
        (tensorSheafFunctor W).map
          ((u', v') : ((A₂, B₂) : W.Modules × W.Modules) ⟶ (A₁, B₁))).val (op ⊤) z = z := by
    rw [hmap]
    rfl
  exact hz

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {h : X' ⟶ X}

/-- The comparison of [Stacks, Tag 01CD] is compatible with the identification of the pullbacks
along two equal morphisms. -/
private theorem pullbackCongr_pullbackTensorSection (A B : Y.Modules)
    (t : Γ(Stacks.Divisors.tensorModules A B, ⊤)) (k : X' ⟶ Y) (hk : k = f' ≫ g) :
    PresheafOfModules.Hom.app ((tensorSheafFunctor X').map
          (((Scheme.Modules.pullbackCongr hk).hom.app A,
              (Scheme.Modules.pullbackCongr hk).hom.app B) :
            (((Scheme.Modules.pullback k).obj A,
                (Scheme.Modules.pullback k).obj B) : X'.Modules × X'.Modules) ⟶
              ((Scheme.Modules.pullback (f' ≫ g)).obj A,
                (Scheme.Modules.pullback (f' ≫ g)).obj B))).val (op ⊤)
        (pullbackTensorSection k A B t) =
      pullbackTensorSection (f' ≫ g) A B t := by
  subst hk
  exact tensorSheafMap_id_app _ _ _

/-- **The comparison of [Stacks, Tag 01CD] is compatible with a commutative square.** For a
commutative square `h ≫ f = f' ≫ g` and a global section `t` of `A ⊗ B` on the lower-right
corner, if the pullback of `t` along `f` is the product of two sections `a` and `b`, then the
pullback of `t` along `g` and then along `f'` is the product of the pullbacks of `a` and `b`
along `h`, read through `Stacks.Chow.TensorZeroScheme.squarePullbackMap`. -/
theorem pullbackTensorSection_of_square (w : h ≫ f = f' ≫ g) (A B : Y.Modules)
    (t : Γ(Stacks.Divisors.tensorModules A B, ⊤))
    (a : Γ((Scheme.Modules.pullback f).obj A, ⊤))
    (b : Γ((Scheme.Modules.pullback f).obj B, ⊤))
    (ht : pullbackTensorSection f A B t =
      Stacks.Divisors.tensorSection ((Scheme.Modules.pullback f).obj A)
        ((Scheme.Modules.pullback f).obj B) ⊤ a b) :
    pullbackTensorSection f' ((Scheme.Modules.pullback g).obj A)
        ((Scheme.Modules.pullback g).obj B) (pullbackTensorSection g A B t) =
      Stacks.Divisors.tensorSection _ _ ⊤
        (Scheme.Modules.Hom.app (Stacks.Chow.TensorZeroScheme.squarePullbackMap w A) ⊤
          (AlgebraicGeometry.pullbackGlobalSections h ((Scheme.Modules.pullback f).obj A) a))
        (Scheme.Modules.Hom.app (Stacks.Chow.TensorZeroScheme.squarePullbackMap w B) ⊤
          (AlgebraicGeometry.pullbackGlobalSections h
            ((Scheme.Modules.pullback f).obj B) b)) := by
  have step₁ : pullbackTensorSection (h ≫ f) A B t =
      Stacks.Divisors.tensorSection _ _ ⊤
        (Scheme.Modules.Hom.app (pullbackCompHom h f A) ⊤
          (AlgebraicGeometry.pullbackGlobalSections h ((Scheme.Modules.pullback f).obj A) a))
        (Scheme.Modules.Hom.app (pullbackCompHom h f B) ⊤
          (AlgebraicGeometry.pullbackGlobalSections h
            ((Scheme.Modules.pullback f).obj B) b)) := by
    rw [pullbackTensorSection_comp h f A B t, ht,
      show pullbackTensorSection h ((Scheme.Modules.pullback f).obj A)
            ((Scheme.Modules.pullback f).obj B)
            (Stacks.Divisors.tensorSection ((Scheme.Modules.pullback f).obj A)
              ((Scheme.Modules.pullback f).obj B) ⊤ a b) =
          Stacks.Divisors.tensorSection _ _ ⊤
            (AlgebraicGeometry.pullbackGlobalSections h
              ((Scheme.Modules.pullback f).obj A) a)
            (AlgebraicGeometry.pullbackGlobalSections h
              ((Scheme.Modules.pullback f).obj B) b) from
        pullbackGlobalSections_tensorSectionsAt h _ _ a b]
    exact tensorSheafMap_tensorSectionsAt _ _ _ _
  have step₂ : pullbackTensorSection (f' ≫ g) A B t =
      Stacks.Divisors.tensorSection _ _ ⊤
        (Scheme.Modules.Hom.app
          (pullbackCompHom h f A ≫ (Scheme.Modules.pullbackCongr w).hom.app A) ⊤
          (AlgebraicGeometry.pullbackGlobalSections h ((Scheme.Modules.pullback f).obj A) a))
        (Scheme.Modules.Hom.app
          (pullbackCompHom h f B ≫ (Scheme.Modules.pullbackCongr w).hom.app B) ⊤
          (AlgebraicGeometry.pullbackGlobalSections h
            ((Scheme.Modules.pullback f).obj B) b)) := by
    rw [← pullbackCongr_pullbackTensorSection A B t (h ≫ f) w, step₁]
    exact tensorSheafMap_tensorSectionsAt _ _ _ _
  refine Eq.trans (tensorSheafMap_cancel
      (u := pullbackCompHom f' g A) (v := pullbackCompHom f' g B)
      (u' := (Scheme.Modules.pullbackComp f' g).inv.app A)
      (v' := (Scheme.Modules.pullbackComp f' g).inv.app B)
      ((congrArg (fun φ => φ ≫ (Scheme.Modules.pullbackComp f' g).inv.app A)
          (pullbackCompHom_eq f' g A)).trans
        ((Scheme.Modules.pullbackComp f' g).hom_inv_id_app A))
      ((congrArg (fun φ => φ ≫ (Scheme.Modules.pullbackComp f' g).inv.app B)
          (pullbackCompHom_eq f' g B)).trans
        ((Scheme.Modules.pullbackComp f' g).hom_inv_id_app B)) _).symm ?_
  refine (congrArg _ (pullbackTensorSection_comp f' g A B t).symm).trans ?_
  rw [step₂]
  exact tensorSheafMap_tensorSectionsAt _ _ _ _

end Square

end Stacks.PullbackTensorIso

namespace Stacks.LineBundle

/-- **A global section whose zero scheme meets a closed subscheme in the zero section of a line
bundle over it restricts to a regular section of that subscheme.**

Let `D₁`, `D₂` be closed subschemes of `V`, let `D₂` be the zero scheme of a global section `t`
of an invertible module `M`, let `D₁` be identified by `b` with the total space of a line bundle
`E`, and let the scheme-theoretic intersection `D₁ ∩ D₂`, read in `Tot(E)` through `b`, be the
image of the zero section of `E` under an isomorphism `c` of `D₁ ∩ D₂` with the base of `E`.
Then the restriction `t|_{D₁}` is a regular section of `M|_{D₁}`. -/
theorem isRegularSection_restrict_of_inf_eq_zeroSection {V : Scheme.{u}}
    (D₁ D₂ : V.IdealSheafData) (M : V.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible V.sheaf.obj V.ringCatSheaf.property M]
    (t : Γ(M, ⊤)) (hD₂ : D₂ = Stacks.Divisors.zeroScheme V M t)
    (E : Situation.{u}) (b : D₁.subscheme ≅ E.totalSpace)
    (c : (D₁ ⊔ D₂).subscheme ⟶ E.X) (hciso : IsIso c)
    (hc : Scheme.IdealSheafData.inclusion (le_sup_left : D₁ ≤ D₁ ⊔ D₂) ≫ b.hom =
      c ≫ E.zeroSection) :
    AlgebraicGeometry.IsRegularSection D₁.subscheme.sheaf.obj
      D₁.subscheme.ringCatSheaf.property
      (Stacks.SheafOfModules.sectionsOfTop
        ((Scheme.Modules.pullback D₁.subschemeι).obj M)
        (AlgebraicGeometry.pullbackGlobalSections D₁.subschemeι M t)) := by
  have := hciso
  let : AlgebraicGeometry.SheafOfModules.IsInvertible D₁.subscheme.sheaf.obj
      D₁.subscheme.ringCatSheaf.property ((Scheme.Modules.pullback D₁.subschemeι).obj M) :=
    Stacks.Divisors.pullback_isInvertible _ _
  refine (AlgebraicGeometry.isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection
    D₁.subscheme _ _).mp ?_
  have hz : Stacks.Divisors.zeroScheme D₁.subscheme
      ((Scheme.Modules.pullback D₁.subschemeι).obj M)
      (AlgebraicGeometry.pullbackGlobalSections D₁.subschemeι M t) =
      D₂.comap D₁.subschemeι := by
    rw [Stacks.Divisors.zeroScheme_pullback D₁.subschemeι M t, ← hD₂]
  have hsq : IsPullback (Scheme.IdealSheafData.inclusion (le_sup_left : D₁ ≤ D₁ ⊔ D₂)) c b.hom
      E.zeroSection := IsPullback.of_vert_isIso ⟨hc⟩
  have hfinal : Stacks.Divisors.zeroScheme D₁.subscheme
        ((Scheme.Modules.pullback D₁.subschemeι).obj M)
        ((Stacks.SheafOfModules.sectionsOfTop
            ((Scheme.Modules.pullback D₁.subschemeι).obj M)
            (AlgebraicGeometry.pullbackGlobalSections D₁.subschemeι M t)).eval (op ⊤)) =
      E.zeroSection.ker.comap b.hom :=
    (congrArg (Stacks.Divisors.zeroScheme D₁.subscheme
        ((Scheme.Modules.pullback D₁.subschemeι).obj M))
      (Stacks.SheafOfModules.sectionsOfTop_eval_top _ _)).trans
      (hz.trans ((Scheme.IdealSheafData.ker_inclusion_le_sup_left D₁ D₂).symm.trans
        (Scheme.Hom.ker_eq_comap_ker_of_isPullback hsq)))
  exact Eq.mpr (congrArg Stacks.Divisors.IsEffectiveCartierDivisor hfinal)
    (Stacks.Divisors.isPullbackDefined_of_flat b.hom _
      E.isRelativeEffectiveCartierDivisor_ker_zeroSection.1)

end Stacks.LineBundle

namespace Stacks.Chow.TensorZeroScheme

variable {Y : Scheme.{u}} {L₁ L₂ : Y.Modules}
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]
  (s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤))

include h₁ h₂ in
/-- **The closed subscheme `i : D → Y` of [Stacks, Tag 0F97] commutes with arbitrary base
change**: the zero scheme of the base-changed section `g^*s`, read in
`g^*L₁ ⊗ g^*L₂` through the comparison of [Stacks, Tag 01CD], is the scheme-theoretic inverse
image `g^{-1}D`. -/
theorem comap_zeroIdeal {Y' : Scheme.{u}} (g : Y' ⟶ Y) :
    (zeroIdeal Y L₁ L₂ s).comap g =
      zeroIdeal Y' ((Scheme.Modules.pullback g).obj L₁) ((Scheme.Modules.pullback g).obj L₂)
        (pullbackTensorSection g L₁ L₂ s) := by
  let : AlgebraicGeometry.SheafOfModules.IsInvertible Y'.sheaf.obj Y'.ringCatSheaf.property
      ((Scheme.Modules.pullback g).obj (Stacks.Divisors.tensorModules L₁ L₂)) :=
    Stacks.Divisors.pullback_isInvertible _ _
  refine (Stacks.Divisors.zeroScheme_pullback g (Stacks.Divisors.tensorModules L₁ L₂) s).symm.trans
    ?_
  exact AlgebraicGeometry.zeroScheme_eq_of_iso
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso g L₁ L₂)
    (t := pullbackTensorSection g L₁ L₂ s) rfl

include h₁ h₂ in
/-- **The canonical morphism `D' ⟶ D` of the zero schemes of `g^*s` and of `s`.** -/
def zeroIdealBaseChangeMap {Y' : Scheme.{u}} (g : Y' ⟶ Y) :
    (zeroIdeal Y' ((Scheme.Modules.pullback g).obj L₁) ((Scheme.Modules.pullback g).obj L₂)
        (pullbackTensorSection g L₁ L₂ s)).subscheme ⟶ (zeroIdeal Y L₁ L₂ s).subscheme :=
  Scheme.IdealSheafData.subschemeMap _ _ g
    (Scheme.IdealSheafData.le_map_iff_comap_le.2 (comap_zeroIdeal s g).le)

include h₁ h₂ in
/-- The canonical morphism of zero schemes lies over `g`. -/
@[reassoc]
theorem zeroIdealBaseChangeMap_comp_subschemeι {Y' : Scheme.{u}} (g : Y' ⟶ Y) :
    zeroIdealBaseChangeMap s g ≫ (zeroIdeal Y L₁ L₂ s).subschemeι =
      (zeroIdeal Y' ((Scheme.Modules.pullback g).obj L₁) ((Scheme.Modules.pullback g).obj L₂)
        (pullbackTensorSection g L₁ L₂ s)).subschemeι ≫ g :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

include h₁ h₂ in
/-- **The closed subscheme `i : D → Y` of [Stacks, Tag 0F97] commutes with arbitrary base change,
as a cartesian square**: `D' = D ×_Y Y'`. -/
theorem isPullback_zeroIdealBaseChangeMap {Y' : Scheme.{u}} (g : Y' ⟶ Y) :
    IsPullback
      (zeroIdeal Y' ((Scheme.Modules.pullback g).obj L₁) ((Scheme.Modules.pullback g).obj L₂)
        (pullbackTensorSection g L₁ L₂ s)).subschemeι
      (zeroIdealBaseChangeMap s g) g (zeroIdeal Y L₁ L₂ s).subschemeι :=
  AlgebraicGeometry.isPullback_of_isClosedImmersion _ _ _ _
    (zeroIdealBaseChangeMap_comp_subschemeι s g).symm
    (by
      rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι]
      exact comap_zeroIdeal s g)

include h₁ h₂ in
/-- **The restriction of `s₂` to `D₁` is a regular section**, for every decomposition of
[Stacks, Tag 0F97]. -/
theorem isRegularSection_restrict_s₂ (R : Decomposition Y L₁ L₂ s) :
    letI : AlgebraicGeometry.SheafOfModules.IsInvertible R.total.sheaf.obj
        R.total.ringCatSheaf.property ((Scheme.Modules.pullback R.p).obj L₂) :=
      Stacks.Divisors.pullback_isInvertible R.p L₂
    AlgebraicGeometry.IsRegularSection R.D₁.subscheme.sheaf.obj
      R.D₁.subscheme.ringCatSheaf.property
      (Stacks.SheafOfModules.sectionsOfTop
        ((Scheme.Modules.pullback R.D₁.subschemeι).obj ((Scheme.Modules.pullback R.p).obj L₂))
        (AlgebraicGeometry.pullbackGlobalSections R.D₁.subschemeι
          ((Scheme.Modules.pullback R.p).obj L₂) R.s₂)) := by
  let : AlgebraicGeometry.SheafOfModules.IsInvertible R.total.sheaf.obj
      R.total.ringCatSheaf.property ((Scheme.Modules.pullback R.p).obj L₂) :=
    Stacks.Divisors.pullback_isInvertible R.p L₂
  exact Stacks.LineBundle.isRegularSection_restrict_of_inf_eq_zeroSection R.D₁ R.D₂
    ((Scheme.Modules.pullback R.p).obj L₂) R.s₂ R.zeroScheme₂ (branchSituation Y L₁ L₂ s L₂)
    R.branch₁ (Scheme.IdealSheafData.inclusion (le_sup_left : R.D₁ ≤ R.D₁ ⊔ R.D₂) ≫ R.p₁)
    R.intersection_isIso R.intersection_zeroSection₁

end Stacks.Chow.TensorZeroScheme

end
