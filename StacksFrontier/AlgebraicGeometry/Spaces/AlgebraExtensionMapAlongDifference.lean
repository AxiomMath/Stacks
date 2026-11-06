module

public import StacksFrontier.AlgebraicGeometry.Spaces.LiftDifferenceDescent
public import StacksFrontier.Deformation.AlgebraExtension.Basic

/-!
# The difference of two morphisms of extensions, as a map out of the differentials

Let `b : Y ⟶ T` be a morphism of algebraic spaces and let `P`, `Q` be extensions of
`b⁻¹𝒪_T`-algebras of `𝒪_Y` by `𝒪_Y`-modules `ℳ`, `𝒩` on the small étale site of `Y`. Two
morphisms of extensions `f, g : P ⟶ Q` along the same map `φ : ℳ ⟶ 𝒩` agree after the reduction
to `𝒪_Y`, so their sectionwise difference takes values in the square-zero ideal `𝒩`; it is a
derivation of the middle term of `P` for the action through the reduction, it kills the ideal
`ℳ` (both maps induce `φ` there) and the sections of `b⁻¹𝒪_T` (both maps are under it). So it
descends along the locally surjective reduction to a `T`-derivation `𝒪_Y ⟶ 𝒩`, that is, to an
`𝒪_Y`-linear map

`Ω_{Y/T} ⟶ 𝒩`

(`AlgebraicGeometry.Space.mapAlongDifferentialsHom`). Two morphisms of extensions with the same
difference to a third one are equal, and the difference is natural for composition with a
morphism of extensions out of `Q`.

This is the description of the automorphisms of a first order deformation in the proof of
[Stacks Project, Tag 0D1K] (the infinitesimal automorphisms are `Ext⁰(NL_{X/k}, 𝒪_X ⊗ M)`,
[Stacks Project, Tag 0D17]): an endomorphism of a deformation induces an endomorphism of its
extension, and the difference with the identity is the class in `Hom(Ω_{X/k}, 𝒪_X ⊗ M)`.

## Main definitions

* `Deformation.AlgebraExtension.MapAlong.diff`: the sectionwise difference, in `𝒩`, over any
  site.
* `Deformation.AlgebraExtension.MapAlong.quotientDerivation`: the difference as a derivation
  through the reduction.
* `AlgebraicGeometry.Space.mapAlongDerivation`: the descended `T`-derivation of `𝒪_Y`.
* `AlgebraicGeometry.Space.mapAlongDifferentialsHom`: the linear map `Ω_{Y/T} ⟶ 𝒩`.

## Main results

* `AlgebraicGeometry.Space.mapAlongDifferentialsHom_spec`: the derivation attached to the linear
  map is the descended difference.
* `AlgebraicGeometry.Space.eq_of_mapAlongDifferentialsHom_eq`: two morphisms with the same
  difference to a third one are equal.
* `AlgebraicGeometry.Space.mapAlongDifferentialsHom_comp`: the difference of the composites with a
  morphism along `ψ` is the difference followed by `ψ`.
* `AlgebraicGeometry.Space.comp_mapAlongDifferentialsHom_comp`: precomposition does not change the
  difference.

## References

* [Stacks Project, Tag 0D1K](https://stacks.math.columbia.edu/tag/0D1K)
* [Stacks Project, Tag 0D17](https://stacks.math.columbia.edu/tag/0D17)
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v w

namespace Deformation

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] {A O : Sheaf J CommRingCat.{u}}
  {a : A ⟶ O}
  {M N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)}
  {φ : M ⟶ N} {P : AlgebraExtension.{u, v, w} a M} {Q : AlgebraExtension.{u, v, w} a N}

namespace AlgebraExtension.MapAlong

variable (f g : MapAlong.{u, v, w} φ P Q)

/-- The reductions of `f x` and `g x` agree: their difference maps to zero in `O`. -/
theorem reduction_sub {U : Cᵒᵖ} (x : P.extension.obj.obj U) :
    Q.reduction.hom.app U (f.hom.hom.app U x - g.hom.hom.app U x) = 0 := by
  rw [map_sub, f.reduction_apply, g.reduction_apply, sub_self]

/-- **The sectionwise difference of two morphisms of extensions**, a section of the ideal. -/
noncomputable def diff {U : Cᵒᵖ} (x : P.extension.obj.obj U) : N.val.obj U :=
  (Q.exists_incl _ (reduction_sub f g x)).choose

/-- The inclusion of `f.diff g x` into the middle term of `Q` is `f x - g x`. -/
theorem incl_diff {U : Cᵒᵖ} (x : P.extension.obj.obj U) :
    Q.incl (f.diff g x) = f.hom.hom.app U x - g.hom.hom.app U x :=
  (Q.exists_incl _ (reduction_sub f g x)).choose_spec

/-- A section of `N` whose inclusion into the middle term of `Q` is `f x - g x` is
`f.diff g x`. -/
theorem diff_eq {U : Cᵒᵖ} (x : P.extension.obj.obj U) (n : N.val.obj U)
    (h : Q.incl n = f.hom.hom.app U x - g.hom.hom.app U x) : f.diff g x = n :=
  Q.incl_injective ((f.incl_diff g x).trans h.symm)

/-- The difference vanishes on `0`. -/
theorem diff_zero {U : Cᵒᵖ} : f.diff g (0 : P.extension.obj.obj U) = 0 :=
  f.diff_eq g _ _ (Q.incl_zero.trans (by rw [map_zero, map_zero, sub_self]))

/-- The difference is additive. -/
theorem diff_add {U : Cᵒᵖ} (x y : P.extension.obj.obj U) :
    f.diff g (x + y) = f.diff g x + f.diff g y :=
  f.diff_eq g _ _ (by
    rw [Q.incl_add, incl_diff, incl_diff, map_add, map_add]
    abel)

/-- The Leibniz rule for the difference, for the action through the reduction of `P`. -/
theorem diff_mul {U : Cᵒᵖ} (x y : P.extension.obj.obj U) :
    f.diff g (x * y) = scalar (P.reduction.hom.app U x) • f.diff g y +
      scalar (P.reduction.hom.app U y) • f.diff g x :=
  f.diff_eq g _ _ (by
    have h0 := Q.incl_mul_incl (f.diff g x) (f.diff g y)
    rw [incl_diff, incl_diff] at h0
    rw [Q.incl_add, ← f.reduction_apply x, ← f.reduction_apply y, ← Q.mul_incl, ← Q.mul_incl,
      incl_diff, incl_diff, map_mul, map_mul]
    linear_combination h0)

/-- The difference commutes with restriction. -/
theorem diff_map {U V : Cᵒᵖ} (h : U ⟶ V) (x : P.extension.obj.obj U) :
    f.diff g (P.extension.obj.map h x) = N.val.map h (f.diff g x) :=
  f.diff_eq g _ _ (by
    refine (Q.incl_naturality h (f.diff g x)).trans ?_
    rw [incl_diff, map_sub]
    exact congrArg₂ (· - ·) (NatTrans.naturality_apply f.hom.hom h x).symm
      (NatTrans.naturality_apply g.hom.hom h x).symm)

/-- The difference vanishes on the ideal `M` of `P`. -/
theorem diff_incl {U : Cᵒᵖ} (m : M.val.obj U) : f.diff g (P.incl m) = 0 :=
  f.diff_eq g _ _ (by rw [Q.incl_zero, f.kernel_comm, g.kernel_comm, sub_self])

/-- The difference vanishes on the sections of `A`. -/
theorem diff_algebraMap {U : Cᵒᵖ} (r : A.obj.obj U) :
    f.diff g (P.algebraMap.hom.app U r) = 0 :=
  f.diff_eq g _ _ (by rw [Q.incl_zero, f.algebraMap_apply, g.algebraMap_apply, sub_self])

/-- The reduction of an extension, as a morphism of sheaves of rings. -/
abbrev ringReduction (P : AlgebraExtension.{u, v, w} a M) :
    (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj P.extension ⟶
      (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O :=
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map P.reduction

/-- **The difference as a derivation through the reduction**: additive, Leibniz for the action
through the reduction, compatible with restriction and zero on the ideal `ℳ`. -/
noncomputable def quotientDerivation : Stacks.Sites.QuotientDerivation (ringReduction P) N where
  d {U} :=
    { toFun := fun x => f.diff g (U := U) x
      map_zero' := f.diff_zero g
      map_add' := f.diff_add g }
  d_mul {U} x y := f.diff_mul g x y
  d_map {U V} h x := f.diff_map g h x
  d_eq_zero_of_app_eq_zero {U} x hx := by
    obtain ⟨m, rfl⟩ := P.exists_incl x hx
    exact f.diff_incl g m

/-- The derivation `f.quotientDerivation g` is the sectionwise difference. -/
theorem quotientDerivation_d {U : Cᵒᵖ} (x : P.extension.obj.obj U) :
    (f.quotientDerivation g).d x = f.diff g x :=
  rfl

/-- The reduction of an extension is locally surjective. -/
instance isLocallySurjective_ringReduction (P : AlgebraExtension.{u, v, w} a M) :
    Sheaf.IsLocallySurjective (ringReduction P) where
  imageSieve_mem {_U} y :=
    haveI := P.locallySurjective
    Presheaf.imageSieve_mem J P.reduction.hom y

/-- **The difference is natural for postcomposition**, sectionwise. -/
theorem diff_comp
    {L : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)}
    {ψ : N ⟶ L} {χ : M ⟶ L} {R : AlgebraExtension.{u, v, w} a L}
    (h : MapAlong.{u, v, w} ψ Q R) (hχ : φ ≫ ψ = χ) {U : Cᵒᵖ} (x : P.extension.obj.obj U) :
    (f.comp h hχ).diff (g.comp h hχ) x = ψ.val.app U (f.diff g x) :=
  (f.comp h hχ).diff_eq (g.comp h hχ) _ _ (by
    rw [← h.kernel_comm, incl_diff, map_sub]
    rfl)

/-- **The difference is natural for precomposition**, sectionwise. -/
theorem comp_diff_comp
    {M' : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)}
    {χ : M' ⟶ M} {χ' : M' ⟶ N} {P' : AlgebraExtension.{u, v, w} a M'}
    (k : MapAlong.{u, v, w} χ P' P) (hχ : χ ≫ φ = χ') {U : Cᵒᵖ} (x : P'.extension.obj.obj U) :
    (k.comp f hχ).diff (k.comp g hχ) x = f.diff g (k.hom.hom.app U x) :=
  (k.comp f hχ).diff_eq (k.comp g hχ) _ _ (f.incl_diff g _)

end AlgebraExtension.MapAlong

end Deformation

namespace AlgebraicGeometry.Space

open Deformation Deformation.AlgebraExtension

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Y T : AlgebraicSpaces B S hS} (b : Y ⟶ T)
  {M N : Modules.{u, u} B S hS Y.1 Y.2} {φ : M ⟶ N}
  {P : AlgebraExtension.{u, u + 1, u} (J := SmallEtale.topology B S hS Y.1)
    (structureSharpInverseImage B S hS b) M}
  {Q : AlgebraExtension.{u, u + 1, u} (J := SmallEtale.topology B S hS Y.1)
    (structureSharpInverseImage B S hS b) N}
  (f g : MapAlong.{u, u + 1, u} φ P Q)

/-- The reduction of an extension on the small étale site is locally surjective. -/
instance isLocallySurjective_ringReduction_smallEtale
    (P : AlgebraExtension.{u, u + 1, u} (J := SmallEtale.topology B S hS Y.1)
      (structureSharpInverseImage B S hS b) M) :
    Sheaf.IsLocallySurjective (MapAlong.ringReduction P) where
  imageSieve_mem {_U} y :=
    haveI := P.locallySurjective
    Presheaf.imageSieve_mem _ P.reduction.hom y

/-- The descended difference kills the sections read from `T`: both morphisms are under
`b⁻¹𝒪_T`. -/
theorem mapAlong_descend_eq_zero (V : (SmallEtale B S hS Y.1)ᵒᵖ)
    (s : (inverseImageStructureSheaf B S hS b).obj.obj V) :
    (f.quotientDerivation g).descend ((structureSharpInverseImage B S hS b).hom.app V s) = 0 :=
  (congrArg (f.quotientDerivation g).descend (P.reduction_algebraMap s).symm).trans
    (((f.quotientDerivation g).descend_app (P.algebraMap.hom.app V s)).trans
      (f.diff_algebraMap g s))

/-- **The difference of two morphisms of extensions, as a `T`-derivation of `𝒪_Y`** with
values in the ideal `𝒩`. -/
def mapAlongDerivation : PresheafOfModulesOfCommRing.Derivation' N.val (structureSharpInverseImage B S hS b).hom :=
  @descendedDerivation B S hS Y T b _ _ (isLocallySurjective_ringReduction_smallEtale B S hS b P) N
    (f.quotientDerivation g) (mapAlong_descend_eq_zero B S hS b f g)

/-- On the reduction of a section of the middle term, the derivation is the sectionwise
difference. -/
theorem mapAlongDerivation_d_reduction {U : (SmallEtale B S hS Y.1)ᵒᵖ}
    (x : P.extension.obj.obj U) :
    (mapAlongDerivation B S hS b f g).d (P.reduction.hom.app U x) = f.diff g x :=
  (f.quotientDerivation g).descend_app x

/-- **The difference of two morphisms of extensions, as a linear map `Ω_{Y/T} ⟶ 𝒩`**: the map
corepresenting `AlgebraicGeometry.Space.mapAlongDerivation`. -/
def mapAlongDifferentialsHom : sheafOfDifferentials B S hS b ⟶ N :=
  (universalDerivation_isUniversal B S hS b N (mapAlongDerivation B S hS b f g)).choose

/-- The derivation attached to `AlgebraicGeometry.Space.mapAlongDifferentialsHom` is the
descended difference. -/
theorem mapAlongDifferentialsHom_spec :
    (universalDerivation B S hS b).postcomp (mapAlongDifferentialsHom B S hS b f g).val =
      mapAlongDerivation B S hS b f g :=
  (universalDerivation_isUniversal B S hS b N (mapAlongDerivation B S hS b f g)).choose_spec.1

/-- `AlgebraicGeometry.Space.mapAlongDifferentialsHom` is the only linear map whose attached
derivation is the descended difference. -/
theorem eq_mapAlongDifferentialsHom (θ : sheafOfDifferentials B S hS b ⟶ N)
    (hθ : (universalDerivation B S hS b).postcomp θ.val = mapAlongDerivation B S hS b f g) :
    θ = mapAlongDifferentialsHom B S hS b f g :=
  (universalDerivation_isUniversal B S hS b N (mapAlongDerivation B S hS b f g)).unique hθ
    (mapAlongDifferentialsHom_spec B S hS b f g)

/-- Two morphisms of extensions whose descended derivations relative to a third one agree
agree on every section of the middle term. -/
theorem mapAlong_hom_app_eq_of_mapAlongDerivation_eq (f₁ f₂ g : MapAlong.{u, u + 1, u} φ P Q)
    (hD : mapAlongDerivation B S hS b f₁ g = mapAlongDerivation B S hS b f₂ g)
    {U : (SmallEtale B S hS Y.1)ᵒᵖ} (x : P.extension.obj.obj U) :
    f₁.hom.hom.app U x = f₂.hom.hom.app U x := by
  have hx : f₁.diff g x = f₂.diff g x :=
    (mapAlongDerivation_d_reduction B S hS b f₁ g x).symm.trans
      ((congrArg (fun D : PresheafOfModulesOfCommRing.Derivation' N.val (structureSharpInverseImage B S hS b).hom =>
        D.d (P.reduction.hom.app U x)) hD).trans (mapAlongDerivation_d_reduction B S hS b f₂ g x))
  exact sub_left_injective ((f₁.incl_diff g x).symm.trans ((congrArg Q.incl hx).trans
    (f₂.incl_diff g x)))

/-- **Two morphisms of extensions with the same difference to a third one are equal.** -/
theorem eq_of_mapAlongDifferentialsHom_eq (f₁ f₂ g : MapAlong.{u, u + 1, u} φ P Q)
    (h : mapAlongDifferentialsHom B S hS b f₁ g = mapAlongDifferentialsHom B S hS b f₂ g) :
    f₁ = f₂ := by
  have hD : mapAlongDerivation B S hS b f₁ g = mapAlongDerivation B S hS b f₂ g := by
    rw [← mapAlongDifferentialsHom_spec, ← mapAlongDifferentialsHom_spec, h]
  refine MapAlong.ext.{u, u + 1, u} ?_
  refine Sheaf.hom_ext ?_
  refine NatTrans.ext (funext fun U => ?_)
  exact ConcreteCategory.hom_ext _ _
    (mapAlong_hom_app_eq_of_mapAlongDerivation_eq B S hS b f₁ f₂ g hD (U := U))

/-- Two `b⁻¹𝒪_T`-derivations of `𝒪_Y`, one with values in `ℒ` and one in `𝒩`, are related by
a linear map `𝒩 ⟶ ℒ` as soon as they are on the reductions of sections of the middle term of
an extension. -/
private theorem derivation_d_eq_of_reduction {L : Modules.{u, u} B S hS Y.1 Y.2} (F : N ⟶ L)
    (D₁ : PresheafOfModulesOfCommRing.Derivation' L.val (structureSharpInverseImage B S hS b).hom)
    (D₂ : PresheafOfModulesOfCommRing.Derivation' N.val (structureSharpInverseImage B S hS b).hom)
    (h : ∀ {U : (SmallEtale B S hS Y.1)ᵒᵖ} (x : P.extension.obj.obj U),
      D₁.d (P.reduction.hom.app U x) = F.val.app U (D₂.d (P.reduction.hom.app U x)))
    (U : (SmallEtale B S hS Y.1)ᵒᵖ) (t : (structureRingSheaf B S hS Y).obj.obj U) :
    D₁.d t = F.val.app U (D₂.d t) := by
  have := P.locallySurjective
  have hsep : Presheaf.IsSeparated (SmallEtale.topology B S hS Y.1) L.val.presheaf :=
    L.isSheaf.isSeparated
  let t' : (smallEtaleRingedTopos B S hS Y).O.obj.obj U := t
  refine hsep U.unop (Presheaf.imageSieve P.reduction.hom t')
    (Presheaf.imageSieve_mem (SmallEtale.topology B S hS Y.1) P.reduction.hom t') _ _ ?_
  rintro V i ⟨x, hx⟩
  have e3 := PresheafOfModules.naturality_apply F.val i.op (D₂.d t)
  refine (D₁.d_map i.op t).symm.trans (Eq.trans ?_
    ((congrArg (F.val.app _) (D₂.d_map i.op t)).trans e3))
  exact (congrArg D₁.d hx.symm).trans ((h x).trans (congrArg (F.val.app _) (congrArg D₂.d hx)))

/-- **The difference is natural for postcomposition**: composing both morphisms with a morphism
of extensions along `ψ : 𝒩 ⟶ ℒ` composes the difference with `ψ`. -/
theorem mapAlongDifferentialsHom_comp {L : Modules.{u, u} B S hS Y.1 Y.2} {ψ : N ⟶ L}
    {χ : M ⟶ L} {R : AlgebraExtension.{u, u + 1, u} (J := SmallEtale.topology B S hS Y.1)
      (structureSharpInverseImage B S hS b) L}
    (h : MapAlong.{u, u + 1, u} ψ Q R) (hχ : φ ≫ ψ = χ) :
    mapAlongDifferentialsHom B S hS b (f.comp h hχ) (g.comp h hχ) =
      mapAlongDifferentialsHom B S hS b f g ≫ ψ := by
  refine (eq_mapAlongDifferentialsHom B S hS b _ _ _ ?_).symm
  have key := derivation_d_eq_of_reduction (P := P) B S hS b ψ
    (mapAlongDerivation B S hS b (f.comp h hχ) (g.comp h hχ)) (mapAlongDerivation B S hS b f g)
    fun x => (mapAlongDerivation_d_reduction B S hS b _ _ x).trans
      ((f.diff_comp g h hχ x).trans (congrArg (ψ.val.app _)
        (mapAlongDerivation_d_reduction B S hS b f g x).symm))
  apply PresheafOfModulesOfCommRing.Derivation.ext
  ext U t
  refine Eq.trans ?_ (key _ t).symm
  have hs := congrArg (fun D : PresheafOfModulesOfCommRing.Derivation' N.val (structureSharpInverseImage B S hS b).hom =>
    D.d t) (mapAlongDifferentialsHom_spec B S hS b f g)
  simp only at hs ⊢
  rw [← hs]
  rfl

/-- **The difference is natural for precomposition**: composing both morphisms with a morphism
of extensions `k : P' ⟶ P` does not change the difference. -/
theorem comp_mapAlongDifferentialsHom_comp {M' : Modules.{u, u} B S hS Y.1 Y.2} {χ : M' ⟶ M}
    {χ' : M' ⟶ N} {P' : AlgebraExtension.{u, u + 1, u} (J := SmallEtale.topology B S hS Y.1)
      (structureSharpInverseImage B S hS b) M'}
    (k : MapAlong.{u, u + 1, u} χ P' P) (hχ : χ ≫ φ = χ') :
    mapAlongDifferentialsHom B S hS b (k.comp f hχ) (k.comp g hχ) =
      mapAlongDifferentialsHom B S hS b f g := by
  refine (eq_mapAlongDifferentialsHom B S hS b _ _ _ ?_).symm
  have key := derivation_d_eq_of_reduction (P := P') B S hS b (𝟙 N)
    (mapAlongDerivation B S hS b (k.comp f hχ) (k.comp g hχ)) (mapAlongDerivation B S hS b f g)
    fun x => (mapAlongDerivation_d_reduction B S hS b _ _ x).trans
      ((f.comp_diff_comp g k hχ x).trans
        ((mapAlongDerivation_d_reduction B S hS b f g _).symm.trans
          (by rw [k.reduction_apply]; rfl)))
  apply PresheafOfModulesOfCommRing.Derivation.ext
  ext U t
  refine Eq.trans ?_ (key _ t).symm
  have hs := congrArg (fun D : PresheafOfModulesOfCommRing.Derivation' N.val (structureSharpInverseImage B S hS b).hom =>
    D.d t) (mapAlongDifferentialsHom_spec B S hS b f g)
  simp only at hs ⊢
  exact hs

end AlgebraicGeometry.Space

end
