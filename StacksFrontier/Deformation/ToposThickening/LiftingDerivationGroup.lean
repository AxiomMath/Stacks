module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PrincipalPartsUniversal
public import StacksFrontier.Deformation.ToposThickening.FirstOrderLiftDiagram
import StacksCore.Tactic.StacksAttribute

/-!
# The acting group of clause (2) of Stacks 08UG, in the source's own spelling

In the situation of `Deformation.ToposThickening.FirstOrderLiftDiagram` — the diagram of
[Stacks Project, Tag 08UG] reduced, as in the source's own proof, to sheaves of rings on one
site — the morphisms fitting into the diagram compatibly with `ν` form a principal homogeneous
space under the group `Deformation.ToposThickening.Derivation` of section-wise derivations out
of `O'₁`, by `Deformation.ToposThickening.FirstOrderLiftDiagram.existsUnique_translateHom`. The
source's clause (2) names the acting group differently: it is `Hom_{O₁}(Ω_{O₁/O_{B₁}}, g_*G₂)`, a
homomorphism group out of the module of relative differentials of the *reduced* structure
sheaf. This file identifies the two, and so states clause (2) with the source's group and
nothing assumed.

The identification is a descent. A derivation of the diagram is a section-wise map out of the
thickened sheaf `O'₁` rather than out of `O₁`, because the reduction `O'₁ ⟶ O₁` is only
*locally* surjective, so a map out of `O₁` is not determined section by section by its
pullback. But the reduction's section-wise kernel is exactly the ideal module `G₁`
(`LiftSquare.kernelUniversal`), which a derivation kills; so the values of a derivation at the
local lifts of a section of `O₁` form a compatible family on the image sieve of that section,
and `G₂` being a sheaf they glue. That is the content of the first section below, and it is
what turns a derivation out of `O'₁` into a relative derivation out of `O₁`. Corepresenting
the relative derivations by `Ω_{O₁/O_{B₁}}` (**Stacks 04BL**) then gives the source's group.

## Main definitions

* `Deformation.ToposThickening.FirstOrderLiftDiagram.pushedIdeal`: `g_*G₂`, the ideal module of
  the back layer read over the front structure sheaf through `g`; the underlying topoi being
  identified, this is the source's pushforward.
* `Deformation.ToposThickening.FirstOrderLiftDiagram.descDerivation` and
  `Deformation.ToposThickening.FirstOrderLiftDiagram.derivationOfRelative`: the two directions
  of the identification, the second being composition with the reduction and the first its
  descent.
* `Deformation.ToposThickening.differentialsHomAddEquiv`: **Stacks 04BL** as an additive
  identification, `Hom(Ω_{O₂/O₁}, F) = Der_{O₁}(O₂, F)`.
* `Deformation.ToposThickening.FirstOrderLiftDiagram.frontDifferentials`: `Ω_{O₁/O_{B₁}}`.
* `Deformation.ToposThickening.FirstOrderLiftDiagram.translateHom`: translation of a morphism
  fitting into the diagram by a homomorphism `Ω_{O₁/O_{B₁}} ⟶ g_*G₂`.

## Main results

* `Deformation.ToposThickening.existsUnique_descendSection`: the descent lemma. A section-wise
  additive map into a sheaf of modules, natural in the object of the site and vanishing on the
  section-wise kernel of a locally surjective morphism `red : O' ⟶ O`, determines a unique
  section over each section of `O`, namely the one restricting to its value at every local
  lift.
* `Deformation.ToposThickening.FirstOrderLiftDiagram.relativeEquivDerivation`: the
  identification of the acting group, `Der_{O_{B₁}}(O₁, g_*G₂) = Derivation`, and
  `Deformation.ToposThickening.FirstOrderLiftDiagram.derivationEquivDifferentialsHom`, its
  composite with **Stacks 04BL**: `Derivation = Hom_{O₁}(Ω_{O₁/O_{B₁}}, g_*G₂)`.
* `Deformation.ToposThickening.FirstOrderLiftDiagram.translateHom_zero`,
  `Deformation.ToposThickening.FirstOrderLiftDiagram.translateHom_add` and
  `Deformation.ToposThickening.FirstOrderLiftDiagram.existsUnique_translateHom`: **Stacks 08UG**,
  clause (2), with the source's own acting group and nothing assumed.

## Implementation notes

The descent lemma is stated and proved by hand — amalgamate over the image sieve of a section,
get well-definedness from the vanishing on the kernel, get uniqueness from separatedness —
rather than through sheafification. It is the same three-step argument as
`Stacks.BilinearMap.existsUnique_extend`, but that one needs the comparison morphism to be
locally *injective* and the reduction is not: its kernel is the whole ideal module. What
replaces local injectivity here is `Deformation.ToposThickening.eq_of_red_eq`, which is
section-wise and stronger.

`g_*G₂` is written twice, as a sheaf of modules (`pushedIdeal`, the form in which the
homomorphism group out of `Ω` is taken) and as a presheaf of modules over
`O₁ ⋙ forget₂ CommRingCat RingCat` (`pushedPresheaf`, the form in which relative derivations
are taken). The two are the same object; the second ascription exists because the ring
presheaf of the first is spelled `(Stacks.commRingSheafToRingSheaf O₁).obj`, which unification
does not put into the shape `PresheafOfModules.Derivation'` matches.

Universes. The descent and the identification `relativeEquivDerivation` are stated in the
file's general universes. The passage to `Ω_{O₁/O_{B₁}}` is not: `moduleOfDifferentialsOfSite`
corepresents derivations with values in `SheafOfModules.{max u v w m}`, so the module universe
must absorb the two site universes, and the last section accordingly reads the diagram at ring
universe `max u v w`. This is the restriction of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PrincipalPartsUniversal.lean` and is forced
there, not chosen here.

### Scope

This file is about clause (2) only. It says nothing about clause (1), and in particular does
not construct the bijection of Steps 1 to 3 of the source's proof between the morphisms
fitting into the diagram and the factorizations of the difference homomorphism `xi` through
the degree `0` term of `NL(α)`: that bijection is read off the presentation `O_{B'₁}[E] ↠ O₁`
of Step 1. The descent along `I' ↠ I` that Step 1 performs is available —
`Stacks.Sites.Conormal.existsUnique_descend_conormalDifference` in
`StacksFrontier/CategoryTheory/Sites/Modules/FreeAlgebraConormalDescent.lean` — but the
presentation of `E = O'₁ ×_{O₂} O'₂`, the two algebra maps out of `O_{B'₁}[E]` and Steps 2
and 3 are not, as the implementation notes of
`StacksFrontier/CategoryTheory/Sites/Modules/ConormalIdealRestriction.lean` record. The acting
group identified here is the *first* of the three groups of the source's display, the one
mentioning no pullback; its further identification with `Hom_{O₂}(g^*Ω_{O₁/O_{B₁}}, G₂)` and
with an `Ext⁰` group — which the source calls immediate from the definitions — is the
ringed-space
`StacksFrontier/Deformation/RingedSpaceThickening/NaiveCotangentActingGroup.lean`. In particular
the source's `Lg^*` versus the degreewise `g^*` of that file is not a question clause (2)
depends on here: the group proved to act is one the source names, and no pullback occurs in
it.

## References

* [Stacks Project, Tag 08UG](https://stacks.math.columbia.edu/tag/08UG)
* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8), the ringed-space twin
* [Stacks Project, Tag 04BL](https://stacks.math.columbia.edu/tag/04BL), the corepresentability
  of relative derivations
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u w u₂ v₂ u₃ v₃

namespace Deformation.ToposThickening

section Descent

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {P : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat.{w} RingCat.{w})}

/-- Two sections of a sheaf of modules agreeing after restriction along every arrow of a
covering sieve are equal. -/
public theorem eq_of_locally_eq (hP : Presheaf.IsSheaf J P.presheaf) {U : Cᵒᵖ}
    (S : Sieve U.unop) (hS : S ∈ J U.unop) (t₁ t₂ : P.obj U)
    (h : ∀ ⦃V : C⦄ (f : V ⟶ U.unop), S f → P.map f.op t₁ = P.map f.op t₂) :
    t₁ = t₂ :=
  hP.isSeparated _ S hS t₁ t₂ (fun _V f hf => h f hf)

variable {O' : Cᵒᵖ ⥤ CommRingCat.{w}} (red : O' ⟶ O)
  (δ : ∀ U : Cᵒᵖ, O'.obj U → P.obj U)

/-- A section-wise additive map killing the kernel of `red` does not distinguish two local
sections with the same image. -/
public theorem eq_of_red_eq
    (hadd : ∀ (U : Cᵒᵖ) (x y : O'.obj U), δ U (x + y) = δ U x + δ U y)
    (hker : ∀ (U : Cᵒᵖ) (x : O'.obj U), red.app U x = 0 → δ U x = 0)
    (U : Cᵒᵖ) (x y : O'.obj U) (hxy : red.app U x = red.app U y) :
    δ U x = δ U y := by
  have hsub : δ U (x - y) = 0 := by
    refine hker U _ ?_
    rw [map_sub, hxy, sub_self]
  have key : δ U (x - y) = δ U x - δ U y :=
    (AddMonoidHom.mk' (δ U) (hadd U)).map_sub x y
  rw [hsub] at key
  exact sub_eq_zero.1 key.symm

variable (hP : Presheaf.IsSheaf J P.presheaf)
  (hsurj : Presheaf.IsLocallySurjective J red)
  (hadd : ∀ (U : Cᵒᵖ) (x y : O'.obj U), δ U (x + y) = δ U x + δ U y)
  (hnat : ∀ {U V : Cᵒᵖ} (h : U ⟶ V) (x : O'.obj U), δ V (O'.map h x) = P.map h (δ U x))
  (hker : ∀ (U : Cᵒᵖ) (x : O'.obj U), red.app U x = 0 → δ U x = 0)

include hP hsurj in
/-- Two sections of a sheaf of modules are equal as soon as they agree after restriction along
every pair of local lifts of two given sections of `O`. -/
public theorem eq_of_forall_lift₂ {U : Cᵒᵖ} (s₁ s₂ : O.obj U) (t₁ t₂ : P.obj U)
    (h : ∀ ⦃V : C⦄ (f : V ⟶ U.unop) (x₁ x₂ : O'.obj (op V)),
      red.app (op V) x₁ = O.map f.op s₁ → red.app (op V) x₂ = O.map f.op s₂ →
        P.map f.op t₁ = P.map f.op t₂) :
    t₁ = t₂ := by
  refine eq_of_locally_eq hP (Presheaf.imageSieve red s₁ ⊓ Presheaf.imageSieve red s₂)
    (J.intersection_covering (hsurj.imageSieve_mem s₁) (hsurj.imageSieve_mem s₂)) t₁ t₂ ?_
  rintro V f ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
  exact h f x₁ x₂ hx₁ hx₂

include hP hsurj hadd hnat hker in
/-- **Descent of a section-wise map along a locally surjective morphism.** A section-wise
additive map `O' ⟶ P`, natural in the object of the site and vanishing on the section-wise
kernel of `red : O' ⟶ O`, determines a unique section of the sheaf `P` over every section of
`O`: the one which restricts to the value of the map at every local lift. -/
public theorem existsUnique_descendSection (U : Cᵒᵖ) (s : O.obj U) :
    ∃! t : P.obj U, ∀ ⦃V : Cᵒᵖ⦄ (h : U ⟶ V) (x : O'.obj V),
      red.app V x = O.map h s → P.map h t = δ V x := by
  have hwd : ∀ (V : Cᵒᵖ) (x y : O'.obj V), red.app V x = red.app V y → δ V x = δ V y :=
    eq_of_red_eq red δ hadd hker
  set S := Presheaf.imageSieve red s with hSdef
  have hSmem : S ∈ J U.unop := hsurj.imageSieve_mem s
  have hPtype : Presheaf.IsSheaf J (P.presheaf ⋙ forget AddCommGrpCat.{w}) :=
    ((sheafCompose J (forget AddCommGrpCat.{w})).obj ⟨P.presheaf, hP⟩).2
  have hsf := hPtype.isSheafFor S hSmem
  have hlift : ∀ (V : C) (f : V ⟶ U.unop), S f →
      ∃ x : O'.obj (op V), red.app (op V) x = O.map f.op s := fun _ _ hf => hf
  choose x hx using hlift
  have hfam : Presieve.FamilyOfElements.Compatible
      (P := P.presheaf ⋙ forget AddCommGrpCat.{w}) (R := S.arrows)
      (fun V f hf => δ (op V) (x V f hf)) := by
    intro V₁ V₂ Z g₁ g₂ f₁ f₂ h₁ h₂ fac
    show P.map g₁.op (δ (op V₁) (x V₁ f₁ h₁)) = P.map g₂.op (δ (op V₂) (x V₂ f₂ h₂))
    rw [← hnat g₁.op, ← hnat g₂.op]
    refine hwd _ _ _ ?_
    rw [NatTrans.naturality_apply red g₁.op, NatTrans.naturality_apply red g₂.op, hx, hx,
      ← O.map_comp_apply, ← O.map_comp_apply, ← op_comp, ← op_comp, fac]
  refine ⟨hsf.amalgamate _ hfam, ?_, ?_⟩
  · intro V h x₀ hx₀
    have hmem : S h.unop := ⟨x₀, hx₀⟩
    have key : P.map h (hsf.amalgamate _ hfam) = δ (op V.unop) (x V.unop h.unop hmem) :=
      hsf.isAmalgamation hfam h.unop hmem
    rw [key]
    exact hwd _ _ _ ((hx _ h.unop hmem).trans hx₀.symm)
  · intro t ht
    refine eq_of_locally_eq hP S hSmem t _ ?_
    intro V f hf
    rw [ht f.op (x V f hf) (hx V f hf)]
    exact (hsf.isAmalgamation hfam f hf).symm

end Descent

/-! ### Relative derivations as homomorphisms out of the module of differentials -/

section Differentials

open AlgebraicGeometry.SheafOfModules
  (moduleOfDifferentialsOfSite universalDerivationOfSite existsUnique_descDerivation)

universe m

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (O₁ O₂ : Sheaf J CommRingCat.{w}) (φ : O₁ ⟶ O₂)

/-- **Stacks 04BL as an additive identification.** Postcomposition with the universal
derivation identifies the homomorphisms `Ω_{𝒪₂/𝒪₁} ⟶ ℱ` of sheaves of modules with the
relative derivations of `𝒪₂` over `𝒪₁` with values in `ℱ`. -/
public noncomputable def differentialsHomAddEquiv
    (F : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂)) :
    (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ ⟶ F) ≃+ F.val.Derivation' φ.hom where
  toFun f := (universalDerivationOfSite.{v, u, w, m} O₁ O₂ φ).postcomp f.val
  invFun d := (existsUnique_descDerivation.{v, u, w, m} O₁ O₂ φ F d).choose
  left_inv f :=
    ((existsUnique_descDerivation.{v, u, w, m} O₁ O₂ φ F
      ((universalDerivationOfSite.{v, u, w, m} O₁ O₂ φ).postcomp f.val)).choose_spec.2
        f rfl).symm
  right_inv d := (existsUnique_descDerivation.{v, u, w, m} O₁ O₂ φ F d).choose_spec.1
  map_add' f g := by
    refine PresheafOfModules.Derivation.ext ?_
    exact funext fun U => AddMonoidHom.ext fun x => rfl

end Differentials

/-! ### Derivations of the diagram as relative derivations of the reduced structure sheaf -/

section Acting

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

namespace FirstOrderLiftDiagram

/-- `g_*𝒢₂`, the ideal module of the back layer of the diagram read as a module over the front
reduced structure sheaf through the comparison `g`. The underlying topoi being identified, this
is the source's pushforward `g_*𝒢₂`. -/
public noncomputable abbrev pushedIdeal (D : FirstOrderLiftDiagram J) :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf D.front.O) :=
  (SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map D.g)).obj D.back.G

/-- `g_*𝒢₂` as a presheaf of modules over the front reduced structure sheaf, in the spelling
in which the relative derivations of that sheaf are taken. -/
public noncomputable abbrev pushedPresheaf (D : FirstOrderLiftDiagram J) :
    PresheafOfModules.{w} (D.front.O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}) :=
  (pushedIdeal D).val

variable {D : FirstOrderLiftDiagram J} (δ : Derivation D.toSituation)

/-- The underlying section-wise map of a derivation of the diagram, with values read in
`g_*𝒢₂`: the module of the back layer and its restriction of scalars along `g` have the same
sections. -/
public noncomputable def pushedFun (U : Cᵒᵖ) (x : D.front.O'.obj.obj U) :
    (pushedPresheaf D).obj U :=
  δ.toFun U x

/-- The section-wise map of a derivation is additive. -/
public theorem pushedFun_add (U : Cᵒᵖ) (x y : D.front.O'.obj.obj U) :
    pushedFun δ U (x + y) = pushedFun δ U x + pushedFun δ U y :=
  δ.map_add' U x y

/-- The section-wise map of a derivation commutes with the restriction maps. -/
public theorem pushedFun_naturality {U V : Cᵒᵖ} (h : U ⟶ V) (x : D.front.O'.obj.obj U) :
    pushedFun δ V (D.front.O'.obj.map h x) = (pushedPresheaf D).map h (pushedFun δ U x) :=
  δ.naturality h x

/-- A derivation of the diagram vanishes on every section killed by the reduction: the
section-wise kernel of the reduction is the ideal module, on which a derivation vanishes. -/
public theorem pushedFun_eq_zero_of_reduction_eq_zero (U : Cᵒᵖ)
    (x : D.front.O'.obj.obj U) (hx : D.front.reduction.hom.app U x = 0) :
    pushedFun δ U x = 0 := by
  obtain ⟨m, hm⟩ := D.front.exists_incl x hx
  rw [show pushedFun δ U x = pushedFun δ U (D.front.incl m) from by rw [hm]]
  exact δ.map_kernel U m

/-- A derivation of the diagram does not distinguish two sections with the same reduction. -/
public theorem pushedFun_congr (U : Cᵒᵖ) (x y : D.front.O'.obj.obj U)
    (hxy : D.front.reduction.hom.app U x = D.front.reduction.hom.app U y) :
    pushedFun δ U x = pushedFun δ U y :=
  eq_of_red_eq (P := pushedPresheaf D) D.front.reduction.hom (pushedFun δ)
    (pushedFun_add δ) (pushedFun_eq_zero_of_reduction_eq_zero δ) U x y hxy

/-- Over every section of the reduced structure sheaf there is a unique section of `g_*𝒢₂`
restricting to the value of the derivation at every local lift. -/
public theorem existsUnique_descDerivationFun (U : Cᵒᵖ) (s : D.front.O.obj.obj U) :
    ∃! t : (pushedPresheaf D).obj U, ∀ ⦃V : Cᵒᵖ⦄ (h : U ⟶ V) (x : D.front.O'.obj.obj V),
      D.front.reduction.hom.app V x = D.front.O.obj.map h s →
        (pushedPresheaf D).map h t = pushedFun δ V x :=
  existsUnique_descendSection (P := pushedPresheaf D) D.front.reduction.hom (pushedFun δ)
    (pushedIdeal D).isSheaf D.front.locallySurjective (pushedFun_add δ)
    (fun h x => pushedFun_naturality δ h x)
    (pushedFun_eq_zero_of_reduction_eq_zero δ) U s

/-- The value over a section of the reduced structure sheaf of the descent of a derivation of
the diagram. -/
public noncomputable def descDerivationFun (U : Cᵒᵖ) (s : D.front.O.obj.obj U) :
    (pushedPresheaf D).obj U :=
  (existsUnique_descDerivationFun δ U s).choose

/-- The defining property of the descent of a derivation: it restricts to the value of the
derivation at every local lift. -/
public theorem map_descDerivationFun {U V : Cᵒᵖ} (s : D.front.O.obj.obj U) (h : U ⟶ V)
    (x : D.front.O'.obj.obj V)
    (hx : D.front.reduction.hom.app V x = D.front.O.obj.map h s) :
    (pushedPresheaf D).map h (descDerivationFun δ U s) = pushedFun δ V x :=
  (existsUnique_descDerivationFun δ U s).choose_spec.1 h x hx

/-- The descent of a derivation is pinned by its defining property. -/
public theorem descDerivationFun_eq {U : Cᵒᵖ} (s : D.front.O.obj.obj U)
    (t : (pushedPresheaf D).obj U)
    (ht : ∀ ⦃V : Cᵒᵖ⦄ (h : U ⟶ V) (x : D.front.O'.obj.obj V),
      D.front.reduction.hom.app V x = D.front.O.obj.map h s →
        (pushedPresheaf D).map h t = pushedFun δ V x) :
    t = descDerivationFun δ U s :=
  (existsUnique_descDerivationFun δ U s).choose_spec.2 t ht

/-- The descent of a derivation recovers it along the reduction. -/
@[simp]
public theorem descDerivationFun_reduction (U : Cᵒᵖ) (x : D.front.O'.obj.obj U) :
    descDerivationFun δ U (D.front.reduction.hom.app U x) = pushedFun δ U x :=
  (descDerivationFun_eq δ _ (pushedFun δ U x) (fun {V} h y hy => by
    rw [← pushedFun_naturality δ h x]
    refine pushedFun_congr δ V _ y ?_
    rw [sheafHom_naturality_apply, hy])).symm

/-- The Leibniz rule for the section-wise map of a derivation, the scalars acting on `g_*𝒢₂`
through the reduction. -/
public theorem pushedFun_leibniz (U : Cᵒᵖ) (x y : D.front.O'.obj.obj U) :
    pushedFun δ U (x * y) =
      D.front.reduction.hom.app U x • pushedFun δ U y +
        D.front.reduction.hom.app U y • pushedFun δ U x :=
  δ.leibniz U x y

/-- The section-wise map of a derivation vanishes on the image of the thickened base. -/
public theorem pushedFun_base (U : Cᵒᵖ) (a : D.front.OB'.obj.obj U) :
    pushedFun δ U (D.front.f'.hom.app U a) = 0 :=
  δ.map_base U a

/-- The descent of a derivation is additive. -/
public theorem descDerivationFun_add (U : Cᵒᵖ) (s₁ s₂ : D.front.O.obj.obj U) :
    descDerivationFun δ U (s₁ + s₂) =
      descDerivationFun δ U s₁ + descDerivationFun δ U s₂ := by
  refine eq_of_forall_lift₂ (P := pushedPresheaf D) D.front.reduction.hom
    (pushedIdeal D).isSheaf D.front.locallySurjective s₁ s₂ _ _ ?_
  intro V f x₁ x₂ hx₁ hx₂
  rw [map_descDerivationFun δ (s₁ + s₂) f.op (x₁ + x₂) (by rw [map_add, hx₁, hx₂, map_add]),
    map_add, map_descDerivationFun δ s₁ f.op x₁ hx₁,
    map_descDerivationFun δ s₂ f.op x₂ hx₂, pushedFun_add]
  rfl

/-- The descent of a derivation satisfies the Leibniz rule. -/
public theorem descDerivationFun_mul (U : Cᵒᵖ) (s₁ s₂ : D.front.O.obj.obj U) :
    descDerivationFun δ U (s₁ * s₂) =
      s₁ • descDerivationFun δ U s₂ + s₂ • descDerivationFun δ U s₁ := by
  refine eq_of_forall_lift₂ (P := pushedPresheaf D) D.front.reduction.hom
    (pushedIdeal D).isSheaf D.front.locallySurjective s₁ s₂ _ _ ?_
  intro V f x₁ x₂ hx₁ hx₂
  rw [map_descDerivationFun δ (s₁ * s₂) f.op (x₁ * x₂) (by rw [map_mul, hx₁, hx₂, map_mul]),
    map_add, PresheafOfModules.map_smul, PresheafOfModules.map_smul,
    map_descDerivationFun δ s₁ f.op x₁ hx₁, map_descDerivationFun δ s₂ f.op x₂ hx₂,
    pushedFun_leibniz, hx₁, hx₂]
  rfl

/-- The descent of a derivation commutes with the restriction maps. -/
public theorem descDerivationFun_map {U V : Cᵒᵖ} (h : U ⟶ V) (s : D.front.O.obj.obj U) :
    descDerivationFun δ V (D.front.O.obj.map h s) =
      (pushedPresheaf D).map h (descDerivationFun δ U s) :=
  (descDerivationFun_eq δ _ _ (fun {W} k y hy => by
    rw [← PresheafOfModules.map_comp_apply]
    exact map_descDerivationFun δ s (h ≫ k) y
      (by rw [hy, D.front.O.obj.map_comp_apply]))).symm

/-- The descent of a derivation vanishes on the image of the base. -/
public theorem descDerivationFun_base (U : Cᵒᵖ) (a : D.front.OB.obj.obj U) :
    descDerivationFun δ U (D.front.f.hom.app U a) = 0 := by
  refine eq_of_locally_eq (P := pushedPresheaf D) (pushedIdeal D).isSheaf
    (Presheaf.imageSieve D.front.baseReduction.hom a)
    (D.front.baseLocallySurjective.imageSieve_mem a)
    (descDerivationFun δ U (D.front.f.hom.app U a)) 0 ?_
  rintro V f ⟨a', ha'⟩
  have hc : D.front.reduction.hom.app (op V) (D.front.f'.hom.app (op V) a') =
      D.front.f.hom.app (op V) (D.front.baseReduction.hom.app (op V) a') :=
    congrArg (fun k : D.front.OB' ⟶ D.front.O => k.hom.app (op V) a') D.front.comm
  have hlift : D.front.reduction.hom.app (op V) (D.front.f'.hom.app (op V) a') =
      D.front.O.obj.map f.op (D.front.f.hom.app U a) := by
    rw [hc, ha', sheafHom_naturality_apply]
  rw [map_descDerivationFun δ _ f.op _ hlift, pushedFun_base, map_zero]
  rfl

/-- **The relative derivation descending a derivation of the diagram.** A derivation of the
diagram is a section-wise map out of the *thickened* front structure sheaf `𝒪'₁`; because it
kills the ideal and the reduction `𝒪'₁ ⟶ 𝒪₁` is locally surjective with section-wise kernel
that ideal, it descends to a relative derivation of `𝒪₁` over `𝒪_{ℬ₁}` with values in
`g_*𝒢₂`. -/
public noncomputable def descDerivation :
    (pushedPresheaf D).Derivation' D.front.f.hom where
  d {U} := AddMonoidHom.mk' (descDerivationFun δ U) (descDerivationFun_add δ U)
  d_mul {U} a b := descDerivationFun_mul δ U a b
  d_map {_U _V} h s := descDerivationFun_map δ h s
  d_app {U} a := descDerivationFun_base δ U a

/-- The value of the descended relative derivation. -/
@[simp]
public theorem descDerivation_d (U : Cᵒᵖ) (s : D.front.O.obj.obj U) :
    (descDerivation δ).d (X := U) s = descDerivationFun δ U s := rfl

/-- **The derivation of the diagram attached to a relative derivation.** Composing a relative
derivation of `𝒪₁` over `𝒪_{ℬ₁}` with values in `g_*𝒢₂` with the reduction `𝒪'₁ ⟶ 𝒪₁` gives a
derivation of the diagram: the Leibniz rule and the vanishing on the ideal and on the image of
the thickened base all come from the relative derivation. -/
public noncomputable def derivationOfRelative
    (d : (pushedPresheaf D).Derivation' D.front.f.hom) : Derivation D.toSituation where
  toFun U x := d.d (D.front.reduction.hom.app U x)
  map_add' U x y := by rw [map_add, map_add]; rfl
  naturality h x := by rw [sheafHom_naturality_apply, d.d_map]; rfl
  leibniz U x y := by rw [map_mul, d.d_mul]; rfl
  map_kernel U m := by
    rw [show D.toSituation.incl m = D.front.incl m from rfl, D.front.reduction_incl, map_zero]
    rfl
  map_base U a := by
    rw [show D.toSituation.f' = D.front.f' from rfl,
      show D.front.reduction.hom.app U (D.front.f'.hom.app U a) =
        D.front.f.hom.app U (D.front.baseReduction.hom.app U a) from
        congrArg (fun k : D.front.OB' ⟶ D.front.O => k.hom.app U a) D.front.comm,
      d.d_app]
    rfl

/-- The value of the derivation attached to a relative derivation. -/
@[simp]
public theorem derivationOfRelative_toFun (d : (pushedPresheaf D).Derivation' D.front.f.hom)
    (U : Cᵒᵖ) (x : D.front.O'.obj.obj U) :
    (derivationOfRelative d).toFun U x = d.d (D.front.reduction.hom.app U x) := rfl

/-- The derivations of the diagram — the group acting on the lifts by
`Deformation.ToposThickening.FirstOrderLiftDiagram.existsUnique_translateHom` — are the relative
derivations of `𝒪₁` over `𝒪_{ℬ₁}` with values in `g_*𝒢₂`: composition with the reduction is a
bijection, with inverse the descent along it. -/
public noncomputable def relativeEquivDerivation :
    ((pushedPresheaf D).Derivation' D.front.f.hom) ≃+ Derivation D.toSituation where
  toFun := derivationOfRelative
  invFun := descDerivation
  left_inv d := by
    refine PresheafOfModules.Derivation.ext ?_
    refine funext fun U => AddMonoidHom.ext fun s => ?_
    refine (descDerivationFun_eq (derivationOfRelative d) s (d.d s) ?_).symm
    intro V h x hx
    rw [show (pushedPresheaf D).map h (d.d s) = d.d (D.front.O.obj.map h s) from
      (d.d_map h s).symm, ← hx]
    rfl
  right_inv δ := Derivation.ext_apply fun U x => descDerivationFun_reduction δ U x
  map_add' d e := Derivation.ext_apply fun U x => rfl

end FirstOrderLiftDiagram

end Acting

/-! ### Clause (2) of Stacks 08UG with the source's own acting group -/

section ActingGroup

open AlgebraicGeometry.SheafOfModules ( moduleOfDifferentialsOfSite)

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]

namespace FirstOrderLiftDiagram

variable (D : FirstOrderLiftDiagram J)

/-- `Ω_{𝒪₁/𝒪_{ℬ₁}}`, the sheaf of relative differentials of the front reduced structure sheaf
over its base. -/
public noncomputable abbrev frontDifferentials :
    SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf D.front.O) :=
  moduleOfDifferentialsOfSite.{v, u, max u v w, max u v w} D.front.OB D.front.O D.front.f

/-- The derivations of the diagram, under which the lifts form a principal homogeneous space by
`Deformation.ToposThickening.FirstOrderLiftDiagram.existsUnique_translateHom`, are the
homomorphisms `Hom_{𝒪₁}(Ω_{𝒪₁/𝒪_{ℬ₁}}, g_*𝒢₂)`. -/
@[stacks 08UG "clause (2): the identification of the acting group of \
`FirstOrderLiftDiagram.existsUnique_translateHom` with the first group of the source's display, \
Hom_{O_1}(Omega_{O_1/O_{B_1}}, g_* G_2). Nothing assumed"]
public noncomputable def derivationEquivDifferentialsHom :
    Derivation D.toSituation ≃+ (frontDifferentials D ⟶ pushedIdeal D) :=
  (relativeEquivDerivation (D := D)).symm.trans
    (differentialsHomAddEquiv.{v, u, max u v w, max u v w} D.front.OB D.front.O D.front.f
      (pushedIdeal D)).symm

/-- Translation of a lift of the diagram by a homomorphism
`Ω_{𝒪₁/𝒪_{ℬ₁}} ⟶ g_*𝒢₂`: the derivation it corresponds to acts on the lift. -/
public noncomputable def translateHom (p : D.Lift)
    (a : frontDifferentials D ⟶ pushedIdeal D) : D.Lift :=
  translate p ((derivationEquivDifferentialsHom D).symm a)

/-- The formula determining translation by a homomorphism. -/
@[simp]
public theorem translateHom_eq (p : D.Lift) (a : frontDifferentials D ⟶ pushedIdeal D) :
    translateHom D p a = translate p ((derivationEquivDifferentialsHom D).symm a) := rfl

/-- The zero homomorphism acts trivially on the lifts of the diagram. -/
@[stacks 08UG "clause (2): triviality of the action of 0 in the principal homogeneous space \
structure under Hom_{O_1}(Omega_{O_1/O_{B_1}}, g_* G_2)"]
public theorem translateHom_zero (p : D.Lift) : translateHom D p 0 = p := by
  rw [translateHom_eq, map_zero, translate_zero]

/-- Translation of the lifts of the diagram is additive in the translating homomorphism. -/
@[stacks 08UG "clause (2): additivity of the action in the principal homogeneous space \
structure under Hom_{O_1}(Omega_{O_1/O_{B_1}}, g_* G_2)"]
public theorem translateHom_add (p : D.Lift) (a b : frontDifferentials D ⟶ pushedIdeal D) :
    translateHom D (translateHom D p a) b = translateHom D p (a + b) := by
  rw [translateHom_eq, translateHom_eq, translateHom_eq, translate_add, map_add]

/-- The morphisms `(Sh(𝒞'₂), 𝒪'₂) ⟶ (Sh(𝒞'₁), 𝒪'₁)` fitting into the diagram compatibly with `ν`
form a principal homogeneous space under `Hom_{𝒪₁}(Ω_{𝒪₁/𝒪_{ℬ₁}}, g_*𝒢₂)`: any one of them is
carried to any other by exactly one homomorphism. -/
@[stacks 08UG "clause (2) in full, with nothing assumed: the morphisms fitting into the \
source's diagram compatibly with nu are a principal homogeneous space under the source's own \
acting group Hom_{O_1}(Omega_{O_1/O_{B_1}}, g_* G_2), the underlying topoi identified as in \
the source's own reduction"]
public theorem existsUnique_translateHom (p q : D.Lift) :
    ∃! a : frontDifferentials D ⟶ pushedIdeal D, translateHom D p a = q := by
  have hd : ∀ (U : Cᵒᵖ) (x : D.front.O'.obj.obj U), ∃ m : D.back.G.val.obj U,
      D.back.incl m = q.hom.hom.app U x - p.hom.hom.app U x := fun U x =>
    D.back.exists_incl _ (by rw [map_sub, q.reduction_app, p.reduction_app, sub_self])
  choose diff hdiff using hd
  let δ : Derivation D.toSituation :=
    { toFun := diff
      map_add' := fun U x y => by
        refine D.back.incl_injective ?_
        rw [hdiff, D.back.incl_add, hdiff, hdiff, map_add, map_add]
        abel
      naturality := fun {U V} h x => by
        refine D.back.incl_injective ?_
        rw [hdiff, D.back.incl_naturality, hdiff, sheafHom_naturality_apply,
          sheafHom_naturality_apply]
        exact (map_sub _ _ _).symm
      leibniz := fun U x y => by
        refine D.back.incl_injective ?_
        have hqx := q.reduction_app U x
        have hpy := p.reduction_app U y
        rw [D.back.incl_add, ← hqx, ← hpy, ← D.back.mul_incl, ← D.back.mul_incl,
          hdiff, hdiff, hdiff, map_mul, map_mul]
        ring
      map_kernel := fun U m => by
        refine D.back.incl_injective ?_
        simp only [toSituation_incl]
        rw [hdiff, q.kernel_comm, p.kernel_comm, sub_self, D.back.incl_zero]
      map_base := fun U a => by
        refine D.back.incl_injective ?_
        rw [hdiff, q.base_app, p.base_app, sub_self, D.back.incl_zero] }
  have hδ : translate p δ = q := by
    refine Lift.ext (sheafHom_ext J fun U x => ?_)
    show p.hom.hom.app U x + D.back.incl (diff U x) = q.hom.hom.app U x
    rw [hdiff]
    abel
  have huniq : ∀ ε : Derivation D.toSituation, translate p ε = q → ε = δ := fun ε hε => by
    refine Derivation.ext_apply fun U x => ?_
    refine D.back.incl_injective ?_
    have h : p.hom.hom.app U x + D.back.incl (ε.toFun U x) = q.hom.hom.app U x :=
      congrArg (fun r : Lift D => r.hom.hom.app U x) hε
    show D.back.incl (ε.toFun U x) = D.back.incl (diff U x)
    rw [hdiff, ← h]
    abel
  refine ⟨derivationEquivDifferentialsHom D δ, ?_, ?_⟩
  · show translateHom D p (derivationEquivDifferentialsHom D δ) = q
    rw [translateHom_eq, AddEquiv.symm_apply_apply, hδ]
  · intro a ha
    rw [← huniq _ ha, AddEquiv.apply_symm_apply]

end FirstOrderLiftDiagram

end ActingGroup

end Deformation.ToposThickening

end
