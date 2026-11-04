module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangePullback
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentPullback
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleModuleComparisonUnivLE
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleAssociatedModuleBaseChange

/-!
# The flat base change property is preserved by inverse image (Stacks 0764 part (1))

Let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf category of a
scheme `S`, presented strictly: `f ⋙ q` is the structure functor of `𝒳`. For an étale sheaf of
`𝒪_𝒴`-modules `G`, **Stacks 075D** part (3) identifies the restriction of `f⁻¹G` at an object `y`
of `𝒳` with the restriction of `G` at `f y`, and part (4) says that under these identifications
the comparison map `c_ψ` of **Stacks 06WC** for `f⁻¹G` along an arrow `ψ` of `𝒳` is the
comparison map `c_{f ψ}` for `G`. **Stacks 0764** part (1) follows: `ψ` and `f ψ` lie over the
same morphism of schemes, so if `G` has the flat base change property of **Stacks 0762** then so
does `f⁻¹G`. Together with **Stacks 06WL** this is **Stacks 0771** part (3), that inverse image
carries `LQCoh^fbc` into `LQCoh^fbc`.

## Main results

* `PresheafOfModules.isIso_homEquiv_symm_iff_of_sections`: two comparisons with a direct image,
  along equal maps of presheaves of rings, which agree on sections under isomorphisms have mates
  which are isomorphisms together.
* `AlgebraicGeometry.Stack.restrictionPushforwardComparison_inverseImageIso_apply`:
  **Stacks 075D** part (4) for the comparison with the direct image, on sections, at every
  universe of sections.
* `AlgebraicGeometry.Stack.isIso_restrictModulePullbackComparisonUnivLE_inverseImage_iff`:
  **Stacks 075D** part (4) for modules: `c_ψ(f⁻¹G)` is an isomorphism exactly when `c_{f ψ}(G)` is.
* `AlgebraicGeometry.Stack.hasFlatBaseChangePropertyUnivLE_modulePresheafPullback` and
  `AlgebraicGeometry.Stack.hasFlatBaseChangeProperty_modulePresheafPullback`: **Stacks 0764**
  part (1).
* `AlgebraicGeometry.Stack.isLocallyQuasicoherentWithFlatBaseChange_stackInverseImage`:
  **Stacks 0771** part (3) for algebraic stacks, with nothing assumed.

## Implementation notes

The sets-level form of **Stacks 075D** part (4),
`AlgebraicGeometry.Stack.restrictionInverseImageComparison_comp_inverseImageIso`, is a square of
pullback comparisons and asks for sections in a universe above `u + 1`, where the sheaf pullback
on small étale sites exists. What the module statement needs is the mate square, of comparisons
with the direct image, read on sections; it is obtained from that theorem by the naturality of the
adjunction bijection, after lifting the sections of the module to `Type (max (u + 1) m)`, which
does not change any of the maps involved.

The comparison maps of `f⁻¹G` and of `G` are mates along the maps of structure sheaves
`a_{small}^♯` built from `𝒳` and from `𝒴`, which are not the same term; both are the structure
map of the morphism of ringed sites below the common morphism of schemes, by
`AlgebraicGeometry.Stack.smallEtaleStructureComparison_eq_smallEtaleStructureMapRing`, and the
abstract lemma about mates takes that equality as an argument.

## References

* [Stacks Project, Tag 0764](https://stacks.math.columbia.edu/tag/0764)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 075D](https://stacks.math.columbia.edu/tag/075D)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 06WL](https://stacks.math.columbia.edu/tag/06WL)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w v' w' m

namespace PresheafOfModules

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {F : C ⥤ D}
  {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}}

/-- Two pushforward comparisons, along equal maps of presheaves of rings, which agree on sections
under isomorphisms of their sources and of their targets have mates under the pullback-pushforward
adjunction which are isomorphisms together. -/
theorem isIso_homEquiv_symm_iff_of_sections {φ₁ φ₂ : S ⟶ F.op ⋙ R} (hφ : φ₁ = φ₂)
    [h₁ : (pushforward.{m} φ₁).IsRightAdjoint] [h₂ : (pushforward.{m} φ₂).IsRightAdjoint]
    {M₁ M₂ : PresheafOfModules.{m} S} {N₁ N₂ : PresheafOfModules.{m} R}
    (eM : M₁ ≅ M₂) (eN : N₁ ≅ N₂)
    (ρ₁ : M₁ ⟶ (pushforward.{m} φ₁).obj N₁) (ρ₂ : M₂ ⟶ (pushforward.{m} φ₂).obj N₂)
    (hsq : ∀ (W : Cᵒᵖ) (n : M₁.obj W),
      ρ₂.app W (eM.hom.app W n) = eN.hom.app (Opposite.op (F.obj W.unop)) (ρ₁.app W n)) :
    IsIso (((pullbackPushforwardAdjunction.{m} φ₁).homEquiv _ _).symm ρ₁) ↔
      IsIso (((pullbackPushforwardAdjunction.{m} φ₂).homEquiv _ _).symm ρ₂) := by
  subst hφ
  let adj := pullbackPushforwardAdjunction.{m} φ₁
  have hsq' : eM.hom ≫ ρ₂ = ρ₁ ≫ (pushforward.{m} φ₁).map eN.hom := by
    ext W n
    exact hsq W n
  have hmate : (pullback.{m} φ₁).map eM.hom ≫ (adj.homEquiv _ _).symm ρ₂ =
      (adj.homEquiv _ _).symm ρ₁ ≫ eN.hom := by
    apply (adj.homEquiv _ _).injective
    rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply, hsq']
  rw [← isIso_comp_right_iff _ eN.hom, ← hmate, isIso_comp_left_iff]

end PresheafOfModules

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- The comparison of Stacks 06W2 for a presheaf followed by a functor is that functor applied to
the comparison: on each small étale object both are the image of one arrow of `𝒳`. -/
theorem restrictionPushforwardComparison_comp_app {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) {x y : 𝒳} (φ : x ⟶ y)
    {A : Type*} [Category* A] {A' : Type*} [Category* A'] (F : 𝒳ᵒᵖ ⥤ A) (H : A ⥤ A')
    (W : (SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y))ᵒᵖ) :
    (restrictionPushforwardComparison B E h S hS p hp φ (F ⋙ H)).app W =
      H.map ((restrictionPushforwardComparison B E h S hS p hp φ F).app W) :=
  rfl

variable {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (q : 𝒴 ⥤ BigFppfOver B S hS) (hq : q.IsFiberedInGroupoids) (f : 𝒳 ⥤ 𝒴)
  (hp : (f ⋙ q).IsFiberedInGroupoids) (hf : (f ⋙ q).IsFibredOneMorphism q f)

/-- **Stacks 075D part (4), on sections and at every universe of sections.** The comparison of
Stacks 06W2 for an étale sheaf `F` on `𝒴` along `f ψ`, precomposed with the identification of
Stacks 075D part (3) at `y`, is the comparison for `f⁻¹F` along `ψ` followed by that
identification at `y'`.

`AlgebraicGeometry.Stack.restrictionInverseImageComparison_comp_inverseImageIso` states the
square for the pullback comparisons and for sections in a universe above `u + 1`; this is its
mate, read on sections, and the universe restriction is removed by lifting the sections. -/
theorem restrictionPushforwardComparison_inverseImageIso_apply {y' y : 𝒳} (ψ : y' ⟶ y)
    (F : Sheaf (associatedTopology B S hS q (etaleTopology B)) (Type m))
    (W : (SmallEtale E (q.obj (f.obj y)).left.1 (contains_base B E h S hS q (f.obj y)))ᵒᵖ)
    (n : (restrictToSmallEtale B E h S hS (f ⋙ q) hp y (f.op ⋙ F.obj)).obj W) :
    letI : (f ⋙ q).IsFibered := hp.isFibered
    letI : q.IsFibered := hq.isFibered
    letI := (hf.isContinuous_and_isCocontinuous_inheritedTopology
      ((etaleTopology B).over (B.obj hS))).1
    (restrictionPushforwardComparison B E h S hS q hq (f.map ψ) F.obj).app W
        ((restrictToSmallEtaleInverseImageIso B E h S hS q hq f hp hf y F).hom.app W n) =
      (restrictToSmallEtaleInverseImageIso B E h S hS q hq f hp hf y' F).hom.app
        (Opposite.op ((smallEtaleBaseChange E
          (smallEtaleBaseMorphism B E h S hS (f ⋙ q) ψ)).obj W.unop))
        ((restrictionPushforwardComparison B E h S hS (f ⋙ q) hp ψ (f.op ⋙ F.obj)).app W n) := by
  classical
  let : (f ⋙ q).IsFibered := hp.isFibered
  let : q.IsFibered := hq.isFibered
  let := (hf.isContinuous_and_isCocontinuous_inheritedTopology
    ((etaleTopology B).over (B.obj hS))).1
  let Fup : Sheaf (associatedTopology B S hS q (etaleTopology B)) (Type (max (u + 1) m)) :=
    ⟨F.obj ⋙ uliftFunctor.{u + 1, m}, Presheaf.isSheaf_comp_of_isSheaf _ _ _ F.property⟩
  have thm := restrictionInverseImageComparison_comp_inverseImageIso B E h S hS q hq f hp hf
    ψ Fup
  let b := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS (f ⋙ q) ψ)
  let Jy := SmallEtale.topology E (q.obj (f.obj y)).left.1 (contains_base B E h S hS q (f.obj y))
  let Jy' := SmallEtale.topology E (q.obj (f.obj y')).left.1
    (contains_base B E h S hS q (f.obj y'))
  let : b.IsContinuous Jy Jy' :=
    smallEtaleBaseChange_isContinuous E (smallEtaleBaseMorphism B E h S hS (f ⋙ q) ψ)
  let adj := b.sheafAdjunctionContinuous (Type (max (u + 1) m)) Jy Jy'
  dsimp only at thm
  have hpush := ((adj.homEquiv_naturality_left _ _).symm.trans
    (congrArg (adj.homEquiv _ _) thm)).trans (adj.homEquiv_naturality_right _ _)
  let F'up := (f.sheafPushforwardContinuous (Type (max (u + 1) m))
    (associatedTopology B S hS (f ⋙ q) (etaleTopology B))
    (associatedTopology B S hS q (etaleTopology B))).obj Fup
  let cX : restrictToSmallEtaleSheaf B E h S hS q hq (f.obj y) Fup ⟶
      (b.sheafPushforwardContinuous (Type (max (u + 1) m)) Jy Jy').obj
        (restrictToSmallEtaleSheaf B E h S hS q hq (f.obj y') Fup) :=
    Sheaf.homEquiv.symm (restrictionPushforwardComparison B E h S hS q hq (f.map ψ) Fup.obj)
  let cI : restrictToSmallEtaleSheaf B E h S hS (f ⋙ q) hp y F'up ⟶
      (b.sheafPushforwardContinuous (Type (max (u + 1) m)) Jy Jy').obj
        (restrictToSmallEtaleSheaf B E h S hS (f ⋙ q) hp y' F'up) :=
    Sheaf.homEquiv.symm (restrictionPushforwardComparison B E h S hS (f ⋙ q) hp ψ F'up.obj)
  have hX : adj.homEquiv _ _ (restrictionInverseImageComparison B E h S hS q hq (f.map ψ) Fup) =
      cX :=
    Equiv.apply_symm_apply _ _
  have hI : adj.homEquiv _ _
      (restrictionInverseImageComparison B E h S hS (f ⋙ q) hp ψ F'up) = cI :=
    Equiv.apply_symm_apply _ _
  have hpush2 : (restrictToSmallEtaleSheafInverseImageIso B E h S hS q hq f hp hf y Fup).hom ≫
        cX = cI ≫ (b.sheafPushforwardContinuous (Type (max (u + 1) m)) Jy Jy').map
          (restrictToSmallEtaleSheafInverseImageIso B E h S hS q hq f hp hf y' Fup).hom := by
    rwa [← hX, ← hI]
  have hev := congrArg (fun k => k.hom.app W (ULift.up n)) hpush2
  dsimp only at hev
  have hev' : (restrictionPushforwardComparison B E h S hS q hq (f.map ψ) Fup.obj).app W
        ((restrictToSmallEtaleInverseImageIso B E h S hS q hq f hp hf y Fup).hom.app W
          (ULift.up n)) =
      (restrictToSmallEtaleInverseImageIso B E h S hS q hq f hp hf y' Fup).hom.app
        (Opposite.op (b.obj W.unop))
        ((restrictionPushforwardComparison B E h S hS (f ⋙ q) hp ψ (f.op ⋙ Fup.obj)).app W
          (ULift.up n)) := hev
  obtain ⟨φy, hφy, -⟩ := existsUnique_inverseImageComparisonLift B E h S hS q hq f hp y W.unop
  obtain ⟨φy', hφy', -⟩ := existsUnique_inverseImageComparisonLift B E h S hS q hq f hp y'
    (b.obj W.unop)
  have a₁ := restrictToSmallEtaleInverseImageIso_app B E h S hS q hq f hp hf y F W.unop φy
    hφy.1 hφy.2
  have a₂ := restrictToSmallEtaleInverseImageIso_app B E h S hS q hq f hp hf y Fup W.unop φy
    hφy.1 hφy.2
  have a₃ := restrictToSmallEtaleInverseImageIso_app B E h S hS q hq f hp hf y' F
    (b.obj W.unop) φy' hφy'.1 hφy'.2
  have a₄ := restrictToSmallEtaleInverseImageIso_app B E h S hS q hq f hp hf y' Fup
    (b.obj W.unop) φy' hφy'.1 hφy'.2
  dsimp only at a₁ a₂ a₃ a₄
  simp only [Opposite.op_unop] at a₁ a₂
  rw [a₂, a₄] at hev'
  rw [a₁, a₃]
  exact congrArg ULift.down hev'

variable (G : PresheafOfModules.{m} (ringStructureSheafCore B S hS q hq (etaleTopology B)
    (etaleTopology_le_topology B)).obj)
  (hG : Presheaf.IsSheaf (associatedTopology B S hS q (etaleTopology B)) G.presheaf)

/-- **Stacks 075D part (4) for modules, on sections.** The comparison of Stacks 06WC for the
inverse image `f⁻¹G` along `ψ`, followed by the identification of Stacks 075D part (3) at `y'`,
agrees on sections with that identification at `y` followed by the comparison for `G` along
`f ψ`. -/
theorem restrictModulePushforwardComparison_inverseImageIso_apply {y' y : 𝒳} (ψ : y' ⟶ y)
    (W : (SmallEtale E (q.obj (f.obj y)).left.1 (contains_base B E h S hS q (f.obj y)))ᵒᵖ)
    (n : (restrictModuleToSmallEtale B E h S hS (f ⋙ q) hp y (etaleTopology B)
      (etaleTopology_le_topology B)
      ((modulePresheafPullback.{u, v, w, v', w', m} B S hS q hq f hp).obj G)).obj W) :
    (restrictModulePushforwardComparison B E h S hS q hq (f.map ψ) (etaleTopology B)
        (etaleTopology_le_topology B) G).app W
        ((restrictModuleToSmallEtaleInverseImageIso.{u, v, w, v', w', m}
          B E h S hS q hq f hp G hG hf y).hom.app W n) =
      (restrictModuleToSmallEtaleInverseImageIso.{u, v, w, v', w', m}
          B E h S hS q hq f hp G hG hf y').hom.app
        (Opposite.op ((smallEtaleBaseChange E
          (smallEtaleBaseMorphism B E h S hS (f ⋙ q) ψ)).obj W.unop))
        ((restrictModulePushforwardComparison B E h S hS (f ⋙ q) hp ψ (etaleTopology B)
          (etaleTopology_le_topology B)
          ((modulePresheafPullback.{u, v, w, v', w', m} B S hS q hq f hp).obj G)).app W n) :=
  restrictionPushforwardComparison_inverseImageIso_apply B E h S hS q hq f hp hf ψ
    (etaleSheafOfSections.{u, v', w', m} B S hS q hq G hG) W n

include hG hf in
/-- **Stacks 075D part (4) for modules**, in the form needed for the flat base change property:
the comparison map of Stacks 06WC for `f⁻¹G` along `ψ` is an isomorphism exactly when the one
for `G` along `f ψ` is, at any module universe above that of the schemes. -/
theorem isIso_restrictModulePullbackComparisonUnivLE_inverseImage_iff [UnivLE.{u, m}]
    {y' y : 𝒳} (ψ : y' ⟶ y) :
    IsIso (restrictModulePullbackComparisonUnivLE B E h S hS (f ⋙ q) hp ψ (etaleTopology B)
        (etaleTopology_le_topology B)
        ((modulePresheafPullback.{u, v, w, v', w', m} B S hS q hq f hp).obj G)) ↔
      IsIso (restrictModulePullbackComparisonUnivLE B E h S hS q hq (f.map ψ) (etaleTopology B)
        (etaleTopology_le_topology B) G) :=
  PresheafOfModules.isIso_homEquiv_symm_iff_of_sections
    ((smallEtaleStructureComparison_eq_smallEtaleStructureMapRing B E h S hS (f ⋙ q) hp
        (etaleTopology B) (etaleTopology_le_topology B) ψ).trans
      (smallEtaleStructureComparison_eq_smallEtaleStructureMapRing B E h S hS q hq
        (etaleTopology B) (etaleTopology_le_topology B) (f.map ψ)).symm)
    (h₂ := isRightAdjoint_pushforward_smallEtaleStructureComparison_univLE.{u, v', w', m}
      B E h S hS q hq (f.map ψ) (etaleTopology B) (etaleTopology_le_topology B))
    (restrictModuleToSmallEtaleInverseImageIso.{u, v, w, v', w', m}
      B E h S hS q hq f hp G hG hf y)
    (restrictModuleToSmallEtaleInverseImageIso.{u, v, w, v', w', m}
      B E h S hS q hq f hp G hG hf y')
    _ _
    (restrictModulePushforwardComparison_inverseImageIso_apply B E h S hS q hq f hp hf G hG ψ)

include hG hf in
/-- **Stacks 0764 part (1)**, at any module universe above that of the schemes. The inverse
image of an étale sheaf of modules with the flat base change property along a strictly presented
1-morphism of categories fibred in groupoids has the flat base change property.

The comparison map of `f⁻¹G` along an arrow `ψ` is identified with the comparison map of `G` along
`f ψ` by `AlgebraicGeometry.Stack.isIso_restrictModulePullbackComparisonUnivLE_inverseImage_iff`,
and `ψ` and `f ψ` lie over the same morphism of schemes. -/
theorem hasFlatBaseChangePropertyUnivLE_modulePresheafPullback [UnivLE.{u, m}]
    (hfbc : HasFlatBaseChangePropertyUnivLE B E h S hS q hq (etaleTopology B)
      (etaleTopology_le_topology B) G) :
    HasFlatBaseChangePropertyUnivLE B E h S hS (f ⋙ q) hp (etaleTopology B)
      (etaleTopology_le_topology B)
      ((modulePresheafPullback.{u, v, w, v', w', m} B S hS q hq f hp).obj G) :=
  fun ψ hflat =>
    (isIso_restrictModulePullbackComparisonUnivLE_inverseImage_iff B E h S hS q hq f hp hf G hG
      ψ).2 (hfbc (f.map ψ) hflat)

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0764 part (1)** at the module universe of the schemes, in the spelling
`AlgebraicGeometry.Stack.HasFlatBaseChangeProperty`, which is the spelling at universe `u` of
`AlgebraicGeometry.Stack.HasFlatBaseChangePropertyUnivLE`. -/
theorem hasFlatBaseChangeProperty_modulePresheafPullback
    {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
    (q : 𝒴 ⥤ BigFppfOver B S hS) (hq : q.IsFiberedInGroupoids) (f : 𝒳 ⥤ 𝒴)
    (hp : (f ⋙ q).IsFiberedInGroupoids) (hf : (f ⋙ q).IsFibredOneMorphism q f)
    (G : PresheafOfModules.{u} (ringStructureSheafCore B S hS q hq (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hG : Presheaf.IsSheaf (associatedTopology B S hS q (etaleTopology B)) G.presheaf)
    (hfbc : HasFlatBaseChangeProperty B E h S hS q hq (etaleTopology B)
      (etaleTopology_le_topology B) G) :
    HasFlatBaseChangeProperty B E h S hS (f ⋙ q) hp (etaleTopology B)
      (etaleTopology_le_topology B)
      ((modulePresheafPullback.{u, v, w, v', w', u} B S hS q hq f hp).obj G) :=
  hasFlatBaseChangePropertyUnivLE_modulePresheafPullback.{u, v, w, v', w', u}
    B E h S hS q hq f hp hf G hG hfbc

/-- **Stacks 0771 part (3)**, at the module universe of the schemes. Let `g : 𝒵 ⟶ 𝒳` be a
1-morphism of algebraic stacks over `S` and let `F` lie in `LQCoh^fbc(𝒪_𝒳)`. Then the inverse
image `g⁻¹F` lies in `LQCoh^fbc(𝒪_𝒵)`: local quasi-coherence is **Stacks 06WL** and the flat
base change property is **Stacks 0764** part (1),
`AlgebraicGeometry.Stack.hasFlatBaseChangeProperty_modulePresheafPullback`. -/
theorem isLocallyQuasicoherentWithFlatBaseChange_stackInverseImage
    {𝒵 𝒳 : AlgebraicStacks.{u, w} B S hS} (g : 𝒵 ⟶ 𝒳)
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hF : IsLocallyQuasicoherentWithFlatBaseChange B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids F) :
    IsLocallyQuasicoherentWithFlatBaseChange B E h S hS
      (CatFiberedInGroupoids.homFunctor g.hom ⋙ 𝒳.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS g.hom)
      ((stackModulePresheafPullback.{u, w, u} B S hS g).obj F) :=
  isLocallyQuasicoherentWithFlatBaseChange_stackModulePresheafPullback B E h S hS g F hF
    (hasFlatBaseChangeProperty_modulePresheafPullback B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (CatFiberedInGroupoids.homFunctor g.hom)
      (isFiberedInGroupoids_homFunctor_comp B S hS g.hom)
      (isFibredOneMorphism_homFunctor_comp B S hS g.hom) F hF.1.1 hF.2)

end AlgebraicGeometry.Stack
