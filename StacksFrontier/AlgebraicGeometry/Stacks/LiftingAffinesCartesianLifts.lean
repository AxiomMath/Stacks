module

public import StacksCore.CategoryTheory.FiberedInGroupoids
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.CartesianHom
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurj
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleFaithfulGeneral
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleFullGeneral
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackTwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesEtaleAmbient
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesFibredInGroupoids
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenImageSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningSchemeStack
public import StacksFrontier.CategoryTheory.Bicategory.TwoOneCategory
public import StacksFrontier.CategoryTheory.FiberedCategory.ChoiceOfPullbacks
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.LocallyGroupoid

/-!
# Smooth lifts of étale opens form a category fibred in groupoids (Stacks 0CJT)

Fix a thickening `ι : 𝒳 ⟶ 𝒳'` of algebraic stacks over `S`, an algebraic space `W` and a smooth
1-morphism `x : W ⟶ 𝒳`, and let `p : 𝒞 ⟶ W_{spaces, étale}` be the category of smooth lifts of
étale opens of `W` of **Stacks 0CJP**, `AlgebraicGeometry.Stack.EtaleSmoothLift.proj`.
**Stacks 0CJT** says that `p` is fibred in groupoids. This file proves it with no hypothesis beyond
those of Stacks 0CJP, as `AlgebraicGeometry.Stack.EtaleSmoothLift.isFiberedInGroupoids_proj`.

The conclusion is `CategoryTheory.Functor.IsFiberedInGroupoids`, the definition of
**Stacks 003S** itself: existence of lifts, and existence and uniqueness of fill-ins for every
pair of morphisms with a common target. Both are proved directly.

* **Existence of lifts** is the source's construction of `f^*ξ`. For `f : V ⟶ U` in the site and
  `ξ = (U, U', a, i, x', α)` over `U`, the inclusion `i` is a thickening of algebraic spaces
  (base change of `ι`, **Stacks 0BPR**). The topological invariance of the étale site along it
  — the source's **Stacks 07VW**, here the arbitrary-order **Stacks 05ZH** of the library,
  `AlgebraicGeometry.Space.essSurj_spacesBaseChange_of_isThickening` — gives an étale
  `f' : V' ⟶ U'` with `V = U ×_{U'} V'`. Then `y' = x' ∘ f'` is smooth, and pasting this
  cartesian square, read as a 2-fibre product of algebraic stacks, with `U = 𝒳 ×_{𝒳'} U'`
  gives `V = 𝒳 ×_{𝒳'} V'`.
* **Unique fill-ins** replace both halves of the source's argument: its verification that the
  chosen pullbacks are strongly cartesian, which it omits, and its proof that the fibres are
  groupoids. Given `φ : η ⟶ ξ`, `ψ : ζ ⟶ ξ` and `h` with `φ ∘ h = ψ` on the base, both
  squares `Y = U ×_{U'} Y'` and `V = U ×_{U'} V'` are cartesian
  (`AlgebraicGeometry.Stack.EtaleSmoothLift.isPullback_of_hom`), and the ambient components of
  `φ`, `ψ` are étale by **Stacks 0CJS**. So fullness of the étale base change along `U ⊂ U'`
  (`AlgebraicGeometry.Space.full_spacesBaseChange_of_isThickening`) gives the ambient
  component `h'`, and faithfulness gives its uniqueness. The comparison 2-morphism of the
  fill-in is that of `ψ` with the invertible one of `φ` cancelled.

The two inputs that the earlier registration
`AlgebraicGeometry.Stack.EtaleSmoothLift.isFiberedInGroupoids` carried as hypotheses are
corollaries here. `hiso`, the isomorphism clause of **Stacks 0CJC** read on smooth lifts, is
`AlgebraicGeometry.Stack.EtaleSmoothLift.isIso_ambient_of_isIso_base`. `hfib`, that `p` is a
fibred category (**Stacks 02XM**), is
`AlgebraicGeometry.Stack.EtaleSmoothLift.isFibredCategory_proj`.

## Main results

* `AlgebraicGeometry.Space.IsThickeningHom.exists_isPullback`,
  `AlgebraicGeometry.Space.IsThickeningHom.exists_lift_of_isPullback`,
  `AlgebraicGeometry.Space.hom_ext_of_isEtale_of_isSurjective`: **Stacks 05ZH** along a
  thickening morphism of algebraic spaces, read on cartesian squares.
* `AlgebraicGeometry.Stack.EtaleSmoothLift.isThickeningHom_inclusion`: the inclusion of a
  smooth lift is a thickening.
* `AlgebraicGeometry.Stack.EtaleSmoothLift.isPullback_of_hom`: a morphism of smooth lifts gives
  a cartesian square of algebraic spaces.
* `AlgebraicGeometry.Stack.EtaleSmoothLift.fillIn`, `fillIn_comp`: the fill-in.
* `AlgebraicGeometry.Stack.EtaleSmoothLift.exists_hom_isHomLift`: the pullback `f^*ξ`.
* `AlgebraicGeometry.Stack.EtaleSmoothLift.isFiberedInGroupoids_proj`: **Stacks 0CJT**.
* `AlgebraicGeometry.Stack.EtaleSmoothLift.isIso_ambient_of_isIso_base`,
  `isFibredCategory_proj`, `isGroupoid_fiber_proj`: the discharged hypotheses.

## Implementation notes

The 2-categorical bookkeeping, coherence of the fill-in and the transport of a 2-fibre product
along a pasting, is isolated as lemmas about an arbitrary strict bicategory
(`CategoryTheory.Bicategory.coherence_of_comp_eq`,
`CategoryTheory.Bicategory.isTwoFibreProduct_of_paste_of_eqToHom`). Rewriting works there, but
not in `AlgebraicGeometry.Stack.AlgebraicStacks`, whose 1-morphism composites are not
type-correct at implicit transparency; see
`StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesCategory`.

## References

* [Stacks Project, Tag 003S](https://stacks.math.columbia.edu/tag/003S)
* [Stacks Project, Tag 02XM](https://stacks.math.columbia.edu/tag/02XM)
* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 07VW](https://stacks.math.columbia.edu/tag/07VW)
* [Stacks Project, Tag 0CJC](https://stacks.math.columbia.edu/tag/0CJC)
* [Stacks Project, Tag 0CJP](https://stacks.math.columbia.edu/tag/0CJP)
* [Stacks Project, Tag 0CJS](https://stacks.math.columbia.edu/tag/0CJS)
* [Stacks Project, Tag 0CJT](https://stacks.math.columbia.edu/tag/0CJT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits

namespace CategoryTheory.Bicategory

/-- **Transporting a doubly whiskered 2-morphism along a commuting square of 1-morphisms.** In a
strict bicategory, if `K ≫ H' = H ≫ J` then whiskering a 2-morphism `θ` by `H'` and then `K`
agrees with whiskering it by `J` and then `H`, up to the transports along the square. -/
theorem whiskerLeft_whiskerLeft_eqToHom {𝔅 : Type*} [Bicategory 𝔅] [Bicategory.Strict 𝔅]
    {Y V Y' V' X' : 𝔅} {K : Y ⟶ Y'} {H' : Y' ⟶ V'} {H : Y ⟶ V} {J : V ⟶ V'}
    (hKH : K ≫ H' = H ≫ J) {A B' : V' ⟶ X'} (θ : A ⟶ B')
    (h₁ : H ≫ (J ≫ A) = K ≫ (H' ≫ A)) (h₂ : H ≫ (J ≫ B') = K ≫ (H' ≫ B')) :
    eqToHom h₁ ≫ K ◁ H' ◁ θ = H ◁ J ◁ θ ≫ eqToHom h₂ := by
  have e : ∀ {P Q : Y ⟶ V'} (_ : P = Q), P ◁ θ =
      eqToHom (congrArg (· ≫ A) ‹P = Q›) ≫ Q ◁ θ ≫ eqToHom (congrArg (· ≫ B') ‹P = Q›).symm := by
    intro P Q hPQ
    subst hPQ
    simp
  have e₃ := e hKH
  simp only [comp_whiskerLeft, Strict.associator_eqToIso, eqToIso.hom, eqToIso.inv,
    Category.assoc, eqToHom_trans_assoc, eqToHom_comp_iff, comp_eqToHom_iff] at e₃
  rw [e₃]
  simp

/-- **The coherence of a factor through a morphism with invertible comparison.** In a strict
bicategory, consider three 2-commutative triangles `cζ`, `cη`, `cξ` of the shape of the
coherence condition of Stacks 0CJP, a morphism `(Fφ, Φ', γφ)` from the middle one to the last
and a morphism `(G, Ψ', γψ)` from the first one to the last, both coherent. If `G = H ≫ Fφ`,
`Ψ' = H' ≫ Φ'` and `K ≫ H' = H ≫ J`, then `(H, H', γψ ∘ H'^*γφ⁻¹)` is coherent: the coherence
is the one of `(G, Ψ', γψ)` with the coherence of `(Fφ, Φ', γφ)` cancelled. -/
theorem coherence_of_comp_eq {𝔅 : Type*} [Bicategory 𝔅] [Bicategory.Strict 𝔅]
    {Y V U Y' V' U' X' : 𝔅}
    {K : Y ⟶ Y'} {J : V ⟶ V'} {I : U ⟶ U'} {H : Y ⟶ V} {Fφ : V ⟶ U} {G : Y ⟶ U}
    {H' : Y' ⟶ V'} {Φ' : V' ⟶ U'} {Ψ' : Y' ⟶ U'}
    {z' : Y' ⟶ X'} {y' : V' ⟶ X'} {x' : U' ⟶ X'}
    {Aζ : Y ⟶ X'} {Aη : V ⟶ X'} {Aξ : U ⟶ X'}
    (cζ : Aζ ⟶ K ≫ z') (cη : Aη ⟶ J ≫ y') (cξ : Aξ ⟶ I ≫ x')
    (γφ : y' ⟶ Φ' ≫ x') [IsIso γφ] (γψ : z' ⟶ Ψ' ≫ x')
    (hG : G = H ≫ Fφ) (hΨ : Ψ' = H' ≫ Φ') (hKH : K ≫ H' = H ≫ J)
    (lζη : Aζ = H ≫ Aη) (lηξ : Aη = Fφ ≫ Aξ) (lζξ : Aζ = G ≫ Aξ)
    (rφ : Fφ ≫ (I ≫ x') = J ≫ (Φ' ≫ x')) (rψ : G ≫ (I ≫ x') = K ≫ (Ψ' ≫ x'))
    (rχ : H ≫ (J ≫ y') = K ≫ (H' ≫ y')) (e₁ : Ψ' ≫ x' = H' ≫ (Φ' ≫ x'))
    (hφ : cη ≫ J ◁ γφ = eqToHom lηξ ≫ Fφ ◁ cξ ≫ eqToHom rφ)
    (hψ : cζ ≫ K ◁ γψ = eqToHom lζξ ≫ G ◁ cξ ≫ eqToHom rψ) :
    cζ ≫ K ◁ (γψ ≫ eqToHom e₁ ≫ H' ◁ inv γφ) = eqToHom lζη ≫ H ◁ cη ≫ eqToHom rχ := by
  subst hG hΨ lηξ lζη
  rw [← cancel_mono (K ◁ H' ◁ γφ)]
  simp only [Category.assoc, ← whiskerLeft_comp, IsIso.inv_hom_id, Category.comp_id,
    whiskerLeft_id]
  simp only [whiskerLeft_comp, whiskerLeft_eqToHom]
  rw [reassoc_of% hψ, whiskerLeft_whiskerLeft_eqToHom hKH γφ rχ (by rw [← Strict.assoc, ← hKH,
    Strict.assoc])]
  have hφH := congrArg (H ◁ ·) hφ
  simp only [whiskerLeft_comp, whiskerLeft_eqToHom] at hφH
  rw [reassoc_of% hφH]
  simp [comp_whiskerLeft, Strict.associator_eqToIso]

/-- **Pasting onto a strictly commuting square, with the leg and filler written out.** In a
strict bicategory, let `S` be a 2-fibre product over `(f, g)` and `T` a 2-fibre product over
`(S.snd, k)` whose filler is the transport along an equality `T.fst ≫ S.snd = T.snd ≫ k`. Then
any square with apex `T.pt`, second leg `T.snd`, first leg equal to `T.fst ≫ S.fst`, and filler
the filler of `S` whiskered by `T.fst` (up to the transports) is a 2-fibre product over
`(f, k ≫ g)`: it is the pasted rectangle of `CategoryTheory.Bicategory.isTwoFibreProduct_paste`,
written out. -/
noncomputable def isTwoFibreProduct_of_paste_of_eqToHom {𝔅 : Type*} [Bicategory 𝔅]
    [Bicategory.Strict 𝔅] {x y z t : 𝔅} {f : x ⟶ z} {g : y ⟶ z} {k : t ⟶ y}
    (S : TwoCommSq f g) (hS : IsTwoFibreProduct S) (T : TwoCommSq S.snd k)
    (hT : IsTwoFibreProduct T) (hTw : T.fst ≫ S.snd = T.snd ≫ k)
    (hTiso : T.iso.hom = eqToHom hTw) {a : T.pt ⟶ x} (ha : a = T.fst ≫ S.fst)
    (γ : a ≫ f ≅ T.snd ≫ (k ≫ g))
    (hγ : γ.hom = eqToHom (by rw [ha, Strict.assoc]) ≫ T.fst ◁ S.iso.hom ≫
      eqToHom (by rw [← Strict.assoc, hTw, Strict.assoc])) :
    IsTwoFibreProduct (⟨T.pt, a, T.snd, γ⟩ : TwoCommSq f (k ≫ g)) := by
  subst ha
  have e : γ = (S.paste T).iso := by
    ext
    rw [hγ, TwoCommSq.paste_iso_hom, hTiso]
    simp [Strict.associator_eqToIso, eqToHom_whiskerRight]
  subst e
  exact isTwoFibreProduct_paste hS hT

/-- **A whiskered inverse cancels.** In a bicategory, a 2-morphism `a`, transported and followed
by `H ◁ g⁻¹`, then by `H ◁ g` and a transport back, is `a`. -/
theorem comp_eqToHom_whiskerLeft_inv_cancel {𝔅 : Type*} [Bicategory 𝔅] {A C D : 𝔅}
    {z P : A ⟶ D} {H : A ⟶ C} {y v : C ⟶ D} (a : z ⟶ P) (e : P = H ≫ v) (g : y ⟶ v) [IsIso g]
    (e' : H ≫ v = P) :
    ((a ≫ eqToHom e ≫ H ◁ inv g) ≫ H ◁ g) ≫ eqToHom e' = a := by
  simp [← whiskerLeft_comp]

end CategoryTheory.Bicategory

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace IsThickeningHom

variable {U U' : AlgebraicSpaces B S hS} {i : U ⟶ U'}

/-- **A thickening of algebraic spaces is isomorphic to the closed subspace it cuts out.** The
isomorphism of presheaves onto the range, read in the category of algebraic spaces. -/
def isoSpace (hi : IsThickeningHom B S hS i) : U ≅ IsThickening.space B S hS hi.2 :=
  (ObjectProperty.fullyFaithfulι _).preimageIso hi.isoRange

/-- The isomorphism onto the closed subspace, followed by its inclusion, is the thickening. -/
theorem isoSpace_hom_inclusion (hi : IsThickeningHom B S hS i) :
    hi.isoSpace.hom ≫ IsThickening.inclusion B S hS hi.2 = i :=
  ObjectProperty.hom_ext _ hi.isoRange_hom_ι

/-- The square comparing the inclusion of the closed subspace cut out by a thickening with the
thickening itself, along the inverse of the isomorphism onto that subspace, is cartesian. -/
theorem isPullback_isoSpace_inv (hi : IsThickeningHom B S hS i) :
    IsPullback (𝟙 _ ≫ IsThickening.inclusion B S hS hi.2) hi.isoSpace.inv (𝟙 U') i :=
  IsPullback.of_vert_isIso ⟨by
    rw [Category.comp_id, Category.id_comp]
    exact (Iso.eq_inv_comp _).2 (isoSpace_hom_inclusion hi)⟩

/-- The square comparing a thickening with the inclusion of the closed subspace it cuts out,
along the isomorphism onto that subspace, is cartesian. -/
theorem isPullback_isoSpace_hom (hi : IsThickeningHom B S hS i) :
    IsPullback i hi.isoSpace.hom (𝟙 U') (IsThickening.inclusion B S hS hi.2) :=
  IsPullback.of_vert_isIso ⟨by rw [Category.comp_id, isoSpace_hom_inclusion]⟩

/-- **Stacks 05ZH, essential surjectivity, read on cartesian squares.** Let `i : U ⟶ U'` be a
thickening of algebraic spaces, of arbitrary order, and `f : V ⟶ U` an étale morphism. There is
an étale `f' : V' ⟶ U'` and a cartesian square `V = U ×_{U'} V'` exhibiting `f` as the base change
of `f'` along `i`.

This is `AlgebraicGeometry.Space.essSurj_spacesBaseChange_of_isThickening` for the closed
subspace cut out by `i`, transported along the isomorphism of `U` with that subspace. -/
theorem exists_isPullback (hi : IsThickeningHom B S hS i) {V : AlgebraicSpaces B S hS}
    (f : V ⟶ U) (hf : IsEtale B S hS f.hom) :
    ∃ (V' : AlgebraicSpaces B S hS) (j : V ⟶ V') (f' : V' ⟶ U'),
      IsEtale B S hS f'.hom ∧ IsPullback j f f' i := by
  let D := spacesBaseChange B S hS (IsThickening.inclusion B S hS hi.2)
  let O : SpacesEtale B S hS (IsThickening.space B S hS hi.2) :=
    ⟨Over.mk (f ≫ hi.isoSpace.hom), isEtale_comp B S hS hf (isEtale_of_isIso B S hS _)⟩
  obtain ⟨V', ⟨φ⟩⟩ := (essSurj_spacesBaseChange_of_isThickening B S hS hi.2).mem_essImage O
  have : IsIso φ.inv.hom.left :=
    inferInstanceAs (IsIso ((SpacesEtale.toSpaces B S hS _).map φ.inv))
  have h₀ : IsPullback φ.inv.hom.left (f ≫ hi.isoSpace.hom) (D.functor.obj V').1.hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact Over.w φ.inv.hom⟩
  have h₁ := (h₀.paste_horiz (D.isPullback V')).paste_vert (isPullback_isoSpace_inv hi)
  refine ⟨V'.1.left, φ.inv.hom.left ≫ D.projection.app V', V'.1.hom, V'.property, ?_⟩
  rwa [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.comp_id] at h₁

/-- **Stacks 05ZH, fullness, read on cartesian squares.** Let `i : U ⟶ U'` be a thickening of
algebraic spaces, of arbitrary order, and let `Y = U ×_{U'} Y'` and `V = U ×_{U'} V'` be
cartesian squares over étale morphisms `g' : Y' ⟶ U'` and `f' : V' ⟶ U'`. Every morphism
`h : Y ⟶ V` over `U` is the restriction of a morphism `h' : Y' ⟶ V'` over `U'`.

This is `AlgebraicGeometry.Space.full_spacesBaseChange_of_isThickening` for the closed subspace
cut out by `i`, transported along the isomorphism of `U` with that subspace and along the
comparison of each square with the chosen base change. -/
theorem exists_lift_of_isPullback (hi : IsThickeningHom B S hS i)
    {Y Y' V V' : AlgebraicSpaces B S hS} {k : Y ⟶ Y'} {g : Y ⟶ U} {g' : Y' ⟶ U'}
    (hY : IsPullback k g g' i) (hg' : IsEtale B S hS g'.hom)
    {j : V ⟶ V'} {f : V ⟶ U} {f' : V' ⟶ U'} (hV : IsPullback j f f' i)
    (hf' : IsEtale B S hS f'.hom) (h : Y ⟶ V) (hh : h ≫ f = g) :
    ∃ h' : Y' ⟶ V', h' ≫ f' = g' ∧ k ≫ h' = h ≫ j := by
  let D := spacesBaseChange B S hS (IsThickening.inclusion B S hS hi.2)
  let Ye : SpacesEtale B S hS U' := ⟨Over.mk g', hg'⟩
  let Ve : SpacesEtale B S hS U' := ⟨Over.mk f', hf'⟩
  have hY₂ := hY.paste_vert (isPullback_isoSpace_hom hi)
  have hV₂ := hV.paste_vert (isPullback_isoSpace_hom hi)
  rw [Category.comp_id] at hY₂ hV₂
  let eY := hY₂.isoIsPullback _ _ (D.isPullback Ye)
  let eV := hV₂.isoIsPullback _ _ (D.isPullback Ve)
  have hc : (eY.inv ≫ h ≫ eV.hom) ≫ (D.functor.obj Ve).1.hom = (D.functor.obj Ye).1.hom := by
    rw [Category.assoc, Category.assoc, IsPullback.isoIsPullback_hom_snd, ← Category.assoc h,
      hh, IsPullback.isoIsPullback_inv_snd]
  let c : D.functor.obj Ye ⟶ D.functor.obj Ve :=
    ObjectProperty.homMk (Over.homMk (eY.inv ≫ h ≫ eV.hom) hc)
  obtain ⟨a, ha⟩ := (full_spacesBaseChange_of_isThickening B S hS hi.2).map_surjective c
  refine ⟨a.hom.left, Over.w a.hom, ?_⟩
  have hnat' : D.projection.app Ye ≫ a.hom.left =
      (eY.inv ≫ h ≫ eV.hom) ≫ D.projection.app Ve := by
    have h₂ : (D.functor ⋙ SpacesEtale.toSpaces B S hS _).map a = eY.inv ≫ h ≫ eV.hom := by
      change (SpacesEtale.toSpaces B S hS _).map (D.functor.map a) = _
      rw [ha]
      rfl
    rw [← h₂]
    exact (D.projection.naturality a).symm
  rw [← IsPullback.isoIsPullback_hom_fst _ _ hY₂ (D.isPullback Ye), Category.assoc, hnat']
  simp only [eY, eV, Category.assoc, Iso.hom_inv_id_assoc]
  exact congrArg (h ≫ ·) (IsPullback.isoIsPullback_hom_fst _ _ hV₂ (D.isPullback Ve))

/-- **Stacks 05ZH, faithfulness, read on cartesian squares.** Two morphisms `a, b : Y' ⟶ V'`
over a space `V'` étale over `U'` which agree after restriction along a morphism `k : Y ⟶ Y'`
surjective on points are equal. This is
`AlgebraicGeometry.Space.eq_of_comp_eq_of_isSurjective`, an étale morphism being unramified. -/
theorem _root_.AlgebraicGeometry.Space.hom_ext_of_isEtale_of_isSurjective
    {Y Y' V' U' : AlgebraicSpaces B S hS} {f' : V' ⟶ U'} (hf' : IsEtale B S hS f'.hom)
    {k : Y ⟶ Y'} (hk : IsSurjective B S hS k.hom) {a b : Y' ⟶ V'} (hab : a ≫ f' = b ≫ f')
    (hka : k ≫ a = k ≫ b) : a = b :=
  ObjectProperty.hom_ext _ (eq_of_comp_eq_of_isSurjective B S hS V'.property U'.property f'.hom
    (isUnramified_of_isEtale B S hS hf') a.hom b.hom (congrArg (fun t => t.hom) hab) k.hom hk
    (congrArg (fun t => t.hom) hka))

end IsThickeningHom

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} {ι : 𝒳 ⟶ 𝒳'} {hι : IsThickening ι}
  {W : AlgebraicSpaces B S hS}
  {x : (algebraicSpaceStackFunctor B S hS).obj W ⟶ 𝒳}
  {hx : AlgebraicStacks.IsSmooth B S hS x}

namespace EtaleSmoothLift

/-- **The inclusion of a smooth lift is a thickening of algebraic spaces.** The square of a
smooth lift exhibits `U = 𝒳 ×_{𝒳'} U'`, so the 1-morphism attached to `i : U ⟶ U'` is a base
change of the thickening `ι` and hence a thickening (**Stacks 0BPR**); the morphism of
representing algebraic spaces it induces is `i`. -/
theorem isThickeningHom_inclusion (ξ : EtaleSmoothLift B S hS ι hι W x hx) :
    Space.IsThickeningHom B S hS ξ.inclusion := by
  have hth : IsThickening ((algebraicSpaceStackFunctor.{u, w} B S hS).map ξ.inclusion) :=
    isThickening_baseChange B S hS ι ξ.ambientMap _ ξ.isTwoFibreProduct hι
  have key := isThickeningHom_representingMap_of_isThickening B S hS _ hth
    ξ.base.obj.left.property ξ.ambient.property
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
  have e : (ObjectProperty.homMk (representingMap B S hS _ _ ξ.base.obj.left.obj ξ.ambient.obj
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      ((algebraicSpaceStackFunctor.{u, w} B S hS).map ξ.inclusion).hom) :
        ξ.base.obj.left ⟶ ξ.ambient) = ξ.inclusion :=
    ObjectProperty.hom_ext _ (representingMap_associatedMap B S hS _ _ ξ.inclusion.hom)
  exact e ▸ key

/-- The inclusion of a smooth lift is a monomorphism of algebraic spaces. -/
theorem mono_inclusion (ξ : EtaleSmoothLift B S hS ι hι W x hx) : Mono ξ.inclusion :=
  have := ξ.isThickeningHom_inclusion.mono
  (ObjectProperty.ι _).mono_of_mono_map this

/-- A functor sends a commuting square to a commuting square. -/
private theorem map_comp_eq_map_comp {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y Z T : C} {a : X ⟶ Y} {b : Y ⟶ T} {c : X ⟶ Z} {d : Z ⟶ T} (h : a ≫ b = c ≫ d) :
    F.map a ≫ F.map b = F.map c ≫ F.map d := by
  simp only [← F.map_comp, h]

/-- **A morphism into the ambient space of a smooth lift, over a morphism of smooth lifts,
factors through the inclusion.** Let `m : ζ ⟶ ξ` be a morphism of smooth lifts, with ambient
component `g' : Y' ⟶ U'`, and let `a : T ⟶ Y'`, `b : T ⟶ U` satisfy `g' ∘ a = i ∘ b`. Then `a`
factors through the inclusion `k : Y ⟶ Y'`, by the universal property of `Y = 𝒳 ×_{𝒳'} Y'`
applied to `x ∘ (U ⟶ W) ∘ b` and `a`, the 2-isomorphism between their images in `𝒳'` being
`α` of `ξ` composed with the inverse of the comparison `γ` of `m`. -/
theorem exists_comp_inclusion_eq {ζ ξ : EtaleSmoothLift B S hS ι hι W x hx} (m : ζ ⟶ ξ)
    {T : AlgebraicSpaces B S hS} (a : T ⟶ ζ.ambient) (b : T ⟶ ξ.base.obj.left)
    (hab : a ≫ Hom.ambient m = b ≫ ξ.inclusion) :
    ∃ t : T ⟶ ζ.base.obj.left, t ≫ ζ.inclusion = a := by
  have h₁ : (algebraicSpaceStackFunctor B S hS).map b ≫
        ((algebraicSpaceStackFunctor B S hS).map ξ.inclusion ≫ ξ.ambientMap) =
      (algebraicSpaceStackFunctor B S hS).map a ≫
        ((algebraicSpaceStackFunctor B S hS).map (Hom.ambient m) ≫ ξ.ambientMap) :=
    by rw [← Category.assoc, ← Category.assoc, map_comp_eq_map_comp _ hab.symm]
  let Q : TwoCommSq ι ζ.ambientMap :=
    ⟨(algebraicSpaceStackFunctor B S hS).obj T,
      (algebraicSpaceStackFunctor B S hS).map b ≫
        ((algebraicSpaceStackFunctor B S hS).map ξ.base.obj.hom ≫ x),
      (algebraicSpaceStackFunctor B S hS).map a,
      whiskerLeftIso ((algebraicSpaceStackFunctor B S hS).map b) ξ.comm ≪≫ eqToIso h₁ ≪≫
        whiskerLeftIso ((algebraicSpaceStackFunctor B S hS).map a) (asIso (Hom.comm m)).symm⟩
  let d := twoFibreProductPreHom ζ.isTwoFibreProduct Q
  let t : T ⟶ ζ.base.obj.left := ObjectProperty.homMk (representingMap B S hS _ _ T.obj
    ζ.base.obj.left.obj (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) d.hom.hom)
  have ht : (algebraicSpaceStackFunctor.{u, w} B S hS).map t = d.hom :=
    algebraicSpaceStackFunctor_map_homMk_representingMap d.hom
  refine ⟨t, algebraicSpaceStackFunctor_map_injective.{u, w} ?_⟩
  rw [Functor.map_comp, ht]
  exact (eq_of_hom₂_algebraicSpaceStackFunctor_obj d.isoSnd.hom).symm

/-- **A morphism of smooth lifts restricts along a cartesian square.** For a morphism
`m : ζ ⟶ ξ` of smooth lifts, from `(Y, Y', k, …)` to `(U, U', i, …)`, the square formed by the
two inclusions and the two components of `m` is cartesian: `Y = U ×_{U'} Y'`. The source deduces
this from the two 2-fibre products `Y = 𝒳 ×_{𝒳'} Y'` and `U = 𝒳 ×_{𝒳'} U'`; here the factorisation
is `AlgebraicGeometry.Stack.EtaleSmoothLift.exists_comp_inclusion_eq`, and uniqueness and the
second leg come from the two inclusions being monomorphisms. -/
theorem isPullback_of_hom {ζ ξ : EtaleSmoothLift B S hS ι hι W x hx} (m : ζ ⟶ ξ) :
    IsPullback ζ.inclusion (Hom.base m).hom.left (Hom.ambient m) ξ.inclusion := by
  have hw : ζ.inclusion ≫ Hom.ambient m = (Hom.base m).hom.left ≫ ξ.inclusion :=
    Hom.inclusion_comp m
  have := ζ.mono_inclusion
  have := ξ.mono_inclusion
  choose t ht using fun s : PullbackCone (Hom.ambient m) ξ.inclusion =>
    exists_comp_inclusion_eq m s.fst s.snd s.condition
  refine IsPullback.of_isLimit' ⟨hw⟩ (PullbackCone.IsLimit.mk hw t ht ?_ ?_)
  · intro s
    rw [← cancel_mono ξ.inclusion, Category.assoc, ← hw, ← Category.assoc, ht, s.condition]
  · intro s n hn _
    rw [← cancel_mono ζ.inclusion, hn, ht]

/-! ### Unique fill-ins -/

section FillIn

variable {ζ η ξ : EtaleSmoothLift B S hS ι hι W x hx}

/-- **The ambient component of a fill-in exists.** Given morphisms `φ : η ⟶ ξ`, `ψ : ζ ⟶ ξ` of
smooth lifts and a morphism `h` of the spaces-étale site of `W` with `φ ∘ h = ψ` on the base
components, there is `h' : Y' ⟶ V'` with `φ' ∘ h' = ψ'` restricting to `h`. The ambient
components `φ'`, `ψ'` are étale (**Stacks 0CJS**), the squares of `φ` and `ψ` are cartesian
(`AlgebraicGeometry.Stack.EtaleSmoothLift.isPullback_of_hom`), and the inclusion of `ξ` is a
thickening, so this is fullness of the étale base change along it (**Stacks 05ZH**, the source's
**Stacks 07VW**). -/
theorem exists_ambient_fillIn (φ : η ⟶ ξ) (ψ : ζ ⟶ ξ) (h : ζ.base ⟶ η.base)
    (hh : h ≫ Hom.base φ = Hom.base ψ) :
    ∃ h' : ζ.ambient ⟶ η.ambient, h' ≫ Hom.ambient φ = Hom.ambient ψ ∧
      ζ.inclusion ≫ h' = h.hom.left ≫ η.inclusion :=
  Space.IsThickeningHom.exists_lift_of_isPullback ξ.isThickeningHom_inclusion
    (isPullback_of_hom ψ) (Hom.isEtale_ambient _ _ ψ) (isPullback_of_hom φ)
    (Hom.isEtale_ambient _ _ φ) h.hom.left (congrArg (fun t => t.hom.left) hh)

/-- **The ambient component of a fill-in is unique.** Two morphisms `Y' ⟶ V'` over the étale
ambient component `φ'` of a morphism of smooth lifts which agree on the inclusion of `Y` are
equal: the inclusion is a thickening, hence surjective on points, and `φ'` is unramified. This
is faithfulness of the étale base change along the thickening (**Stacks 05ZH**). -/
theorem ambient_ext (φ : η ⟶ ξ) {a b : ζ.ambient ⟶ η.ambient}
    (hab : a ≫ Hom.ambient φ = b ≫ Hom.ambient φ) (hk : ζ.inclusion ≫ a = ζ.inclusion ≫ b) :
    a = b :=
  Space.hom_ext_of_isEtale_of_isSurjective (Hom.isEtale_ambient _ _ φ)
    ζ.isThickeningHom_inclusion.surjective_pointsMap hab hk

/-- **The fill-in, for a given ambient component.** For `φ : η ⟶ ξ`, `ψ : ζ ⟶ ξ`, `h` with
`φ ∘ h = ψ` on the base components and `h' : Y' ⟶ V'` with `φ' ∘ h' = ψ'` restricting to `h`,
the morphism `(h, h', γψ ∘ h'^*γφ⁻¹) : ζ ⟶ η`. Its coherence is that of `ψ` with the coherence
of `φ` cancelled, `CategoryTheory.Bicategory.coherence_of_comp_eq`. -/
def fillInOf (φ : η ⟶ ξ) (ψ : ζ ⟶ ξ) (h : ζ.base ⟶ η.base) (hh : h ≫ Hom.base φ = Hom.base ψ)
    (h' : ζ.ambient ⟶ η.ambient) (h₁ : h' ≫ Hom.ambient φ = Hom.ambient ψ)
    (h₂ : ζ.inclusion ≫ h' = h.hom.left ≫ η.inclusion) : ζ ⟶ η where
  base := h
  ambient := h'
  inclusion_comp := h₂
  comm := Hom.comm ψ ≫ eqToHom (congrArg (fun t => (algebraicSpaceStackFunctor B S hS).map t ≫
      ξ.ambientMap) h₁.symm) ≫ (algebraicSpaceStackFunctor B S hS).map h' ◁ inv (Hom.comm φ)
  coherence :=
    Bicategory.coherence_of_comp_eq ζ.comm.hom η.comm.hom ξ.comm.hom (Hom.comm φ) (Hom.comm ψ)
      (congrArg (fun t => (algebraicSpaceStackFunctor B S hS).map t.hom.left) hh.symm)
      (congrArg (algebraicSpaceStackFunctor B S hS).map h₁.symm) (lift_leg ζ η h _ h₂).symm
      (left_leg ζ η h) (left_leg η ξ (Hom.base φ)) (left_leg ζ ξ (Hom.base ψ))
      (right_leg η ξ (Hom.base φ) (Hom.ambient φ) (Hom.inclusion_comp φ))
      (right_leg ζ ξ (Hom.base ψ) (Hom.ambient ψ) (Hom.inclusion_comp ψ))
      (right_leg ζ η h _ h₂) _ (Hom.coherence φ) (Hom.coherence ψ)

/-- **The fill-in factors `ψ` through `φ`.** -/
theorem fillInOf_comp (φ : η ⟶ ξ) (ψ : ζ ⟶ ξ) (h : ζ.base ⟶ η.base)
    (hh : h ≫ Hom.base φ = Hom.base ψ) (h' : ζ.ambient ⟶ η.ambient)
    (h₁ : h' ≫ Hom.ambient φ = Hom.ambient ψ)
    (h₂ : ζ.inclusion ≫ h' = h.hom.left ≫ η.inclusion) :
    fillInOf φ ψ h hh h' h₁ h₂ ≫ φ = ψ := by
  refine hom_congr _ _ hh h₁ ?_
  refine heq_of_comp_eqToHom (congrArg (fun t => (algebraicSpaceStackFunctor B S hS).map t ≫
    ξ.ambientMap) h₁) _ _ ?_
  change ((Hom.comm ψ ≫ eqToHom (congrArg (fun t => (algebraicSpaceStackFunctor B S hS).map t ≫
      ξ.ambientMap) h₁.symm) ≫ (algebraicSpaceStackFunctor B S hS).map h' ◁ inv (Hom.comm φ)) ≫
    (algebraicSpaceStackFunctor B S hS).map h' ◁ Hom.comm φ) ≫ eqToHom (congrArg (fun t =>
      (algebraicSpaceStackFunctor B S hS).map t ≫ ξ.ambientMap) h₁) = Hom.comm ψ
  exact Bicategory.comp_eqToHom_whiskerLeft_inv_cancel
    (P := (algebraicSpaceStackFunctor B S hS).map (Hom.ambient ψ) ≫ ξ.ambientMap)
    (H := (algebraicSpaceStackFunctor B S hS).map h')
    (v := (algebraicSpaceStackFunctor B S hS).map (Hom.ambient φ) ≫ ξ.ambientMap)
    (Hom.comm ψ) _ (Hom.comm φ) _

/-- **The fill-in.** `AlgebraicGeometry.Stack.EtaleSmoothLift.fillInOf` at the ambient component
of `AlgebraicGeometry.Stack.EtaleSmoothLift.exists_ambient_fillIn`. -/
def fillIn (φ : η ⟶ ξ) (ψ : ζ ⟶ ξ) (h : ζ.base ⟶ η.base) (hh : h ≫ Hom.base φ = Hom.base ψ) :
    ζ ⟶ η :=
  fillInOf φ ψ h hh _ (exists_ambient_fillIn φ ψ h hh).choose_spec.1
    (exists_ambient_fillIn φ ψ h hh).choose_spec.2

/-- **The fill-in factors `ψ` through `φ`.** -/
theorem fillIn_comp (φ : η ⟶ ξ) (ψ : ζ ⟶ ξ) (h : ζ.base ⟶ η.base)
    (hh : h ≫ Hom.base φ = Hom.base ψ) : fillIn φ ψ h hh ≫ φ = ψ :=
  fillInOf_comp _ _ _ _ _ _ _

/-- **A morphism of smooth lifts into a fixed target is determined by its composite with a
morphism out of it, once its two space components are.** The comparison 2-morphism of the
composite is that of the morphism followed by an invertible one. -/
theorem hom_ext_of_comp (φ : η ⟶ ξ) {χ₁ χ₂ : ζ ⟶ η} (hb : Hom.base χ₁ = Hom.base χ₂)
    (ha : Hom.ambient χ₁ = Hom.ambient χ₂) (hc : χ₁ ≫ φ = χ₂ ≫ φ) : χ₁ = χ₂ := by
  obtain ⟨b₁, a₁, r₁, c₁, k₁⟩ := χ₁
  obtain ⟨b₂, a₂, r₂, c₂, k₂⟩ := χ₂
  dsimp only at hb ha
  subst hb ha
  have e₀ := congr_arg_heq (fun m : ζ ⟶ ξ => Hom.comm m) hc
  have e := eq_of_heq e₀
  obtain rfl : c₁ = c₂ :=
    (cancel_mono ((algebraicSpaceStackFunctor B S hS).map a₁ ◁ Hom.comm φ)).1 e
  rfl

end FillIn

/-! ### Existence of lifts -/

/-- **The pullback of a smooth lift along a morphism of the spaces-étale site.** Given a smooth
lift `ξ = (U, U', i, x', α)` and a morphism `f : V ⟶ U` of the spaces-étale site of `W`, there
is a smooth lift over `V` and a morphism to `ξ` lying over `f`. As in the source: the étale
morphism `f' : V' ⟶ U'` restricting to `f` along the thickening `i` comes from the topological
invariance of the étale site (**Stacks 05ZH**, the source's **Stacks 07VW**) through
`AlgebraicGeometry.Space.IsThickeningHom.exists_isPullback`; `y' = x' ∘ f'` is smooth, the
filler is `α` whiskered by `f`, and `V = 𝒳 ×_{𝒳'} V'` is the pasting of the cartesian square
`V = U ×_{U'} V'` with `U = 𝒳 ×_{𝒳'} U'`. The comparison 2-morphism of the morphism is an
identity. -/
theorem exists_hom_isHomLift {V : Space.SpacesEtale B S hS W}
    (ξ : EtaleSmoothLift B S hS ι hι W x hx) (f : V ⟶ ξ.base) :
    ∃ (η : EtaleSmoothLift B S hS ι hι W x hx) (φ : η ⟶ ξ),
      (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsHomLift f φ := by
  obtain ⟨V', j, f', hf', hpb⟩ := ξ.isThickeningHom_inclusion.exists_isPullback f.hom.left
    (Space.SpacesEtale.isEtale_toSpaces_map B S hS W f)
  have hTw := map_comp_eq_map_comp (algebraicSpaceStackFunctor.{u, w} B S hS) hpb.w.symm
  have hpb' := AlgebraicSpaces.isPullback_hom B S hS hpb.flip
  let T : TwoCommSq ((algebraicSpaceStackFunctor B S hS).map ξ.inclusion)
      ((algebraicSpaceStackFunctor B S hS).map f') :=
    algebraicSpaceStackSquare.{u, w} B S hS ξ.base.obj.left.property V'.property
      ξ.ambient.property V.obj.left.property hpb'.w
  have ha : (algebraicSpaceStackFunctor B S hS).map V.obj.hom ≫ x =
      (algebraicSpaceStackFunctor B S hS).map f.hom.left ≫
        ((algebraicSpaceStackFunctor B S hS).map ξ.base.obj.hom ≫ x) :=
    congrArg (· ≫ x) (show (algebraicSpaceStackFunctor.{u, w} B S hS).map V.obj.hom =
      (algebraicSpaceStackFunctor.{u, w} B S hS).map f.hom.left ≫
        (algebraicSpaceStackFunctor.{u, w} B S hS).map ξ.base.obj.hom by
      rw [← Functor.map_comp, Over.w f.hom])
  let γ : ((algebraicSpaceStackFunctor B S hS).map V.obj.hom ≫ x) ≫ ι ≅
      (algebraicSpaceStackFunctor B S hS).map j ≫
        ((algebraicSpaceStackFunctor B S hS).map f' ≫ ξ.ambientMap) :=
    eqToIso (congrArg (· ≫ ι) ha) ≪≫
      whiskerLeftIso ((algebraicSpaceStackFunctor B S hS).map f.hom.left) ξ.comm ≪≫
        eqToIso (congrArg (· ≫ ξ.ambientMap) hTw)
  let η : EtaleSmoothLift B S hS ι hι W x hx :=
    { base := V
      ambient := V'
      inclusion := j
      ambientMap := (algebraicSpaceStackFunctor B S hS).map f' ≫ ξ.ambientMap
      isSmooth_ambientMap := AlgebraicStacks.isSmooth_comp B S hS _ _
        ((isSmooth_algebraicSpaceStackMap_iff.{u, w} B S hS V'.property ξ.ambient.property
          f'.hom).2 (Space.isSmooth_of_isEtale B S hS ξ.ambient.property hf'))
        ξ.isSmooth_ambientMap
      comm := γ
      isTwoFibreProduct := Bicategory.isTwoFibreProduct_of_paste_of_eqToHom _
        ξ.isTwoFibreProduct T (isTwoFibreProduct_algebraicSpaceStackSquare.{u, w} B S hS
          ξ.base.obj.left.property V'.property ξ.ambient.property V.obj.left.property hpb') hTw
        ((subsingleton_hom₂_algebraicSpaceStackFunctor_obj _ _).elim _ _) ha γ rfl }
  let φ : η ⟶ ξ :=
    { base := f
      ambient := f'
      inclusion_comp := hpb.w
      comm := 𝟙 _
      coherence := (congrArg (γ.hom ≫ ·) (whiskerLeft_id _ _)).trans (Category.comp_id _) }
  exact ⟨η, φ, (inferInstance : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsHomLift
    ((proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).map φ) φ)⟩

/-! ### The category of smooth lifts is fibred in groupoids -/

/-- **Stacks 0CJT.** The category of smooth lifts of étale opens of `W` along the thickening
`ι : 𝒳 ⟶ 𝒳'` (**Stacks 0CJP**), projected to the spaces-étale site of `W`, is fibred in
groupoids (**Stacks 003S**).

Both conditions of Stacks 003S are proved outright, with no hypothesis beyond those of
Stacks 0CJP. Existence of lifts is
`AlgebraicGeometry.Stack.EtaleSmoothLift.exists_hom_isHomLift`, the source's construction of
`f^*ξ` from the topological invariance of the étale site along the thickening `U ⊂ U'`. Unique
fill-ins hold for *every* pair of morphisms with a common target, which is what Stacks 003S asks
and is stronger than the source's strongly cartesian verification for its chosen pullbacks
together with its groupoid-fibre argument: for `φ : η ⟶ ξ`, `ψ : ζ ⟶ ξ` and `h` with
`φ ∘ h = ψ` on the base, the fill-in is
`AlgebraicGeometry.Stack.EtaleSmoothLift.fillIn` — its ambient component comes from fullness of
the étale base change along `U ⊂ U'` (**Stacks 05ZH**, the source's **Stacks 07VW**), applied to
the cartesian squares of `φ` and `ψ` and to their ambient components, étale by **Stacks 0CJS** —
and it is unique by faithfulness of that base change and invertibility of the comparison
2-morphism of `φ`. -/
@[stacks 0CJT]
theorem isFiberedInGroupoids_proj :
    (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsFiberedInGroupoids where
  exists_lift {V U} f ξ hξ := by
    subst hξ
    exact exists_hom_isHomLift ξ f
  unique_lift {ξ η ζ} φ ψ h hh :=
    have hs := (exists_ambient_fillIn φ ψ h hh).choose_spec
    ⟨fillIn φ ψ h hh, ⟨rfl, fillIn_comp φ ψ h hh⟩, fun χ ⟨hχ, hχφ⟩ =>
      hom_ext_of_comp φ hχ (ambient_ext φ
        ((congrArg Hom.ambient hχφ).trans hs.1.symm)
        ((Hom.inclusion_comp χ).trans ((congrArg (fun t => t.hom.left ≫ η.inclusion) hχ).trans
          hs.2.symm)))
        (hχφ.trans (fillIn_comp φ ψ h hh).symm)⟩

/-- **The projection of smooth lifts is a fibred category (Stacks 02XM)**, with no hypothesis:
this is the hypothesis `hfib` of `AlgebraicGeometry.Stack.EtaleSmoothLift.isFiberedInGroupoids`,
discharged by `AlgebraicGeometry.Stack.EtaleSmoothLift.isFiberedInGroupoids_proj`. -/
theorem isFibredCategory_proj :
    (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsFibredCategory :=
  (Functor.isFibredCategory_iff_isFibered _).2 isFiberedInGroupoids_proj.isFibered

/-- **A morphism of smooth lifts with invertible base component has invertible ambient
component**, with no hypothesis: this is the hypothesis `hiso` of
`AlgebraicGeometry.Stack.EtaleSmoothLift.fiber_isGroupoid` (the isomorphism clause of
**Stacks 0CJC** read on smooth lifts), discharged by
`AlgebraicGeometry.Stack.EtaleSmoothLift.isFiberedInGroupoids_proj`: the unique fill-in of the
identity of the target through the morphism, over the inverse of its base component, is an
inverse of the morphism. -/
theorem isIso_ambient_of_isIso_base {ξ η : EtaleSmoothLift B S hS ι hι W x hx} (m : ξ ⟶ η)
    [IsIso (Hom.base m)] : IsIso (Hom.ambient m) := by
  have hp := isFiberedInGroupoids_proj (B := B) (S := S) (hS := hS) (ι := ι) (hι := hι) (W := W)
    (x := x) (hx := hx)
  let g : η.base ⟶ ξ.base := inv (Hom.base m)
  have hg : g ≫ Hom.base m = 𝟙 η.base := IsIso.inv_hom_id (Hom.base m)
  obtain ⟨χ, ⟨hχb, hχ⟩, -⟩ := hp.unique_lift m (𝟙 η) g hg
  obtain ⟨_, _, huniq⟩ := hp.unique_lift m m (𝟙 ξ.base) (Category.id_comp _)
  have h₁ : m ≫ χ = 𝟙 ξ := (huniq (m ≫ χ) ⟨by
      change Hom.base m ≫ Hom.base χ = 𝟙 ξ.base
      rw [show Hom.base χ = g from hχb]
      exact IsIso.hom_inv_id (Hom.base m),
    by rw [Category.assoc, hχ, Category.comp_id]⟩).trans
    (huniq (𝟙 ξ) ⟨rfl, Category.id_comp _⟩).symm
  exact ⟨Hom.ambient χ, congrArg Hom.ambient h₁, congrArg Hom.ambient hχ⟩

/-- **Stacks 0CJT, the fibre categories are groupoids**, with no hypothesis: the hypothesis
`hiso` of `AlgebraicGeometry.Stack.EtaleSmoothLift.fiber_isGroupoid` is discharged. -/
theorem isGroupoid_fiber_proj (U : Space.SpacesEtale B S hS W) :
    IsGroupoid ((proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) :=
  isFiberedInGroupoids_proj.fiber_isGroupoid U

end EtaleSmoothLift

end AlgebraicGeometry.Stack

end
