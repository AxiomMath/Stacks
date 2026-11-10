module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.RepresentableFibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.ProperSurjectiveDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesToposBaseChangePasting

/-!
# Base change for a proper morphism of algebraic spaces, reduced to representable squares

Let
```
X' --i--> X
|f'       |f
Y' --g--> Y
```
be a cartesian square of algebraic spaces over `S` with `f` proper. Stacks 0DG0 asserts that the
base-change map `g⁻¹ f_* F ⟶ f'_* i⁻¹ F` is an isomorphism for every sheaf `F` on `X_étale`. We
show that the base-change map is an isomorphism for every such square as soon as it is for the
squares in which `X`, `Y` and `Y'` are represented by schemes of the site, granted the full
faithfulness of descent along proper surjections of schemes
(`AlgebraicGeometry.Space.ProperSurjectivePrestackOverSchemes`).

## Main results

* `AlgebraicGeometry.Space.isIso_of_isIso_spacesEtaleInverseImage_map`: inverse images along an
  étale covering detect isomorphisms of sheaves.
* `AlgebraicGeometry.Space.isIso_spacesToposBaseChangeSquare_of_isEtaleCovering`: invertibility
  of the base-change map is étale local on `Y'`.
* `AlgebraicGeometry.Space.isIso_spacesToposBaseChangeSquare_of_properSurjective`: the descent
  step. If `h : X₁ ⟶ X` is proper and surjective, and the base-change maps of the two squares
  obtained by pasting the square with its base changes along `h` and along `X₁ ×_X X₁ ⟶ X` are
  invertible, then so is the base-change map of the square.
* `AlgebraicGeometry.Space.isIso_spacesToposBaseChangeSquare_of_isProper`: the base-change map of
  a cartesian square with proper right edge is invertible, granted the case of representable
  squares.

## References

* [Stacks Project, Tag 0DG0](https://stacks.math.columbia.edu/tag/0DG0)
* [Stacks Project, Tag 0DFX](https://stacks.math.columbia.edu/tag/0DFX)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Invertibility of the base-change map of a cartesian square does not depend on how its top
and bottom arrows are written. -/
theorem isIso_spacesToposBaseChangeSquare_congr {X Y X' Y' : AlgebraicSpaces B S hS}
    {i₁ i₂ : X' ⟶ X} {f'₁ f'₂ : X' ⟶ Y'} {f : X ⟶ Y} {g₁ g₂ : Y' ⟶ Y} (hi : i₁ = i₂)
    (hf' : f'₁ = f'₂) (hg : g₁ = g₂)
    (sq₁ : IsPullback i₁ f'₁ f g₁) (sq₂ : IsPullback i₂ f'₂ f g₂) :
    IsIso (spacesToposBaseChangeSquare B S hS i₁ f'₁ f g₁ sq₁) ↔
      IsIso (spacesToposBaseChangeSquare B S hS i₂ f'₂ f g₂ sq₂) := by
  subst hi hf' hg
  rfl

/-- **Inverse images along an étale covering detect isomorphisms.** A morphism of sheaves on the
spaces-étale site of `Y` is an isomorphism as soon as its inverse images along the members of an
étale covering of `Y` are. -/
theorem isIso_of_isIso_spacesEtaleInverseImage_map {Y : AlgebraicSpaces B S hS} {I : Type t}
    {V : I → AlgebraicSpaces B S hS} (c : ∀ k, V k ⟶ Y)
    (hc : IsEtaleCovering B S hS (fun k ↦ (V k).1) (fun k ↦ (c k).hom))
    {M N : spacesEtaleSheafCat B S hS Y} (φ : M ⟶ N)
    (h : ∀ k, IsIso ((spacesEtaleInverseImage B S hS (c k)).map φ)) : IsIso φ :=
  Pseudofunctor.isIso_of_descent_components _ c
    (SpacesEtale.isEquivalence_toDescentData_spacesEtalePseudofunctor_of_isEtaleCovering
      B S hS V c hc) φ h

/-- **Invertibility of the base-change map is étale local on the base change.** Let
`{c k : V k ⟶ Y'}` be an étale covering. If for every `k` the base-change map of every cartesian
square over `c k ≫ g` with right edge `f` is invertible, then the base-change map of the square
`(i, f', f, g)` is invertible. -/
theorem isIso_spacesToposBaseChangeSquare_of_isEtaleCovering {X Y X' Y' : AlgebraicSpaces B S hS}
    (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) (sq : IsPullback i f' f g)
    {I : Type t} {V : I → AlgebraicSpaces B S hS} (c : ∀ k, V k ⟶ Y')
    (hc : IsEtaleCovering B S hS (fun k ↦ (V k).1) (fun k ↦ (c k).hom))
    (h : ∀ k ⦃X'' : AlgebraicSpaces B S hS⦄ (j : X'' ⟶ X) (f'' : X'' ⟶ V k)
      (sq'' : IsPullback j f'' f (c k ≫ g)),
      IsIso (spacesToposBaseChangeSquare B S hS j f'' f (c k ≫ g) sq'')) :
    IsIso (spacesToposBaseChangeSquare B S hS i f' f g sq) := by
  rw [NatTrans.isIso_iff_isIso_app]
  refine fun M ↦ isIso_of_isIso_spacesEtaleInverseImage_map B S hS c hc _ fun k ↦ ?_
  let PB := spacesChosenPullback B S hS f' (c k)
  have sq₂ : IsPullback PB.p₁ PB.p₂ f' (c k) := PB.isPullback
  exact isIso_spacesEtaleInverseImage_map_of_paste_horiz B S hS i f' f g PB.p₁ PB.p₂ (c k) sq sq₂
    (h k (PB.p₁ ≫ i) PB.p₂ (sq₂.paste_horiz sq))
    (isIso_spacesToposBaseChangeSquare B S hS PB.p₁ PB.p₂ f' (c k) sq₂ (hc.etale k)) M

variable {B S hS} in
/-- Descent along a proper surjection of algebraic spaces is fully faithful, in the form of the
invertibility of the unit of the reconstruction adjunction. -/
theorem isIso_singletonDescentAdjunction_unit_app
    (H : ProperSurjectivePrestackOverSchemes B S hS) {X₁ X : AlgebraicSpaces B S hS}
    (h : X₁ ⟶ X) (hp : IsProper B S hS h.hom) (hs : IsSurjective B S hS h.hom)
    (XX : ChosenPullback h h) (N : (spacesEtalePseudofunctor B S hS).obj (.mk (op X))) :
    IsIso ((Pseudofunctor.singletonDescentAdjunction (spacesEtalePseudofunctor B S hS) h XX
      (spacesEtalePseudofunctorAdjunction B S hS h)
      (spacesEtalePseudofunctorAdjunction B S hS XX.p)).unit.app N) := by
  have hpre := isPrestackFor_of_isProper_isSurjective H h hp hs
  rw [Sieve.ofArrows, Pseudofunctor.IsPrestackFor_generate_iff,
    Pseudofunctor.isPrestackFor_ofArrows_iff] at hpre
  have := hpre.some.full
  have := hpre.some.faithful
  infer_instance

/-- Properness of morphisms of algebraic spaces is stable under base change. -/
private theorem isProper_of_isPullback_of_isProper {X Y Z W : AlgebraicSpaces B S hS}
    {fst : W ⟶ X} {snd : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (sq : IsPullback fst snd f g)
    (hg : IsProper B S hS f.hom) : IsProper B S hS snd.hom :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := fun ⦃V W : AlgebraicSpaces B S hS⦄ (m : V ⟶ W) => IsProper B S hS m.hom) sq hg

/-- **The descent step, for the mates of the pseudofunctor of spaces-étale inverse images.** Let
`(i, f', f, g)` be a commutative square and `h : X₁ ⟶ X` a proper surjection, with chosen fibre
products `P = X₁ ×_X X'`, `XX = X₁ ×_X X₁` and `QQ = P ×_{X'} P`. If the mates of the two outer
squares obtained by pasting `P` and `QQ` on top of the square are invertible, so is the mate of
the square. -/
theorem isIso_mateEquiv_of_properSurjective
    (H : ProperSurjectivePrestackOverSchemes B S hS) {X Y X' Y' X₁ : AlgebraicSpaces B S hS}
    (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) (w : i ≫ f = f' ≫ g)
    (h : X₁ ⟶ X) (hp : IsProper B S hS h.hom) (hs : IsSurjective B S hS h.hom)
    (P : ChosenPullback h i) (XX : ChosenPullback h h) (QQ : ChosenPullback P.p₂ P.p₂)
    (j : QQ.pullback ⟶ XX.pullback) (hj : j ≫ XX.p = QQ.p ≫ i)
    (hs₁ : QQ.p₁ ≫ P.p₁ = j ≫ XX.p₁) (hs₂ : QQ.p₂ ≫ P.p₁ = j ≫ XX.p₂)
    (w₁ : P.p₁ ≫ h ≫ f = (P.p₂ ≫ f') ≫ g) (w₂ : j ≫ XX.p ≫ f = (QQ.p ≫ f') ≫ g)
    (hout₁ : IsIso (mateEquiv (spacesEtalePseudofunctorAdjunction B S hS (h ≫ f))
      (spacesEtalePseudofunctorAdjunction B S hS (P.p₂ ≫ f'))
      (Pseudofunctor.commSqTwoSquare (spacesEtalePseudofunctor B S hS) w₁)))
    (hout₂ : IsIso (mateEquiv (spacesEtalePseudofunctorAdjunction B S hS (XX.p ≫ f))
      (spacesEtalePseudofunctorAdjunction B S hS (QQ.p ≫ f'))
      (Pseudofunctor.commSqTwoSquare (spacesEtalePseudofunctor B S hS) w₂))) :
    IsIso (mateEquiv (spacesEtalePseudofunctorAdjunction B S hS f)
      (spacesEtalePseudofunctorAdjunction B S hS f')
      (Pseudofunctor.commSqTwoSquare (spacesEtalePseudofunctor B S hS) w)) := by
  have hp' : IsProper B S hS P.p₂.hom := isProper_of_isPullback_of_isProper B S hS P.isPullback hp
  have hs' : IsSurjective B S hS P.p₂.hom := isSurjective_of_isPullback B S hS P.isPullback hs
  let Rf : (spacesEtalePseudofunctor B S hS).obj (.mk (op X)) ⥤
      (spacesEtalePseudofunctor B S hS).obj (.mk (op Y)) := spacesEtaleSheafPushforward B S hS f
  let Rf' : (spacesEtalePseudofunctor B S hS).obj (.mk (op X')) ⥤
      (spacesEtalePseudofunctor B S hS).obj (.mk (op Y')) := spacesEtaleSheafPushforward B S hS f'
  have : Rf.IsRightAdjoint := (spacesEtalePseudofunctorAdjunction B S hS f).isRightAdjoint
  have : Rf'.IsRightAdjoint := (spacesEtalePseudofunctorAdjunction B S hS f').isRightAdjoint
  have hcol₁ := Pseudofunctor.isIso_mateEquiv_commSqTwoSquare_comp_of_paste_vert
    (spacesEtalePseudofunctor B S hS) i f' f g P.p₁ P.p₂ h w P.condition w₁
    (spacesEtalePseudofunctorAdjunction B S hS f) (spacesEtalePseudofunctorAdjunction B S hS f')
    (spacesEtalePseudofunctorAdjunction B S hS h) (spacesEtalePseudofunctorAdjunction B S hS P.p₂)
    (spacesEtalePseudofunctorAdjunction B S hS (h ≫ f))
    (spacesEtalePseudofunctorAdjunction B S hS (P.p₂ ≫ f')) hout₁
  have hcol₂ := Pseudofunctor.isIso_mateEquiv_commSqTwoSquare_comp_of_paste_vert
    (spacesEtalePseudofunctor B S hS) i f' f g j QQ.p XX.p w hj w₂
    (spacesEtalePseudofunctorAdjunction B S hS f) (spacesEtalePseudofunctorAdjunction B S hS f')
    (spacesEtalePseudofunctorAdjunction B S hS XX.p)
    (spacesEtalePseudofunctorAdjunction B S hS QQ.p)
    (spacesEtalePseudofunctorAdjunction B S hS (XX.p ≫ f))
    (spacesEtalePseudofunctorAdjunction B S hS (QQ.p ≫ f')) hout₂
  rw [NatTrans.isIso_iff_isIso_app]
  exact fun N ↦ Pseudofunctor.isIso_app_of_isIso_descentUnit (spacesEtalePseudofunctor B S hS) h i
    P XX QQ P.condition j hj hs₁ hs₂
    (spacesEtalePseudofunctorAdjunction B S hS h) (spacesEtalePseudofunctorAdjunction B S hS XX.p)
    (spacesEtalePseudofunctorAdjunction B S hS P.p₂)
    (spacesEtalePseudofunctorAdjunction B S hS QQ.p)
    (Rf ⋙ ((spacesEtalePseudofunctor B S hS).map g.op.toLoc).toFunctor) Rf' _ hcol₁ hcol₂ N
    (isIso_singletonDescentAdjunction_unit_app H h hp hs XX N)
    (isIso_singletonDescentAdjunction_unit_app H P.p₂ hp' hs' QQ _)

/-- **The descent step.** Let `(i, f', f, g)` be a cartesian square and `h : X₁ ⟶ X` a proper
surjection, with chosen fibre products `P = X₁ ×_X X'` and `XX = X₁ ×_X X₁`, and `ZZ` the fibre
product of `XX ⟶ X` with `i`. If the base-change maps of the two outer squares obtained by pasting
`P` and `ZZ` on top of the square are invertible, so is the base-change map of the square. -/
theorem isIso_spacesToposBaseChangeSquare_of_properSurjective
    (H : ProperSurjectivePrestackOverSchemes B S hS) {X Y X' Y' X₁ : AlgebraicSpaces B S hS}
    (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) (sq : IsPullback i f' f g)
    (h : X₁ ⟶ X) (hp : IsProper B S hS h.hom) (hs : IsSurjective B S hS h.hom)
    (h₁ : IsIso (spacesToposBaseChangeSquare B S hS (spacesChosenPullback B S hS h i).p₁
      ((spacesChosenPullback B S hS h i).p₂ ≫ f') (h ≫ f) g
      ((spacesChosenPullback B S hS h i).isPullback.paste_vert sq)))
    (h₂ : IsIso (spacesToposBaseChangeSquare B S hS
      (spacesChosenPullback B S hS (spacesChosenPullback B S hS h h).p i).p₁
      ((spacesChosenPullback B S hS (spacesChosenPullback B S hS h h).p i).p₂ ≫ f')
      ((spacesChosenPullback B S hS h h).p ≫ f) g
      ((spacesChosenPullback B S hS (spacesChosenPullback B S hS h h).p i).isPullback.paste_vert
        sq))) :
    IsIso (spacesToposBaseChangeSquare B S hS i f' f g sq) := by
  let P := spacesChosenPullback B S hS h i
  let XX := spacesChosenPullback B S hS h h
  let ZZ := spacesChosenPullback B S hS XX.p i
  let QQ := ChosenPullback.baseChangedSelf h i P XX ZZ
  have hQp : QQ.p = ZZ.p₂ := ChosenPullback.baseChangedSelf_p h i P XX ZZ
  have hj : ZZ.p₁ ≫ XX.p = QQ.p ≫ i := hQp ▸ ZZ.condition
  have hZ : IsPullback ZZ.p₁ QQ.p XX.p i := hQp ▸ ZZ.isPullback
  have hout₂ := (isIso_spacesToposBaseChangeSquare_congr B S hS rfl
    (congrArg (· ≫ f') hQp.symm) rfl _ (hZ.paste_vert sq)).mp h₂
  rw [spacesToposBaseChangeSquare_eq_mateEquiv] at h₁ hout₂ ⊢
  exact isIso_mateEquiv_of_properSurjective B S hS H i f' f g sq.w h hp hs P XX QQ ZZ.p₁ hj
    (ChosenPullback.baseChangedSelf_p₁_fst h i P XX ZZ)
    (ChosenPullback.baseChangedSelf_p₂_fst h i P XX ZZ) _ _ h₁ hout₂

section Reduction

variable (H : ProperSurjectivePrestackOverSchemes B S hS)
  (Hrep : ∀ ⦃X Y X' Y' : AlgebraicSpaces B S hS⦄ (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (g : Y' ⟶ Y) (sq : IsPullback i f' f g), X.1.IsRepresentable → Y.1.IsRepresentable →
    Y'.1.IsRepresentable → IsProper B S hS f.hom →
    IsIso (spacesToposBaseChangeSquare B S hS i f' f g sq))

include H Hrep in
/-- **Over an affine base, for a representable base change.** If `Y` is represented by an affine
scheme of the site and `Y'` is representable, the base-change map of a cartesian square with
proper right edge is invertible. -/
theorem isIso_spacesToposBaseChangeSquare_of_isProper_of_isAffine_of_isRepresentable
    {X X' Y' : AlgebraicSpaces B S hS} {V : BigFppfOver B S hS}
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ schemeSpace V) (g : Y' ⟶ schemeSpace V)
    (sq : IsPullback i f' f g) (hY' : Y'.1.IsRepresentable) (hf : IsProper B S hS f.hom) :
    IsIso (spacesToposBaseChangeSquare B S hS i f' f g sq) := by
  obtain ⟨V₁, ρ, hρp, hρs⟩ :=
    exists_properSurjective_schemeCover_of_isProper_toAffine B S hS V hV X.2 f.hom hf
  let h : schemeSpace V₁ ⟶ X := ObjectProperty.homMk ρ
  have hrepV : (schemeSpace V).1.IsRepresentable := inferInstanceAs (yoneda.obj V).IsRepresentable
  have hrep₁ : (schemeSpace V₁).1.IsRepresentable :=
    inferInstanceAs (yoneda.obj V₁).IsRepresentable
  have hp : IsProper B S hS h.hom := hρp
  refine isIso_spacesToposBaseChangeSquare_of_properSurjective B S hS H i f' f g sq h hp hρs ?_ ?_
  · exact Hrep _ _ _ _ _ hrep₁ hrepV hY'
      (isProper_comp' B S hS h.hom f.hom X.2 (schemeSpace V).2 hp hf)
  · let XX := spacesChosenPullback B S hS h h
    have hXX : XX.pullback.1.IsRepresentable :=
      isRepresentable_pullback B S hS X.2 hrep₁ hrep₁ h.hom h.hom
    have hp₂ : IsProper B S hS XX.p₂.hom :=
      isProper_of_isPullback_of_isProper B S hS XX.isPullback hp
    have hpp : IsProper B S hS XX.p.hom :=
      XX.hp₂ ▸ isProper_comp' B S hS XX.p₂.hom h.hom (schemeSpace V₁).2 X.2 hp₂ hp
    exact Hrep _ _ _ _ _ hXX hrepV hY'
      (isProper_comp' B S hS XX.p.hom f.hom X.2 (schemeSpace V).2 hpp hf)

include H Hrep in
/-- **Over an affine base.** If `Y` is represented by an affine scheme of the site, the
base-change map of a cartesian square with proper right edge is invertible. -/
theorem isIso_spacesToposBaseChangeSquare_of_isProper_of_isAffine
    {X X' Y' : AlgebraicSpaces B S hS} {V : BigFppfOver B S hS}
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ schemeSpace V) (g : Y' ⟶ schemeSpace V)
    (sq : IsPullback i f' f g) (hf : IsProper B S hS f.hom) :
    IsIso (spacesToposBaseChangeSquare B S hS i f' f g sq) := by
  obtain ⟨W, b, -, -, -, hcov⟩ := exists_isEtaleCovering_affine B S hS Y'.1 Y'.2
  refine isIso_spacesToposBaseChangeSquare_of_isEtaleCovering B S hS i f' f g sq
    (V := fun x ↦ schemeSpace (W x)) (fun x ↦ ObjectProperty.homMk (b x)) hcov ?_
  exact fun x X'' j f'' sq'' ↦
    isIso_spacesToposBaseChangeSquare_of_isProper_of_isAffine_of_isRepresentable B S hS H Hrep hV j
      f'' f _ sq'' (inferInstanceAs (yoneda.obj (W x)).IsRepresentable) hf

include H Hrep in
/-- **Base change for a proper morphism of algebraic spaces, reduced to representable squares**
(the reduction in the proof of Stacks 0DG0). Let `(i, f', f, g)` be a cartesian square of
algebraic spaces over `S` with `f` proper. Granted full faithfulness of descent along proper
surjections of schemes (`H`) and the statement for cartesian squares of representable algebraic
spaces with proper right edge (`Hrep`), the base-change map `g⁻¹ f_* ⟶ f'_* i⁻¹` is invertible. -/
theorem isIso_spacesToposBaseChangeSquare_of_isProper {X Y X' Y' : AlgebraicSpaces B S hS}
    (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) (sq : IsPullback i f' f g)
    (hf : IsProper B S hS f.hom) :
    IsIso (spacesToposBaseChangeSquare B S hS i f' f g sq) := by
  obtain ⟨W, b, hWaff, -, -, hcov⟩ := exists_isEtaleCovering_affine B S hS Y.1 Y.2
  let d : ∀ l, schemeSpace (W l) ⟶ Y := fun l ↦ ObjectProperty.homMk (b l)
  refine isIso_spacesToposBaseChangeSquare_of_isEtaleCovering B S hS i f' f g sq
    (fun l ↦ (spacesChosenPullback B S hS g (d l)).p₁)
    (isEtaleCovering_spacesChosenPullback_p₁ B S hS _ d hcov g) ?_
  intro l X'' j f'' sqj
  let PB := spacesChosenPullback B S hS g (d l)
  let R := spacesChosenPullback B S hS f (d l)
  have sqd : IsPullback j f'' f (PB.p₂ ≫ d l) := by rwa [← PB.condition]
  let m : X'' ⟶ R.pullback := R.isPullback.lift j (f'' ≫ PB.p₂) (by
    rw [sqd.w, Category.assoc])
  have hm₁ : m ≫ R.p₁ = j := R.isPullback.lift_fst _ _ _
  have hm₂ : m ≫ R.p₂ = f'' ≫ PB.p₂ := R.isPullback.lift_snd _ _ _
  have sqL : IsPullback m f'' R.p₂ PB.p₂ := IsPullback.of_right (hm₁ ▸ sqd) hm₂ R.isPullback
  have hR := isIso_spacesToposBaseChangeSquare B S hS R.p₁ R.p₂ f (d l) R.isPullback
    (hcov.etale l)
  have hL := isIso_spacesToposBaseChangeSquare_of_isProper_of_isAffine B S hS H Hrep (hWaff l)
    m f'' R.p₂ PB.p₂ sqL (isProper_of_isPullback_of_isProper B S hS R.isPullback hf)
  exact (isIso_spacesToposBaseChangeSquare_congr B S hS hm₁ rfl PB.condition.symm _ _).mp
    (isIso_spacesToposBaseChangeSquare_paste_horiz B S hS R.p₁ R.p₂ f (d l) m f'' PB.p₂
      R.isPullback sqL hR hL)

end Reduction

end AlgebraicGeometry.Space

end
