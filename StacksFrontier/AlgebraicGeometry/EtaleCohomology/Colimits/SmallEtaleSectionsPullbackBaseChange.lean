module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleLevelLegPinning
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.SpecializationMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.DegreeZeroSurjectivity

/-!
# Pulling back sections over an étale object, and base change

Let `p : T ⟶ Z` be a morphism of schemes, `W` an object of the small étale site of `Z` and
`r : T ⟶ W` a morphism lying over `p`. A section of an abelian sheaf `M` on `Z` over `W` pulls back
to a global section of `p⁻¹M` on `T`: the unit of the inverse-image/direct-image adjunction over
`W`, followed by restriction along the morphism from the terminal object of the site of `T` into
the base change of `W` that `r` determines. This is `Stacks.EtaleCohomology.etaleSectionsPullback`.

For an étale `e : P ⟶ Y`, pulling back the sections of `M` over the object `e` itself along the
identity of `P` is a bijection `M(e) ≅ Γ(P, e⁻¹M)` (`bijective_etaleSectionsPullback_self`): the
inverse image along an étale morphism is restriction.

The main result is the compatibility of this identification with a square

```
P' --c'--> P
|e'        |e
Y' --c-->  Y
```

and a map `φ : c⁻¹M ⟶ N`: pulling a section over `e` back to `P`, then along `c'` to `P'`, and
applying `e'⁻¹φ` through the two comparisons of iterated inverse images, is applying the transpose
of `φ` over `e` and pulling the result back along `e'`
(`etaleSectionsPullback_comp_etaleSectionsRestriction_comp_leg`). It is what reads the legs and the
transition maps of a system of sheaves restricted to an étale neighbourhood
(`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.systemBaseChange`) on sections over objects of
the original sites.

## Main definitions

* `Stacks.EtaleCohomology.etaleSectionsPullback` — pulling back a section over an étale object.

## Main results

* `Stacks.EtaleCohomology.bijective_etaleSectionsPullback_self` — the identification
  `M(e) ≅ Γ(P, e⁻¹M)` for an étale `e`.
* `Stacks.EtaleCohomology.etaleSectionsPullback_comp_etaleSectionsRestriction_comp_leg` — **the
  compatibility with a square.**

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-! ### Pulling back sections over an étale object -/

section Pullback

variable {Z T : Scheme.{u}} (p : T ⟶ Z) (W : Z.Etale) (r : T ⟶ W.left) (hr : r ≫ W.hom = p)

/-- **Pulling back a section over an étale object to a global section of the inverse image.** For
`r : T ⟶ W` lying over `p`, the unit of `p⁻¹ ⊣ p_*` over `W`, followed by restriction along the
morphism from the terminal object of the site of `T` into the base change of `W` that `r`
determines. -/
def etaleSectionsPullback (M : Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1}) :
    M.obj.obj (op W) ⟶
      ((etaleAbelianInverseImage.{u, u + 1} p).obj M).obj.obj (op (Etale.mk (𝟙 T))) :=
  ((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} p).unit.app M).hom.app (op W) ≫
    ((etaleAbelianInverseImage.{u, u + 1} p).obj M).obj.map
      (smallEtaleBaseChangeLift p W r hr).op

/-- Pulling back along equal morphisms gives equal maps. -/
theorem etaleSectionsPullback_congr {r r' : T ⟶ W.left} (h : r = r') (hr : r ≫ W.hom = p)
    (hr' : r' ≫ W.hom = p) (M : Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1}) :
    etaleSectionsPullback p W r hr M = etaleSectionsPullback p W r' hr' M := by
  subst h
  rfl

/-- The pullback map on global sections is pulling back the sections over the terminal object. -/
theorem etaleSectionsRestriction_eq_etaleSectionsPullback
    (M : Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1}) :
    etaleSectionsRestriction.{u, u + 1} p M =
      etaleSectionsPullback p (Etale.mk (𝟙 Z)) p (Category.comp_id p) M := by
  have h : (isTerminalSmallEtaleBaseChangeEtaleMkId.{u} p).from (Etale.mk (𝟙 T)) =
      smallEtaleBaseChangeLift p (Etale.mk (𝟙 Z)) p (Category.comp_id p) :=
    (isTerminalSmallEtaleBaseChangeEtaleMkId.{u} p).hom_ext _ _
  rw [etaleSectionsRestriction, h]
  rfl

/-- The first projection of a composite of a lift with a base-changed morphism, on variables. -/
private theorem lift_comp_fst_algebra {E : Type*} [Category* E] {A B C D D' : E} {x : A ⟶ B}
    {y : B ⟶ C} {f₁ : C ⟶ D} {f₂ : B ⟶ D'} {gl : D' ⟶ D} {r : A ⟶ D'}
    (hm : y ≫ f₁ = f₂ ≫ gl) (hx : x ≫ f₂ = r) : (x ≫ y) ≫ f₁ = r ≫ gl := by
  rw [Category.assoc, hm, reassoc_of% hx]

/-- **Pulling back a section is natural in the étale object.** Restricting a section along a
morphism `g : W₂ ⟶ W₁` of étale objects and pulling it back along `r₂` is pulling it back along
`r₂ ≫ g`. -/
theorem map_comp_etaleSectionsPullback {W₁ W₂ : Z.Etale} (g : W₂ ⟶ W₁) (r₂ : T ⟶ W₂.left)
    (hr₂ : r₂ ≫ W₂.hom = p) (M : Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1}) :
    M.obj.map g.op ≫ etaleSectionsPullback p W₂ r₂ hr₂ M =
      etaleSectionsPullback p W₁ (r₂ ≫ g.left)
        ((Category.assoc _ _ _).trans ((congrArg (r₂ ≫ ·) (MorphismProperty.Over.w g)).trans hr₂))
        M := by
  have hn := ((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} p).unit.app M).hom.naturality g.op
  have hlift : smallEtaleBaseChangeLift p W₂ r₂ hr₂ ≫ (smallEtaleBaseChange p).map g =
      smallEtaleBaseChangeLift p W₁ (r₂ ≫ g.left)
        ((Category.assoc _ _ _).trans
          ((congrArg (r₂ ≫ ·) (MorphismProperty.Over.w g)).trans hr₂)) :=
    smallEtaleBaseChange_hom_ext p ((lift_comp_fst_algebra (smallEtaleBaseChange_map_left_fst p g)
      (pullback.lift_fst _ _ _)).trans (pullback.lift_fst _ _ _).symm)
  refine (Category.assoc _ _ _).symm.trans ((hn =≫ _).trans ((Category.assoc _ _ _).trans
    (whisker_eq _ ?_)))
  exact (((etaleAbelianInverseImage.{u, u + 1} p).obj M).obj.map_comp _ _).symm.trans
    (congrArg (fun z => ((etaleAbelianInverseImage.{u, u + 1} p).obj M).obj.map z.op) hlift)

end Pullback

/-! ### Over the étale object itself -/

section Self

variable {P Y : Scheme.{u}} (e : P ⟶ Y) [Etale e]

/-- **For an étale `e : P ⟶ Y`, pulling back the sections over the object `e` to `P` is a
bijection `M(e) ≅ Γ(P, e⁻¹M)`.** The inverse image along an étale morphism is restriction
(`Stacks.EtaleCohomology.etaleAbelianInverseImageRestrictionIso`), whose unit on sections is
restriction along the counit of composition with `e` against base change along `e`; at the
object `e` and read on the terminal object of the site of `P`, that is restriction along an
isomorphism. -/
theorem bijective_etaleSectionsPullback_self
    (M : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) :
    Function.Bijective (etaleSectionsPullback e (Etale.mk e) (𝟙 P) (Category.id_comp e) M) := by
  let ρ := (etaleAbelianInverseImageRestrictionIso.{u, u + 1} e).app M
  let κ : (Etale.smallEtaleCompose e).obj (Etale.mk (𝟙 P)) ≅ Etale.mk e :=
    MorphismProperty.Over.isoMk (Iso.refl _) rfl
  have hu : ((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} e).unit.app M).hom.app
        (op (Etale.mk e)) ≫
      ρ.hom.hom.app (op ((smallEtaleBaseChange e).obj (Etale.mk e))) =
        M.obj.map ((Etale.smallEtaleComposeBaseChangeAdj e).counit.app (Etale.mk e)).op :=
    (congrArg (fun z => z.hom.app (op (Etale.mk e)))
      (Adjunction.unit_leftAdjointUniq_hom_app (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} e)
        (etaleRestrictionAbelianDirectImageAdj.{u, u + 1} e) M)).trans
      (etaleRestrictionAbelianDirectImageAdj_unit_app.{u, u + 1} e M (Etale.mk e))
  have hκ : (Etale.smallEtaleCompose e).map (smallEtaleBaseChangeLift e (Etale.mk e) (𝟙 P)
        (Category.id_comp e)) ≫
      (Etale.smallEtaleComposeBaseChangeAdj e).counit.app (Etale.mk e) = κ.hom :=
    MorphismProperty.Over.Hom.ext (pullback.lift_fst _ _ _)
  have key : etaleSectionsPullback e (Etale.mk e) (𝟙 P) (Category.id_comp e) M ≫
      ρ.hom.hom.app (op (Etale.mk (𝟙 P))) = M.obj.map κ.hom.op := by
    have hn := ρ.hom.hom.naturality
      (smallEtaleBaseChangeLift e (Etale.mk e) (𝟙 P) (Category.id_comp e)).op
    refine (Category.assoc _ _ _).trans ((whisker_eq _ hn).trans
      ((Category.assoc _ _ _).symm.trans ((hu =≫ _).trans ?_)))
    exact (M.obj.map_comp _ _).symm.trans (congrArg (fun z => M.obj.map z.op) hκ)
  have hiso : IsIso (etaleSectionsPullback e (Etale.mk e) (𝟙 P) (Category.id_comp e) M ≫
      ρ.hom.hom.app (op (Etale.mk (𝟙 P)))) := by
    rw [key]
    exact inferInstanceAs (IsIso (M.obj.mapIso κ.op).hom)
  have : IsIso (etaleSectionsPullback e (Etale.mk e) (𝟙 P) (Category.id_comp e) M) :=
    IsIso.of_isIso_comp_right _ (ρ.hom.hom.app (op (Etale.mk (𝟙 P))))
  exact ConcreteCategory.bijective_of_isIso _

end Self

/-! ### Compatibility with a square -/

section Square

variable {P P' Y Y' : Scheme.{u}} (c' : P' ⟶ P) (e : P ⟶ Y) (e' : P' ⟶ Y') (c : Y' ⟶ Y)
  (he : c' ≫ e = e' ≫ c)

/-- The map `c'⁻¹e⁻¹M ⟶ e'⁻¹N` that a square `c' ≫ e = e' ≫ c` and a map `φ : c⁻¹M ⟶ N` induce
through the two comparisons of iterated inverse images. This is the shape of the legs and of the
transition maps of `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.systemBaseChange`. -/
abbrev squareLeg (M : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})
    (N : Sheaf (smallEtaleTopology Y') AddCommGrpCat.{u + 1})
    (φ : (etaleAbelianInverseImage.{u, u + 1} c).obj M ⟶ N) :
    (etaleAbelianInverseImage.{u, u + 1} c').obj ((etaleAbelianInverseImage.{u, u + 1} e).obj M) ⟶
      (etaleAbelianInverseImage.{u, u + 1} e').obj N :=
  (etaleAbelianInverseImageCompIso'.{u, u + 1} c' e (c' ≫ e) rfl).inv.app M ≫
    (etaleAbelianInverseImageCompIso'.{u, u + 1} e' c (c' ≫ e) he).hom.app M ≫
      (etaleAbelianInverseImage.{u, u + 1} e').map φ

/-- **The transpose of `squareLeg`.** Transposed along `e` and then along `c'`, the map induced by
`φ` is the transpose of `φ` along `c` followed by `c_*` of the unit along `e'`, through the two
comparisons of iterated direct images with the direct image along the diagonal of the square. -/
theorem squareLeg_transpose (M : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})
    (N : Sheaf (smallEtaleTopology Y') AddCommGrpCat.{u + 1})
    (φ : (etaleAbelianInverseImage.{u, u + 1} c).obj M ⟶ N) :
    (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} e).unit.app M ≫
        (etaleAbelianDirectImage.{u, u + 1} e).map
          ((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} c').homEquiv _ _
            (squareLeg c' e e' c he M N φ)) ≫
        (etaleAbelianDirectImageCompIso'.{u, u + 1} c' e (c' ≫ e) rfl).hom.app
          ((etaleAbelianInverseImage.{u, u + 1} e').obj N) =
      (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} c).homEquiv _ _ φ ≫
        (etaleAbelianDirectImage.{u, u + 1} c).map
          ((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} e').unit.app N) ≫
        (etaleAbelianDirectImageCompIso'.{u, u + 1} e' c (c' ≫ e) he).hom.app
          ((etaleAbelianInverseImage.{u, u + 1} e').obj N) := by
  have LA₁ := leftAdjointCompIso_inv_homEquiv_symm
    (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} e)
    (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} c')
    (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} (c' ≫ e))
    (etaleAbelianDirectImageCompIso'.{u, u + 1} c' e (c' ≫ e) rfl)
    ((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} e).homEquiv M _ (𝟙 _))
    ((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} c').homEquiv _ _
      (squareLeg c' e e' c he M N φ))
  have LA₂ := leftAdjointCompIso_inv_homEquiv_symm
    (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} c)
    (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} e')
    (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} (c' ≫ e))
    (etaleAbelianDirectImageCompIso'.{u, u + 1} e' c (c' ≫ e) he)
    ((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} c).homEquiv _ _ φ)
    ((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} e').homEquiv N _ (𝟙 _))
  simp only [Equiv.symm_apply_apply, CategoryTheory.Functor.map_id,
    Category.comp_id] at LA₁ LA₂
  simp only [Adjunction.homEquiv_id] at LA₁ LA₂
  apply ((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} (c' ≫ e)).homEquiv M
    ((etaleAbelianInverseImage.{u, u + 1} e').obj N)).symm.injective
  rw [← LA₁, ← LA₂]
  simp only [squareLeg, etaleAbelianInverseImageCompIso', Iso.symm_inv, Iso.symm_hom]
  refine (congrArg (_ ≫ ·) (Category.id_comp _)).trans ?_
  exact Iso.inv_hom_id_app_assoc _ _ _

/-- The first projection of the left-hand morphism of `etaleSectionsPullback_comp_squareLeg`,
stated on variables. -/
private theorem hobj_left_algebra {E : Type*} [Category* E] {P' Q R S P : E} {x : P' ⟶ Q}
    {y : Q ⟶ R} {F₁ : R ⟶ S} {F₂ : S ⟶ P} {g : Q ⟶ P} {l₁ : P ⟶ S} {cc : P' ⟶ P}
    (hm : y ≫ F₁ = g ≫ l₁) (hL₂ : x ≫ g = cc) (hL₁ : l₁ ≫ F₂ = 𝟙 P) :
    ((x ≫ y) ≫ F₁) ≫ F₂ = cc := by
  rw [lift_comp_fst_algebra hm hL₂]
  simp [hL₁]

/-- The first projection of the right-hand morphism of `etaleSectionsPullback_comp_squareLeg`,
stated on variables. -/
private theorem hobj_right_algebra {E : Type*} [Category* E] {P' T₀ U R S P T₁ : E}
    {x : P' ⟶ T₀} {k' : T₀ ⟶ U} {k₁ : U ⟶ R} {F₁ : R ⟶ S} {F₂ : S ⟶ P} {pm : U ⟶ P}
    {k₂ : U ⟶ T₀} {G₁ : T₀ ⟶ T₁} {G₂ : T₁ ⟶ P} {lf : P' ⟶ T₁} {cc : P' ⟶ P}
    (h₁ : k₁ ≫ F₁ ≫ F₂ = pm) (h₂ : k₂ ≫ G₁ ≫ G₂ = pm) (hκ : k' ≫ k₂ = 𝟙 T₀)
    (hL₃ : x ≫ G₁ = lf) (hlf : lf ≫ G₂ = cc) :
    ((x ≫ k' ≫ k₁) ≫ F₁) ≫ F₂ = cc := by
  simp only [Category.assoc]
  rw [h₁, ← h₂, reassoc_of% hκ, reassoc_of% hL₃, hlf]

/-- The rearrangement of the left-hand side of `etaleSectionsPullback_comp_squareLeg`, stated
on variables. -/
private theorem left_algebra {E : Type*} [Category* E] {A₀ A₁ A₂ A₃ A₄ A₅ B₁ C₁ : E}
    {uE : A₀ ⟶ A₁} {r₁ : A₁ ⟶ A₂} {uC₀ : A₂ ⟶ A₃} {r₂ : A₃ ⟶ A₄} {lg₀ : A₄ ⟶ A₅}
    {uC₁ : A₁ ⟶ B₁} {rb : B₁ ⟶ A₃} {lg₁ : B₁ ⟶ C₁} {n' : C₁ ⟶ A₅} {rc : B₁ ⟶ A₄}
    (n1 : r₁ ≫ uC₀ = uC₁ ≫ rb) (hc : rb ≫ r₂ = rc) (n2 : rc ≫ lg₀ = lg₁ ≫ n') :
    (uE ≫ r₁) ≫ (uC₀ ≫ r₂) ≫ lg₀ = (uE ≫ uC₁ ≫ lg₁) ≫ n' := by
  simp only [Category.assoc]
  rw [reassoc_of% n1, reassoc_of% hc, n2]

/-- The rearrangement behind `etaleSectionsPullback_comp_squareLeg`, stated on variables. -/
private theorem square_algebra {E : Type*} [Category* E] {A A' B C₀ C D D'' : E}
    {x₁ : A ⟶ A'} {x₂ : A' ⟶ B} {Y₀ : A ⟶ C₀} {u : C₀ ⟶ C} {k₁ m₁ : B ⟶ D} {k₂ m₂ : C ⟶ D}
    {k₂' : D ⟶ C} {l : B ⟶ D''} {l₃ : C ⟶ D''} (hTR : x₁ ≫ x₂ ≫ k₁ = Y₀ ≫ u ≫ k₂)
    (hk₁ : k₁ = m₁) (hk₂ : k₂ = m₂) (hinv : m₂ ≫ k₂' = 𝟙 C) (hgeom : l = m₁ ≫ k₂' ≫ l₃) :
    (x₁ ≫ x₂) ≫ l = Y₀ ≫ u ≫ l₃ := by
  subst hgeom hk₁ hk₂
  simp only [Category.assoc]
  rw [reassoc_of% hTR, reassoc_of% hinv]

variable [Etale e]

/-- **Pulling back a section over an étale object commutes with the map a square induces.** For
a section of `M` over the étale object `e`, pulling it back to `P`, then along `c'` to `P'`, and
applying `squareLeg c' e e' c he M N φ`, is applying the transpose of `φ` over `e` and pulling the
result back along `e'`, through the morphism `P' ⟶ P ×_Y Y'` with components `c'` and `e'`. -/
theorem etaleSectionsPullback_comp_squareLeg
    (M : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})
    (N : Sheaf (smallEtaleTopology Y') AddCommGrpCat.{u + 1})
    (φ : (etaleAbelianInverseImage.{u, u + 1} c).obj M ⟶ N) :
    etaleSectionsPullback e (Etale.mk e) (𝟙 P) (Category.id_comp e) M ≫
        etaleSectionsRestriction.{u, u + 1} c' ((etaleAbelianInverseImage.{u, u + 1} e).obj M) ≫
          (squareLeg c' e e' c he M N φ).hom.app (op (Etale.mk (𝟙 P'))) =
      etaleTransposeSection.{u + 1, u} c φ (Etale.mk e) ≫
        etaleSectionsPullback e' ((smallEtaleBaseChange c).obj (Etale.mk e))
          (pullback.lift c' e' he) (pullback.lift_snd _ _ _) N := by
  let N' := (etaleAbelianInverseImage.{u, u + 1} e').obj N
  let leg := squareLeg c' e e' c he M N φ
  let L₁ := smallEtaleBaseChangeLift e (Etale.mk e) (𝟙 P) (Category.id_comp e)
  let L₂ := smallEtaleBaseChangeLift c' (Etale.mk (𝟙 P)) c' (Category.comp_id c')
  let L₃ := smallEtaleBaseChangeLift e' ((smallEtaleBaseChange c).obj (Etale.mk e))
    (pullback.lift c' e' he) (pullback.lift_snd _ _ _)
  let κ₁ := (smallEtaleBaseChangeComp' c' e (c' ≫ e) rfl).hom.app (Etale.mk e)
  let κ₂ := (smallEtaleBaseChangeComp' e' c (c' ≫ e) he).hom.app (Etale.mk e)
  let κ₂' := (smallEtaleBaseChangeComp' e' c (c' ≫ e) he).inv.app (Etale.mk e)
  let uE := ((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} e).unit.app M).hom
  let uC := ((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} c').unit.app
    ((etaleAbelianInverseImage.{u, u + 1} e).obj M)).hom
  let uN := ((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} e').unit.app N).hom
  -- the transpose of the leg, on sections over `e`
  have TR := squareLeg_transpose c' e e' c he M N φ
  rw [Adjunction.homEquiv_unit] at TR
  have hTR := congrArg (fun z => z.hom.app (op (Etale.mk e))) TR
  have hk₂h : ((etaleAbelianDirectImageCompIso'.{u, u + 1} e' c (c' ≫ e) he).hom.app N').hom.app
      (op (Etale.mk e)) = N'.obj.map κ₂.op :=
    smallEtalePushforwardComp'_hom_app_hom_app e' c (c' ≫ e) he _ N' (op (Etale.mk e))
  have hinv : N'.obj.map κ₂.op ≫ N'.obj.map κ₂'.op = 𝟙 _ := by
    rw [← N'.obj.map_comp, ← op_comp, Iso.inv_hom_id_app, op_id, N'.obj.map_id]
  -- the geometry
  have hobj : L₂ ≫ (smallEtaleBaseChange c').map L₁ = L₃ ≫ κ₂' ≫ κ₁ := by
    have h₂ := smallEtaleBaseChangeComp'_fst_fst e' c (c' ≫ e) he (Etale.mk e)
    have h₁ := smallEtaleBaseChangeComp'_fst_fst c' e (c' ≫ e) rfl (Etale.mk e)
    have hκ : κ₂'.left ≫ κ₂.left = 𝟙 _ :=
      congrArg (fun z => z.left) ((smallEtaleBaseChangeComp' e' c (c' ≫ e) he).inv_hom_id_app
        (Etale.mk e))
    have hL₃ : L₃.left ≫ pullback.fst ((smallEtaleBaseChange c).obj (Etale.mk e)).hom e' =
        pullback.lift c' e' he := pullback.lift_fst _ _ _
    have hL₂ : L₂.left ≫ pullback.fst (Etale.mk (𝟙 P)).hom c' = c' := pullback.lift_fst _ _ _
    have hL₁ : L₁.left ≫ pullback.fst (Etale.mk e).hom e = 𝟙 P := pullback.lift_fst _ _ _
    have hm := smallEtaleBaseChange_map_left_fst c' L₁
    refine smallEtaleBaseChange_hom_ext c' (pullback.hom_ext ?_ ?_)
    · exact (hobj_left_algebra hm hL₂ hL₁).trans (hobj_right_algebra h₁ h₂ hκ hL₃
        (pullback.lift_fst c' e' he)).symm
    · exact (Category.assoc _ _ _).trans
        (((smallEtaleBaseChange_fst_snd c' e (L₂ ≫ (smallEtaleBaseChange c').map L₁)).trans
          (smallEtaleBaseChange_fst_snd c' e (L₃ ≫ κ₂' ≫ κ₁)).symm).trans
            (Category.assoc _ _ _).symm)
  have hk₁ : ((etaleAbelianDirectImageCompIso'.{u, u + 1} c' e (c' ≫ e) rfl).hom.app N').hom.app
      (op (Etale.mk e)) = N'.obj.map κ₁.op :=
    smallEtalePushforwardComp'_hom_app_hom_app c' e (c' ≫ e) rfl _ N' (op (Etale.mk e))
  have hgeom : N'.obj.map (L₂ ≫ (smallEtaleBaseChange c').map L₁).op =
      N'.obj.map κ₁.op ≫ N'.obj.map κ₂'.op ≫ N'.obj.map L₃.op := by
    rw [← N'.obj.map_comp, ← N'.obj.map_comp, ← op_comp, ← op_comp, hobj,
      Category.assoc]
  -- the left-hand side
  have hL : etaleSectionsPullback e (Etale.mk e) (𝟙 P) (Category.id_comp e) M ≫
      etaleSectionsRestriction.{u, u + 1} c' ((etaleAbelianInverseImage.{u, u + 1} e).obj M) ≫
        leg.hom.app (op (Etale.mk (𝟙 P'))) =
      (uE.app (op (Etale.mk e)) ≫ (uC.app (op ((smallEtaleBaseChange e).obj (Etale.mk e))) ≫
        leg.hom.app (op ((smallEtaleBaseChange c').obj
          ((smallEtaleBaseChange e).obj (Etale.mk e)))))) ≫
        N'.obj.map (L₂ ≫ (smallEtaleBaseChange c').map L₁).op := by
    have n1 := uC.naturality L₁.op
    have n2 := leg.hom.naturality (L₂ ≫ (smallEtaleBaseChange c').map L₁).op
    rw [etaleSectionsRestriction_eq_etaleSectionsPullback]
    exact left_algebra n1
      (((etaleAbelianInverseImage.{u, u + 1} c').obj
        ((etaleAbelianInverseImage.{u, u + 1} e).obj M)).obj.map_comp _ _).symm n2
  exact hL.trans (square_algebra hTR hk₁ hk₂h hinv hgeom)

end Square

end Stacks.EtaleCohomology

end
