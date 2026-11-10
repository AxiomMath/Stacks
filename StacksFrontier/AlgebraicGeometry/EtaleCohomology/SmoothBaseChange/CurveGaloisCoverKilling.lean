module

public import Mathlib.GroupTheory.Schreier
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.CurveFirstDegreeReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.FiniteFieldPoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.GaloisCoverSplitting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.TorsorCover

/-!
# A class of degree one with finite constant coefficients dies on a split Galois cover

Let `X` be a geometrically connected scheme over a field `k` with a rational point `x`, let
`E/k` be a field extension and `L` an algebraically closed extension of `E`, and let `S` be a
finite abelian group annihilated by `n`. For every `ζ ∈ H^1(X_E, S)` there are a subextension
`E ⊆ E' ⊆ L` of finite degree and a Galois cover `Z ⟶ X_{E'}`, with group of order dividing a
power of `n` and split over the rational point `x_{E'}`, on which `ζ` restricts to zero.

This is the geometric core of the case `q = 1` of the proof of [Stacks, Tag 0EYT]. The class `ζ`
is killed by an `S`-torsor `V ⟶ X_E` (`Stacks.EtaleCohomology.exists_torsorCover`). The fibre of
`V` over `x_E` is finite over `Spec E`, so a geometric point of it is defined over a finite
subextension `E'` (`Stacks.EtaleCohomology.exists_finiteDimensional_factorization_of_isFinite`).
Over `X_{E'}` the base change of `V` is still an `S`-torsor, and has an `E'`-point over `x_{E'}`;
its connected component through that point is a Galois cover with group a subgroup of `S`
(`Stacks.EtaleCohomology.exists_isGaloisCover_of_torsor`), the component is open in the torsor so
the `E'`-point lies on it, and a Galois cover with a section over `x_{E'}` is split there
(`Stacks.EtaleCohomology.isSplitOver_of_isGaloisCover`).

## Main definitions

* `Stacks.EtaleCohomology.Etale.toFiniteEtaleOverHom` — a morphism of étale schemes finite over
  the base, as a morphism of finite étale covers.
* `Stacks.EtaleCohomology.pullbackSpectrumMap` — the projection `X_{E'} ⟶ X_E`.

## Main results

* `Stacks.EtaleCohomology.exists_galoisCover_restriction_eq_zero`.

## References

* [Stacks Project, Tag 0EYT](https://stacks.math.columbia.edu/tag/0EYT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] hasExt_sheaf_smallEtale_succ

section Etale

variable {Y : Scheme.{u}}

/-- A morphism of étale `Y`-schemes finite over `Y`, as a morphism in `FÉt_Y` between the
objects `MorphismProperty.Over.mk ⊤ V.hom ⟨hV, V.prop⟩` they define. -/
def Etale.toFiniteEtaleOverHom {V W : Y.Etale} (hV : IsFinite V.hom) (hW : IsFinite W.hom)
    (φ : V ⟶ W) :
    (MorphismProperty.Over.mk ⊤ V.hom ⟨hV, V.prop⟩ : FiniteEtaleOver Y) ⟶
      (MorphismProperty.Over.mk ⊤ W.hom ⟨hW, W.prop⟩ : FiniteEtaleOver Y) :=
  MorphismProperty.Over.homMk φ.left (MorphismProperty.Over.w φ)

/-- The fibre of the point of the small étale site attached to a geometric point is the
geometric fibre. -/
def pointSmallEtaleFiberEquiv (y : GeometricPoint Y) (V : Y.Etale) (hV : IsFinite V.hom) :
    (Scheme.pointSmallEtale y.hom).fiber.obj V ≃
      finiteEtaleFiber y (MorphismProperty.Over.mk ⊤ V.hom ⟨hV, V.prop⟩ : FiniteEtaleOver Y) where
  toFun l := ⟨l.left, Over.w l⟩
  invFun a := Over.homMk a.1 a.2
  left_inv _ := Over.OverMorphism.ext rfl
  right_inv _ := rfl

/-- A simply transitive action on the fibres of the points of the small étale site is a simply
transitive action on the geometric fibres. -/
theorem existsUnique_finiteEtaleFiber_of_pointSmallEtale {M : Type*} (V : Y.Etale)
    (hV : IsFinite V.hom) (α : M → (V ⟶ V)) (y : GeometricPoint Y)
    (h : ∀ l l' : (Scheme.pointSmallEtale y.hom).fiber.obj V,
      ∃! m : M, (Scheme.pointSmallEtale y.hom).fiber.map (α m) l = l')
    (a b : finiteEtaleFiber y
      (MorphismProperty.Over.mk ⊤ V.hom ⟨hV, V.prop⟩ : FiniteEtaleOver Y)) :
    ∃! m : M, (finiteEtaleFiberFunctor y).map (Etale.toFiniteEtaleOverHom hV hV (α m)) a = b := by
  let e := pointSmallEtaleFiberEquiv y V hV
  have hnat : ∀ m l, e ((Scheme.pointSmallEtale y.hom).fiber.map (α m) l) =
      (finiteEtaleFiberFunctor y).map (Etale.toFiniteEtaleOverHom hV hV (α m)) (e l) :=
    fun _ _ => rfl
  obtain ⟨m, hm, hu⟩ := h (e.symm a) (e.symm b)
  refine ⟨m, ?_, fun m' hm' => hu m' (e.injective ?_)⟩
  · have := congrArg e hm
    rwa [hnat, e.apply_symm_apply, e.apply_symm_apply] at this
  · rw [hnat, e.apply_symm_apply, e.apply_symm_apply, hm']

end Etale

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The projection `X_{E'} ⟶ X_E`** for a tower `k ⊆ E ⊆ E'`. -/
def pullbackSpectrumMap (E E' : Type u) [Field E] [Field E'] [Algebra k E] [Algebra k E']
    [Algebra E E'] [IsScalarTower k E E'] :
    pullback (spectrumMap k E') f ⟶ pullback (spectrumMap k E) f :=
  pullback.lift (pullback.fst _ _ ≫ spectrumMap E E') (pullback.snd _ _) (by
    rw [Category.assoc, spectrumMap_comp_spectrumMap k E E', pullback.condition])

/-- The composite of `pullbackSpectrumMap f E E'` with the first projection to `Spec E` is the
first projection followed by `Spec E' ⟶ Spec E`. -/
theorem pullbackSpectrumMap_fst (E E' : Type u) [Field E] [Field E'] [Algebra k E] [Algebra k E']
    [Algebra E E'] [IsScalarTower k E E'] :
    pullbackSpectrumMap f E E' ≫ pullback.fst _ _ = pullback.fst _ _ ≫ spectrumMap E E' :=
  pullback.lift_fst _ _ _

/-- The projection `pullbackSpectrumMap f E E'` commutes with the second projections to `X`. -/
theorem pullbackSpectrumMap_snd (E E' : Type u) [Field E] [Field E'] [Algebra k E] [Algebra k E']
    [Algebra E E'] [IsScalarTower k E E'] :
    pullbackSpectrumMap f E E' ≫ pullback.snd _ _ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

/-- The base change of a rational point along `k ⊆ E ⊆ E'` is compatible with the projection
`X_{E'} ⟶ X_E`. -/
theorem basePoint_comp_pullbackSpectrumMap (E E' : Type u) [Field E] [Field E'] [Algebra k E]
    [Algebra k E'] [Algebra E E'] [IsScalarTower k E E'] (x : Spec (.of k) ⟶ X)
    (hx : x ≫ f = 𝟙 _) :
    basePoint f E' x hx ≫ pullbackSpectrumMap f E E' = spectrumMap E E' ≫ basePoint f E x hx := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackSpectrumMap_fst, Category.assoc, basePoint, basePoint,
      pullback.lift_fst_assoc, pullback.lift_fst, Category.id_comp, Category.comp_id]
  · rw [Category.assoc, pullbackSpectrumMap_snd, Category.assoc, basePoint, basePoint,
      pullback.lift_snd, pullback.lift_snd, ← Category.assoc, spectrumMap_comp_spectrumMap k E E']

/-- **A class of degree one with finite constant coefficients dies on a Galois cover split over
the rational point.** Let `X` be geometrically connected over `k`, with a rational point `x`, let
`E/k` be an extension, `L/E` an algebraically closed extension, and `S` a finite abelian group
annihilated by `n`. For every `ζ ∈ H^1(X_E, S)` there are an extension `E'/E` of finite degree
with an embedding `E' ⟶ L` over `E`, and a Galois cover `p : Z ⟶ X_{E'}`, whose group has order
dividing a power of `n` and which is split over `x_{E'}`, such that `ζ` restricts to zero along
`Z ⟶ X_{E'} ⟶ X_E`. The extension is a subextension of `L/E`, returned as an abstract field so
that its algebra structures are fixed once and for all. -/
theorem exists_galoisCover_restriction_eq_zero [GeometricallyConnected f]
    (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) {E L : Type u} [Field E] [Field L] [IsAlgClosed L]
    [Algebra k E] [Algebra E L] [Algebra k L] [IsScalarTower k E L]
    (S : AddCommGrpCat.{u + 1}) [Finite S] {n : ℕ} (hS : ∀ s : S, n • s = 0)
    (ζ : Sheaf.H.{u + 1, u + 1} ((constantSheaf (pullback (spectrumMap k E) f).smallEtaleTopology
      AddCommGrpCat.{u + 1}).obj S) 1) :
    ∃ (E' : Type u) (_ : Field E') (_ : Algebra E E') (_ : Algebra k E')
      (_ : IsScalarTower k E E') (_ : FiniteDimensional E E') (_ : E' →ₐ[E] L) (Z : Scheme.{u})
      (p : Z ⟶ pullback (spectrumMap k E') f),
      IsGaloisCover p ∧ (∃ m : ℕ, Nat.card (Aut (Over.mk p)) ∣ n ^ m) ∧
        IsSplitOver p (basePoint f E' x hx) ∧
        etaleCohomologyRestrictionMap.{u, u + 1, u + 1} (p ≫ pullbackSpectrumMap f E E') _ 1 ζ =
          0 := by
  have := connectedSpace_pullback_spectrumMap f E
  obtain ⟨V, α, hVfin, hζV, hα, hα0, htors⟩ := exists_torsorCover S ζ
  let V₁ : FiniteEtaleOver _ := MorphismProperty.Over.mk ⊤ V.hom ⟨hVfin, V.prop⟩
  let α₁ : S → (V₁ ⟶ V₁) := fun m => Etale.toFiniteEtaleOverHom hVfin hVfin (α m)
  have hα₁ : ∀ m m', α₁ (m + m') = α₁ m ≫ α₁ m' := fun m m' =>
    MorphismProperty.Over.Hom.ext (by
      change (α (m + m')).left = (α m).left ≫ (α m').left
      rw [hα]
      rfl)
  have hα₁0 : α₁ 0 = 𝟙 V₁ := MorphismProperty.Over.Hom.ext (by
    change (α 0).left = 𝟙 _
    rw [hα0]
    rfl)
  have htors₁ : ∀ (z : GeometricPoint (pullback (spectrumMap k E) f)) (a b : finiteEtaleFiber z V₁),
      ∃! m : S, (finiteEtaleFiberFunctor z).map (α₁ m) a = b := fun z =>
    existsUnique_finiteEtaleFiber_of_pointSmallEtale V hVfin α z (htors z.hom).2
  -- a geometric point of `V` over `x_E` is defined over a finite subextension `E'`
  let xE := basePoint f E x hx
  let xbar : GeometricPoint (pullback (spectrumMap k E) f) :=
    { residueField := L
      hom := spectrumMap E L ≫ xE }
  obtain ⟨l⟩ := (htors xbar.hom).1.map (pointSmallEtaleFiberEquiv xbar V hVfin)
  have hl : l.1 ≫ V.hom = spectrumMap E L ≫ xE := l.2
  obtain ⟨E', hE', t, ht₁, ht₂⟩ := exists_finiteDimensional_factorization_of_isFinite
    (pullback.snd V.hom xE) (pullback.lift l.1 (spectrumMap E L) hl) (pullback.lift_snd _ _ _)
  let a₀ : Spec (.of E') ⟶ V.left := t ≫ pullback.fst _ _
  have ha₀ : a₀ ≫ V.hom = spectrumMap E E' ≫ xE := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ht₁]
  -- base change of the torsor to `X_{E'}`
  have := connectedSpace_pullback_spectrumMap f E'
  let g := pullbackSpectrumMap f E E'
  let V₂ := (finiteEtaleBaseChange g).obj V₁
  let α₂ : S → (V₂ ⟶ V₂) := fun m => (finiteEtaleBaseChange g).map (α₁ m)
  have hα₂ : ∀ m m', α₂ (m + m') = α₂ m ≫ α₂ m' := fun m m' => by
    simp only [α₂, hα₁, Functor.map_comp]
  have hα₂0 : α₂ 0 = 𝟙 V₂ := by
    change (finiteEtaleBaseChange g).map (α₁ 0) = 𝟙 _
    rw [hα₁0, CategoryTheory.Functor.map_id]
  let xE' := basePoint f E' x hx
  have hg : xE' ≫ g = spectrumMap E E' ≫ xE := basePoint_comp_pullbackSpectrumMap f E E' x hx
  let a₂ : Spec (.of E') ⟶ V₂.left := pullback.lift a₀ xE' (by rw [hg]; exact ha₀)
  have ha₂ : a₂ ≫ V₂.hom = xE' := pullback.lift_snd _ _ _
  let xbar' : GeometricPoint (pullback (spectrumMap k E') f) :=
    { residueField := L
      hom := spectrumMap E' L ≫ xE' }
  let a : finiteEtaleFiber xbar' V₂ := ⟨spectrumMap E' L ≫ a₂, by rw [Category.assoc, ha₂]⟩
  obtain ⟨A, i, c, hi, hc, hgal, hcard⟩ := exists_isGaloisCover_of_torsor xbar' V₂ α₂ hα₂ hα₂0
    (fun a b => existsUnique_finiteEtaleBaseChange_map g xbar' V₁ α₁ (htors₁ _) a b) a
  -- the component is open in the torsor, so the `E'`-point lies on it
  have : Mono i.left := mono_left_of_mono i
  have : Etale i.left := etale_hom_left i
  have : IsOpenImmersion i.left := IsOpenImmersion.of_flat_of_mono i.left
  have hrange : Set.range a₂.base ⊆ Set.range i.left.base := by
    rintro _ ⟨q, rfl⟩
    refine ⟨c.1.base default, ?_⟩
    rw [show q = (spectrumMap E' L).base default from Subsingleton.elim _ _,
      ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hc]
  let σ₀ := IsOpenImmersion.lift i.left a₂ hrange
  have hσ₀ : σ₀ ≫ A.hom = xE' := by
    rw [← MorphismProperty.Over.w i, ← Category.assoc, IsOpenImmersion.lift_fac, ha₂]
  refine ⟨E', inferInstance, inferInstance, inferInstance, inferInstance, hE', E'.val, A.left,
    A.hom, hgal, ⟨AddGroup.rank S, hcard.trans
      (card_dvd_exponent_nsmul_rank' S hS)⟩,
    isSplitOver_of_isGaloisCover { residueField := L, hom := spectrumMap E' L } xE' A hgal σ₀ hσ₀,
    ?_⟩
  have hfac : A.hom ≫ g = (i.left ≫ finiteEtaleBaseChangeProj g V₁) ≫ V₁.hom := by
    rw [← MorphismProperty.Over.w i, Category.assoc, Category.assoc,
      finiteEtaleBaseChangeProj_comp_hom]
  have h0 : etaleCohomologyRestrictionMap.{u, u + 1, u + 1} V₁.hom
      ((constantSheaf (pullback (spectrumMap k E) f).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        S) 1 ζ = 0 := hζV
  rw [← etaleCohomologyMapTo_id, etaleCohomologyMapTo_eq_comp_restriction _ _ _ hfac, h0, map_zero]

end Stacks.EtaleCohomology

end
