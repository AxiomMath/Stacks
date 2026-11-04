module

public import StacksFrontier.RingTheory.Dualizing.DualizingDerivedHom
public import StacksFrontier.RingTheory.Dualizing.LocalizationCriterion
import StacksFrontier.Homology.HomComplex.RHom.BaseChange
import all StacksFrontier.Homology.HomComplex.RHom.BaseChange.ModelRestrictScalars

/-!
# Naturality of the derived-Hom comparisons of [stacks 0A63] and [stacks 0A7C]

The Hom computation behind [stacks 0AX0] identifies `End_{D(B)}(RHom_A(B, ω))` with `B` for a
finite ring map `f : A → B` and a dualizing complex `ω` over `A`. An identification of additive
groups is not enough: the statement that is needed downstream is `B`-linear, and a `B`-algebra
`E` carrying an `A`-linear isomorphism `E ≃ₗ[A] B` need not satisfy `B ≃ E` — take `A = k`,
`B = k[x]/(x²)`, `E = k[y]/(y²)` with `x ↦ 0`. So the `B`-action has to be *tracked* along the
chain of identifications rather than inferred at the end, and tracking it means knowing that each
link is natural in the variable the action moves.

Two of the links carry no naturality statement in the library, and this file supplies them; the
third, naturality of the biduality morphism of [stacks 0A7C], is already available as
`Dualizing.bidualityMor_naturality`.

* `Dualizing.derivedInternalHomModelIso₂` computes `RHom_R(X, -)` on a bounded-below complex of
  injectives. `Dualizing.derivedInternalHomModelIso₂_naturality_left` says it is natural in the
  first variable: a chain map `g : L' ⟶ L` between the chosen models of `X` and `X'` goes to
  precomposition `g^*` on the Hom complexes.
* The identification of `Hom_{D(R)}(X, ω)` with `H⁰(RHom_R(X, ω))` is replaced here by the
  adjunction-level `Dualizing.homUnitAddEquiv`, which identifies `Hom_{D(R)}(X, ω)` with
  `Hom_{D(R)}(1, RHom_R(X, ω))`; `Dualizing.homUnitAddEquiv_naturality` turns precomposition in
  the first variable into postcomposition with the derived dual. This is a cleaner carrier of the
  same information than a compatibility statement for
  `Dualizing.extAddEquivHomologyDerivedInternalHom`, whose construction passes through a choice of
  model for the first variable and therefore has no naturality in an arbitrary morphism of the
  derived category.

## Main results

* `Dualizing.homUnitAddEquiv`, `Dualizing.homUnitAddEquiv_naturality` — morphisms into `ω` are
  morphisms out of the tensor unit into the derived dual, naturally.
* `Dualizing.derivedInternalHomModelIso₂_naturality_left` — the two-variable K-injective model is
  natural in its first variable.

Three auxiliary naturality statements that the last of these rests on are proved on the way:
`Dualizing.homComplexCongrIso₂_naturality_left`,
`Dualizing.homComplexRestrictScalarsIso₂_naturality_left` and
`Dualizing.precomp_postcomp_comm`.

## Implementation notes

The model comparison `Dualizing.derivedInternalHomModelIso₂` is a composite of four isomorphisms:
the K-injective Hom model over the lifted ring `ULift R`, the factorization of restriction of
scalars through the localization, the compatibility of the Hom complex with restriction along a
ring isomorphism, and conjugation by the unit of the scalar equivalence. Each of the four is
natural, and `Dualizing.paste₄` pastes the four squares.

The naturality of the first factor is `Stacks.DerivedHom.BaseChange.homModelIso_naturality`, which
is `private`; this module reaches it with `import all` rather than re-proving it.

Two transparency hazards shape the proofs. `StacksDraft.DerivedHom.derivedHomAdjunction` is
`@[no_expose]`, so a `rw` or `simp` whose motive crosses between the
`Stacks.DerivedHom.ScalarTransportedInternalHom.hom` spelling and the
`DerivedInternalHom.Model.hom` spelling fails its type-correctness check even though the two sides
are `rfl`-equal. The proof of
`Dualizing.derivedInternalHomModelIso₂_naturality_left` therefore runs entirely in the unfolded
spelling and crosses back once, in term mode, at the closing `exact`. Separately, the carrier of a
Hom complex is a `Cochain` type only up to unfolding `CochainComplex.HomComplexR`, so the
degreewise computations are stated by `change` and closed by `exact` rather than by `simp`.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0A7C](https://stacks.math.columbia.edu/tag/0A7C)
* [Stacks Project, Tag 0AX0](https://stacks.math.columbia.edu/tag/0AX0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex

attribute [local instance] HasDerivedCategory.standard

namespace Dualizing

universe u v w

/-! ### Pasting commuting squares -/

/-- Pasting four commuting squares in a row: a chain of four horizontal isomorphisms, each
compatible with a vertical map, is compatible with the first and last vertical maps. -/
theorem paste₄ {𝒞 : Type*} [Category 𝒞] {A₀ A₁ A₂ A₃ A₄ B₀ B₁ B₂ B₃ B₄ : 𝒞}
    {p₀ : A₀ ⟶ B₀} {p₁ : A₁ ⟶ B₁} {p₂ : A₂ ⟶ B₂} {p₃ : A₃ ⟶ B₃} {p₄ : A₄ ⟶ B₄}
    {i₁ : A₀ ⟶ A₁} {i₂ : A₁ ⟶ A₂} {i₃ : A₂ ⟶ A₃} {i₄ : A₃ ⟶ A₄}
    {j₁ : B₀ ⟶ B₁} {j₂ : B₁ ⟶ B₂} {j₃ : B₂ ⟶ B₃} {j₄ : B₃ ⟶ B₄}
    (h₁ : p₀ ≫ j₁ = i₁ ≫ p₁) (h₂ : p₁ ≫ j₂ = i₂ ≫ p₂)
    (h₃ : p₂ ≫ j₃ = i₃ ≫ p₃) (h₄ : p₃ ≫ j₄ = i₄ ≫ p₄) :
    p₀ ≫ j₁ ≫ j₂ ≫ j₃ ≫ j₄ = (i₁ ≫ i₂ ≫ i₃ ≫ i₄) ≫ p₄ := by
  rw [← Category.assoc p₀, h₁, Category.assoc, ← Category.assoc p₁, h₂, Category.assoc,
    ← Category.assoc p₂, h₃, Category.assoc, h₄]
  simp only [Category.assoc]

/-! ### Morphisms into `ω` as morphisms out of the tensor unit -/

section Unit

variable {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (d : StacksDraft.DerivedHom.DerivedHomAdjunction R)

/-- Precomposition with an isomorphism, as an additive equivalence of morphism groups. -/
def precompAddEquiv {C : Type*} [Category C] [Preadditive C] {X Y : C} (e : X ≅ Y) (Z : C) :
    (Y ⟶ Z) ≃+ (X ⟶ Z) where
  toFun f := e.hom ≫ f
  invFun g := e.inv ≫ g
  left_inv f := by simp
  right_inv g := by simp
  map_add' f g := Preadditive.comp_add _ _ _ _ _ _

variable (one : DerivedCategory (ModuleCat.{v} R))
    (lam : ∀ K : DerivedCategory (ModuleCat.{v} R), d.tensor.obj (one, K) ≅ K)

/-- **Morphisms into `ω` are morphisms out of the tensor unit into the derived dual.** The
transpose of a morphism `1 ⟶ RHom(X, ω)` under the tensor--Hom adjunction is a morphism
`1 ⊗ X ⟶ ω`, and the left unitor turns that into a morphism `X ⟶ ω`. -/
def homUnitAddEquiv (ω X : DerivedCategory (ModuleCat.{v} R)) :
    (one ⟶ d.hom.obj (Opposite.op X, ω)) ≃+ (X ⟶ ω) :=
  (d.homEquiv one X ω).trans (precompAddEquiv (lam X).symm ω)

/-- **`Dualizing.homUnitAddEquiv` is natural in `X`:** precomposition with `ψ` on morphisms into
`ω` corresponds to postcomposition with the derived dual of `ψ`. Only naturality of the left
unitor is used. -/
theorem homUnitAddEquiv_naturality
    (hlam : StacksDraft.DerivedHom.DerivedHomAdjunction.IsUnitorNatural d one lam)
    (ω : DerivedCategory (ModuleCat.{v} R))
    {X X' : DerivedCategory (ModuleCat.{v} R)} (ψ : X' ⟶ X)
    (α : one ⟶ d.hom.obj (Opposite.op X, ω)) :
    homUnitAddEquiv d one lam ω X'
        (α ≫ d.hom.map ((ψ.op, 𝟙 ω) : (Opposite.op X, ω) ⟶ (Opposite.op X', ω))) =
      ψ ≫ homUnitAddEquiv d one lam ω X α := by
  have hn : d.tensor.map ((𝟙 one, ψ) : (one, X') ⟶ (one, X)) ≫ (lam X).hom =
      (lam X').hom ≫ ψ := hlam ψ
  have hn' : (lam X').inv ≫ d.tensor.map ((𝟙 one, ψ) : (one, X') ⟶ (one, X)) =
      ψ ≫ (lam X).inv :=
    (CommSq.vert_inv ⟨hn⟩).w.symm
  change (lam X').inv ≫ d.homEquiv one X' ω _ = _
  rw [d.homEquiv_dinaturality ψ α, ← Category.assoc, hn', Category.assoc]
  rfl

end Unit

/-! ### Naturality of pre- and postcomposition on Hom complexes -/

section PreComp

variable (Rr : Type*) [Ring Rr] {C : Type*} [Category C] [Preadditive C] [Linear Rr C]

/-- Pre- and postcomposition on Hom complexes commute. -/
theorem precomp_postcomp_comm (L' L M M' : CochainComplex C ℤ) (g : L' ⟶ L) (h : M ⟶ M') :
    Stacks.HomComplex.TensorHomMap.postcomp Rr L M M' h ≫
        Stacks.HomComplex.TensorHomMap.precomp Rr L' L M' g =
      Stacks.HomComplex.TensorHomMap.precomp Rr L' L M g ≫
        Stacks.HomComplex.TensorHomMap.postcomp Rr L' M M' h := by
  refine HomologicalComplex.hom_ext _ _ fun n => ModuleCat.hom_ext <| LinearMap.ext fun z => ?_
  change Cochain.comp (Cochain.ofHom g)
      (Cochain.comp z (Cochain.ofHom h) (add_zero n)) (zero_add n) =
    Cochain.comp (Cochain.comp (Cochain.ofHom g) z (zero_add n)) (Cochain.ofHom h) (add_zero n)
  exact (Cochain.comp_assoc_of_first_is_zero_cochain (Cochain.ofHom g) z
    (Cochain.ofHom h) (add_zero n)).symm

end PreComp

section Congr

variable {R : Type u} [CommRing R]

/-- **`Dualizing.homComplexCongrIso₂` is natural in the first variable.** -/
theorem homComplexCongrIso₂_naturality_left
    {I₁ I₁' J₁ J₁' I₂ J₂ : CochainComplex (ModuleCat.{v} R) ℤ}
    (e₁ : I₁ ≅ J₁) (e₁' : I₁' ≅ J₁') (e₂ : I₂ ≅ J₂)
    (p : I₁' ⟶ I₁) (q : J₁' ⟶ J₁) (hpq : e₁'.hom ≫ q = p ≫ e₁.hom) :
    Stacks.HomComplex.TensorHomMap.precomp R I₁' I₁ I₂ p ≫ (homComplexCongrIso₂ e₁' e₂).hom =
      (homComplexCongrIso₂ e₁ e₂).hom ≫ Stacks.HomComplex.TensorHomMap.precomp R J₁' J₁ J₂ q := by
  have hqp : q ≫ e₁.inv = e₁'.inv ≫ p :=
    (CommSq.vert_inv (g := e₁') (h := e₁) ⟨hpq.symm⟩).w
  dsimp only [homComplexCongrIso₂, Iso.trans_hom]
  rw [← Category.assoc, ← Stacks.HomComplex.TensorHomMap.precomp_comp, ← hqp,
    Stacks.HomComplex.TensorHomMap.precomp_comp,
    Category.assoc, Category.assoc, ← precomp_postcomp_comm]

end Congr

section RestrictNat

variable {R : Type u} [CommRing R]

/-- **`Dualizing.homComplexRestrictScalarsIso₂` is natural in the first variable.** -/
theorem homComplexRestrictScalarsIso₂_naturality_left
    {S : Type w} [CommRing S] (e : S ≃+* R) {I I' J : CochainComplex (ModuleCat.{v} R) ℤ}
    (a : I' ⟶ I) :
    ((ModuleCat.restrictScalars.{v} e.toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (Stacks.HomComplex.TensorHomMap.precomp R I' I J a) ≫
        (homComplexRestrictScalarsIso₂ e I' J).hom =
      (homComplexRestrictScalarsIso₂ e I J).hom ≫
        Stacks.HomComplex.TensorHomMap.precomp S
          (((ModuleCat.restrictScalars.{v} e.toRingHom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj I')
          (((ModuleCat.restrictScalars.{v} e.toRingHom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj I)
          (((ModuleCat.restrictScalars.{v} e.toRingHom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj J)
          (((ModuleCat.restrictScalars.{v} e.toRingHom).mapHomologicalComplex
            (ComplexShape.up ℤ)).map a) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ModuleCat.hom_ext <| LinearMap.ext fun z => ?_
  dsimp only [homComplexRestrictScalarsIso₂]
  change Cochain.map (Cochain.comp (Cochain.ofHom a) z (zero_add n))
      (ModuleCat.restrictScalars.{v} e.toRingHom) =
    Cochain.comp
      (Cochain.ofHom (((ModuleCat.restrictScalars.{v} e.toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).map a))
      (Cochain.map z (ModuleCat.restrictScalars.{v} e.toRingHom)) (zero_add n)
  have h1 : Cochain.map (Cochain.ofHom a) (ModuleCat.restrictScalars.{v} e.toRingHom) =
      Cochain.ofHom (((ModuleCat.restrictScalars.{v} e.toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).map a) :=
    Cochain.map_ofHom I' I a (ModuleCat.restrictScalars.{v} e.toRingHom)
  exact (Cochain.map_comp J (Cochain.ofHom a) z (zero_add n)
      (ModuleCat.restrictScalars.{v} e.toRingHom)).trans
    (congrArg (fun w => Cochain.comp w
      (Cochain.map z (ModuleCat.restrictScalars.{v} e.toRingHom)) (zero_add n)) h1)

end RestrictNat

/-! ### Naturality of the two-variable K-injective model -/

section Model

variable {R : Type u} [CommRing R]

/-- The bifunctor underlying the ordinary Hom complex, applied to a precomposition pair. -/
theorem homComplexFunctorMapPair {S : Type w} [CommRing S]
    (LS LS' J : CochainComplex (ModuleCat.{w} S) ℤ) (a : LS' ⟶ LS) :
    (StacksDraft.DerivedHom.Model.homComplexFunctor S).map
        (CategoryTheory.Prod.mkHom (Quiver.Hom.op a) (𝟙 J)) =
      Stacks.HomComplex.TensorHomMap.precomp S LS' LS J a := by
  dsimp only [StacksDraft.DerivedHom.Model.homComplexFunctor, CategoryTheory.Prod.mkHom,
    Quiver.Hom.unop_op]
  rw [Stacks.HomComplex.TensorHomMap.postcomp_id, Category.comp_id]

variable (R)

/-- Restriction of scalars along the ring isomorphism `ULift R ≃+* R`: an `R`-module read as a
`ULift R`-module. -/
abbrev scalarsUp : ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} (ULift.{max u v} R) :=
  ModuleCat.restrictScalars.{max u v}
    (ULift.ringEquiv : ULift.{max u v} R ≃+* R).toRingHom

/-- Restriction of scalars along the inverse of `ULift R ≃+* R`: a `ULift R`-module read as an
`R`-module. -/
abbrev scalarsDown : ModuleCat.{max u v} (ULift.{max u v} R) ⥤ ModuleCat.{max u v} R :=
  ModuleCat.restrictScalars.{max u v}
    (ULift.ringEquiv : ULift.{max u v} R ≃+* R).symm.toRingHom

variable {R}

/-- **The two-variable K-injective model for derived internal Hom is natural in its first
variable.** If `g : L' ⟶ L` is a chain map and `φ : X' ⟶ X` a morphism of the derived category
compatible with `g` through the chosen models, then
`Dualizing.derivedInternalHomModelIso₂` carries `RHom_R(φ, ω)` to precomposition with `g` on the
Hom complexes. -/
theorem derivedInternalHomModelIso₂_naturality_left
    {X X' : DerivedCategory (ModuleCat.{max u v} R)}
    {L L' : CochainComplex (ModuleCat.{max u v} R) ℤ}
    (eL : X ≅ DerivedCategory.Q.obj L) (eL' : X' ≅ DerivedCategory.Q.obj L')
    (g : L' ⟶ L) (φ : X' ⟶ X) (hφ : φ ≫ eL.hom = eL'.hom ≫ DerivedCategory.Q.map g)
    (I : CochainComplex (ModuleCat.{max u v} R) ℤ) (a : ℤ)
    (hGE : I.IsStrictlyGE a) (hInj : ∀ i, Injective (I.X i)) :
    (Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, max u v} R).map
          ((φ.op, 𝟙 (DerivedCategory.Q.obj I)) :
            (Opposite.op X, DerivedCategory.Q.obj I) ⟶
              (Opposite.op X', DerivedCategory.Q.obj I)) ≫
        (derivedInternalHomModelIso₂.{u, v} L' eL' I a hGE hInj).hom =
      (derivedInternalHomModelIso₂.{u, v} L eL I a hGE hInj).hom ≫
        DerivedCategory.Q.map (Stacks.HomComplex.TensorHomMap.precomp R L' L I g) := by
  have hJGE : CochainComplex.IsStrictlyGE
      (((scalarsUp.{u, v} R).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact Functor.map_isZero (scalarsUp.{u, v} R)
      ((CochainComplex.isStrictlyGE_iff I a).mp hGE i hi)
  have hJinj : ∀ i, Injective ((((scalarsUp.{u, v} R).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I).X i) := by
    intro i
    change Injective ((scalarsUp.{u, v} R).obj (I.X i))
    let : Injective (I.X i) := hInj i
    infer_instance
  have hJ : CochainComplex.IsKInjective
      (((scalarsUp.{u, v} R).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    CochainComplex.isKInjective_of_injective _ a
  -- square 1 : the K-injective Hom model is natural in the source complex
  have hg : (scalarsUp.{u, v} R).mapDerivedCategory.map φ ≫
        ((scalarsUp.{u, v} R).mapDerivedCategory.map eL.hom ≫
          ((scalarsUp.{u, v} R).mapDerivedCategoryFactors.app L).hom) =
      ((scalarsUp.{u, v} R).mapDerivedCategory.map eL'.hom ≫
          ((scalarsUp.{u, v} R).mapDerivedCategoryFactors.app L').hom) ≫
        DerivedCategory.Q.map
          (((scalarsUp.{u, v} R).mapHomologicalComplex (ComplexShape.up ℤ)).map g) := by
    rw [← Category.assoc, ← Functor.map_comp, hφ, Functor.map_comp, Category.assoc,
      Category.assoc]
    exact congrArg (fun z => (scalarsUp.{u, v} R).mapDerivedCategory.map eL'.hom ≫ z)
      ((scalarsUp.{u, v} R).mapDerivedCategoryFactors.hom.naturality g)
  have hh : (scalarsUp.{u, v} R).mapDerivedCategory.map (𝟙 (DerivedCategory.Q.obj I)) ≫
        ((scalarsUp.{u, v} R).mapDerivedCategoryFactors.app I).hom =
      ((scalarsUp.{u, v} R).mapDerivedCategoryFactors.app I).hom ≫
        DerivedCategory.Q.map (𝟙 (((scalarsUp.{u, v} R).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I)) := by
    simp
  have hnat := Stacks.DerivedHom.BaseChange.homModelIso_naturality
    ((scalarsUp.{u, v} R).mapDerivedCategory.mapIso eL ≪≫
      (scalarsUp.{u, v} R).mapDerivedCategoryFactors.app L)
    ((scalarsUp.{u, v} R).mapDerivedCategory.mapIso eL' ≪≫
      (scalarsUp.{u, v} R).mapDerivedCategoryFactors.app L')
    ((scalarsUp.{u, v} R).mapDerivedCategoryFactors.app I)
    ((scalarsUp.{u, v} R).mapDerivedCategoryFactors.app I)
    (((scalarsUp.{u, v} R).mapHomologicalComplex (ComplexShape.up ℤ)).map g)
    (𝟙 (((scalarsUp.{u, v} R).mapHomologicalComplex (ComplexShape.up ℤ)).obj I))
    ((scalarsUp.{u, v} R).mapDerivedCategory.map φ)
    ((scalarsUp.{u, v} R).mapDerivedCategory.map (𝟙 (DerivedCategory.Q.obj I))) hg hh
  rw [homComplexFunctorMapPair] at hnat
  have h₁ : (scalarsDown.{u, v} R).mapDerivedCategory.map
          ((StacksDraft.DerivedHom.DerivedInternalHom.Model.hom (ULift.{max u v} R)).map
            (CategoryTheory.Prod.mkHom ((scalarsUp.{u, v} R).mapDerivedCategory.map φ).op
              ((scalarsUp.{u, v} R).mapDerivedCategory.map (𝟙 (DerivedCategory.Q.obj I))))) ≫
        (scalarsDown.{u, v} R).mapDerivedCategory.map
          (Stacks.DerivedHom.BaseChange.homModelIso _ _
            ((scalarsUp.{u, v} R).mapDerivedCategory.mapIso eL' ≪≫
              (scalarsUp.{u, v} R).mapDerivedCategoryFactors.app L')
            ((scalarsUp.{u, v} R).mapDerivedCategoryFactors.app I)).hom =
      (scalarsDown.{u, v} R).mapDerivedCategory.map
          (Stacks.DerivedHom.BaseChange.homModelIso _ _
            ((scalarsUp.{u, v} R).mapDerivedCategory.mapIso eL ≪≫
              (scalarsUp.{u, v} R).mapDerivedCategoryFactors.app L)
            ((scalarsUp.{u, v} R).mapDerivedCategoryFactors.app I)).hom ≫
        (scalarsDown.{u, v} R).mapDerivedCategory.map (DerivedCategory.Q.map
          (Stacks.HomComplex.TensorHomMap.precomp (ULift.{max u v} R) _ _ _
            (((scalarsUp.{u, v} R).mapHomologicalComplex (ComplexShape.up ℤ)).map g))) := by
    rw [← Functor.map_comp, hnat]
    exact Functor.map_comp _ _ _
  -- square 2 : restriction of scalars factors through the localization, naturally
  have h₂ := (scalarsDown.{u, v} R).mapDerivedCategoryFactors.hom.naturality
    (Stacks.HomComplex.TensorHomMap.precomp (ULift.{max u v} R)
      (((scalarsUp.{u, v} R).mapHomologicalComplex (ComplexShape.up ℤ)).obj L')
      (((scalarsUp.{u, v} R).mapHomologicalComplex (ComplexShape.up ℤ)).obj L)
      (((scalarsUp.{u, v} R).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
      (((scalarsUp.{u, v} R).mapHomologicalComplex (ComplexShape.up ℤ)).map g))
  -- square 3 : the Hom complex commutes with restriction along a ring isomorphism
  have h₃ := congrArg DerivedCategory.Q.map
    (homComplexRestrictScalarsIso₂_naturality_left
      (ULift.ringEquiv : ULift.{max u v} R ≃+* R).symm
      (J := ((scalarsUp.{u, v} R).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
      (((scalarsUp.{u, v} R).mapHomologicalComplex (ComplexShape.up ℤ)).map g))
  simp only [Functor.map_comp] at h₃
  -- square 4 : conjugation by the unit of the scalar equivalence
  have h₄ := congrArg DerivedCategory.Q.map
    (homComplexCongrIso₂_naturality_left
      (((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
        (ULift.ringEquiv : ULift.{max u v} R ≃+* R)).mapHomologicalComplex
        (ComplexShape.up ℤ)).unitIso.app L).symm
      (((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
        (ULift.ringEquiv : ULift.{max u v} R ≃+* R)).mapHomologicalComplex
        (ComplexShape.up ℤ)).unitIso.app L').symm
      (((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
        (ULift.ringEquiv : ULift.{max u v} R ≃+* R)).mapHomologicalComplex
        (ComplexShape.up ℤ)).unitIso.app I).symm
      _ g ((((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
        (ULift.ringEquiv : ULift.{max u v} R ≃+* R)).mapHomologicalComplex
        (ComplexShape.up ℤ)).unitIso.inv.naturality g).symm))
  simp only [Functor.map_comp] at h₄
  exact paste₄ h₁ h₂ h₃ h₄

end Model

end Dualizing

end
