module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.Functoriality
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbertRelativeRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.CategoryTheory.Sites.Stack.SiteOverItself

/-!
# The absolute finite Hilbert stack is the relative one over the base

Let `𝒳` be a stack in groupoids over the big fppf site of a scheme `S` and let `d` be a natural
number. The big fppf site is itself a stack in groupoids over itself, through the identity
functor, and this file identifies the absolute finite Hilbert category `ℋ_d(𝒳)` with the relative
one `ℋ_d(𝒳/S)` taken over that stack, and the category `ℋ_d` of degree-`d` finite locally free
covers with `ℋ_d(S/S)`. Both identifications are the two forgetful 1-morphisms of Stacks 05WD.

Under the two identifications the forgetful 1-morphism `ℋ_d(𝒳) ⟶ ℋ_d` becomes the canonical
1-morphism `ℋ_d(𝒳/S) ⟶ ℋ_d(S/S)` of Stacks 05XN attached to the structure 1-morphism of `𝒳`, so
`ℋ_d(𝒳) ⟶ ℋ_d` is representable by algebraic spaces as soon as the structure 1-morphism of `𝒳`
is (Stacks 05YJ).

## Main definitions

* `AlgebraicGeometry.Stack.baseCategory`: the big fppf site of `S` as a category over itself.
* `AlgebraicGeometry.Stack.baseStack`: it is a stack in groupoids over itself.
* `AlgebraicGeometry.Stack.toBaseStack`: the structure 1-morphism of a stack in groupoids over
  the site, read as a 1-morphism into that stack.
* `AlgebraicGeometry.Stack.absoluteHilbertFibered`,
  `AlgebraicGeometry.Stack.finiteCoverFibered` and
  `AlgebraicGeometry.Stack.forgetAbsoluteStructureFibered`: `ℋ_d(𝒳)`, `ℋ_d` and the forgetful
  1-morphism between them, read in the 2-category of categories fibred in groupoids.

## Main results

* `AlgebraicGeometry.Stack.forgetRelativeStructure_base_isEquivalence`: `ℋ_d(𝒳/S) ⟶ ℋ_d(𝒳)` is
  an equivalence.
* `AlgebraicGeometry.Stack.forgetRelativeToFiniteCover_base_isEquivalence`: `ℋ_d(S/S) ⟶ ℋ_d` is
  an equivalence.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_forgetAbsoluteStructure`: **the
  forgetful 1-morphism `ℋ_d(𝒳) ⟶ ℋ_d` is representable by algebraic spaces** when the structure
  1-morphism of `𝒳` is.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_forgetAbsoluteStructure_of_space`:
  the same, when `𝒳` is representable by an algebraic space over `S`.

## References

* [Stacks Project, Tag 05WD](https://stacks.math.columbia.edu/tag/05WD)
* [Stacks Project, Tag 05XN](https://stacks.math.columbia.edu/tag/05XN)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 05YJ](https://stacks.math.columbia.edu/tag/05YJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The big fppf site of `S`, regarded as a category over itself through the identity functor. -/
abbrev baseCategory : BasedCategory.{u, u + 1} (BigFppfOver B S hS) :=
  BasedCategory.ofFunctor (𝟭 (BigFppfOver B S hS))

/-- **The big fppf site of `S` is a stack in groupoids over itself.** -/
def baseStack : StackInGroupoids.{w, u, u, u + 1, u + 1} (BigFppfOver B S hS)
    (BigFppfOver.topology B S hS) where
  toBasedCategory := baseCategory B S hS
  isStackInGroupoids := Functor.isStackInGroupoids_id _ _

variable {B S hS}

variable (𝒳 : StackInGroupoids.{w, u, u, u + 1, u + 1} (BigFppfOver B S hS)
  (BigFppfOver.topology B S hS)) (d : ℕ)

/-- The structure 1-morphism of a stack in groupoids over the big fppf site of `S`, read as a
1-morphism into the site regarded as a stack over itself. -/
def toBaseStack : 𝒳.toBasedCategory ⥤ᵇ baseCategory B S hS where
  toFunctor := 𝒳.toBasedCategory.p
  w := Functor.comp_id _

attribute [local implicit_reducible] BasedCategory.ofFunctor finiteHilbertCategory
  absoluteHilbertCategory finiteCoverCategory baseStack

/-! ### The relative finite Hilbert category over the base -/

/-- A commuting square, conjugated by identifications of its objects, still commutes. -/
private theorem eqToHom_comp_square {C : Type*} [Category C] {x₁ x₂ z₁ z₂ y₁ y₂ u₁ u₂ : C}
    (hx₁ : x₁ = z₁) (hx₂ : x₂ = z₂) (hy₁ : y₁ = u₁) (hy₂ : y₂ = u₂)
    {g : z₁ ⟶ z₂} {f : u₁ ⟶ u₂} {q₁ : z₁ ⟶ u₁} {q₂ : z₂ ⟶ u₂} (hsq : g ≫ q₂ = q₁ ≫ f) :
    (eqToHom hx₁ ≫ g ≫ eqToHom hx₂.symm) ≫ (eqToHom hx₂ ≫ q₂ ≫ eqToHom hy₂.symm) =
      (eqToHom hx₁ ≫ q₁ ≫ eqToHom hy₁.symm) ≫ (eqToHom hy₁ ≫ f ≫ eqToHom hy₂.symm) := by
  subst hx₁ hx₂ hy₁ hy₂
  simpa using hsq

/-- **Forgetting the object of the base and the identification is faithful.** -/
theorem forgetRelativeStructure_base_faithful :
    (forgetRelativeStructure (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳)
      (𝒴 := baseStack B S hS) (F := toBaseStack 𝒳)).toFunctor.Faithful where
  map_injective {P Q φ ψ} h := by
    have hf : φ.f = ψ.f := congrArg (fun t => t.cover.f) h
    refine FiniteHilbert.Hom.ext hf (congrArg (fun t => t.cover.g) h) ?_
      (congrArg AbsoluteHilbert.Hom.a h)
    rw [Functor.eq_of_isHomLift_id_over P.y_over Q.y_over φ.b_over,
      Functor.eq_of_isHomLift_id_over P.y_over Q.y_over ψ.b_over, hf]

/-- **Forgetting the object of the base and the identification is full.** -/
theorem forgetRelativeStructure_base_full :
    (forgetRelativeStructure (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳)
      (𝒴 := baseStack B S hS) (F := toBaseStack 𝒳)).toFunctor.Full where
  map_surjective {P Q} χ := by
    refine ⟨{ f := χ.cover.f
              g := χ.cover.g
              square := χ.cover.square
              b := eqToHom P.y_over ≫ χ.cover.f ≫ eqToHom Q.y_over.symm
              b_over := Functor.isHomLift_idFunctor_eqToHom P.y_over Q.y_over χ.cover.f
              a := χ.a
              a_over := χ.a_over
              compatible := ?_ }, rfl⟩
    have ha : 𝒳.toBasedCategory.p.map χ.a =
        eqToHom P.x_over ≫ χ.cover.g ≫ eqToHom Q.x_over.symm := by
      have := χ.a_over
      exact CategoryTheory.IsHomLift.fac' 𝒳.toBasedCategory.p χ.cover.g χ.a
    change 𝒳.toBasedCategory.p.map χ.a ≫ Q.α = P.α ≫ _
    rw [ha, Functor.eq_of_isHomLift_id_over P.x_over P.y_over P.α_over,
      Functor.eq_of_isHomLift_id_over Q.x_over Q.y_over Q.α_over]
    exact eqToHom_comp_square P.x_over Q.x_over P.y_over Q.y_over χ.cover.square.w

/-- **Forgetting the object of the base and the identification is essentially surjective.** -/
theorem forgetRelativeStructure_base_essSurj :
    (forgetRelativeStructure (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳)
      (𝒴 := baseStack B S hS) (F := toBaseStack 𝒳)).toFunctor.EssSurj where
  mem_essImage R :=
    ⟨{ U := R.U
       Z := R.Z
       q := R.q
       finiteLocallyFree := R.finiteLocallyFree
       y := R.U
       y_over := rfl
       x := R.x
       x_over := R.x_over
       α := eqToHom R.x_over ≫ R.q ≫ eqToHom (rfl : (𝟭 (BigFppfOver B S hS)).obj R.U = R.U).symm
       α_over := Functor.isHomLift_idFunctor_eqToHom R.x_over rfl R.q }, ⟨Iso.refl _⟩⟩

/-- **The forgetful 1-morphism `ℋ_d(𝒳/S) ⟶ ℋ_d(𝒳)` is an equivalence.** -/
theorem forgetRelativeStructure_base_isEquivalence :
    (forgetRelativeStructure (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳)
      (𝒴 := baseStack B S hS) (F := toBaseStack 𝒳)).toFunctor.IsEquivalence where
  faithful := forgetRelativeStructure_base_faithful 𝒳 d
  full := forgetRelativeStructure_base_full 𝒳 d
  essSurj := forgetRelativeStructure_base_essSurj 𝒳 d

/-! ### The category of finite locally free covers as a relative finite Hilbert category -/

/-- **Reading off the cover is faithful on `ℋ_d(S/S)`.** -/
theorem forgetRelativeToFiniteCover_base_faithful :
    (forgetRelativeToFiniteCover (B := B) (S := S) (hS := hS) (d := d)
      (𝒳 := baseStack B S hS) (𝒴 := baseStack B S hS)
      (F := 𝟙 (baseCategory B S hS))).toFunctor.Faithful where
  map_injective {P Q φ ψ} h := by
    have hf : φ.f = ψ.f := congrArg FiniteCover.Hom.f h
    have hg : φ.g = ψ.g := congrArg FiniteCover.Hom.g h
    refine FiniteHilbert.Hom.ext hf hg ?_ ?_
    · rw [Functor.eq_of_isHomLift_id_over P.y_over Q.y_over φ.b_over,
        Functor.eq_of_isHomLift_id_over P.y_over Q.y_over ψ.b_over, hf]
    · rw [Functor.eq_of_isHomLift_id_over P.x_over Q.x_over φ.a_over,
        Functor.eq_of_isHomLift_id_over P.x_over Q.x_over ψ.a_over, hg]

/-- **Reading off the cover is full on `ℋ_d(S/S)`.** -/
theorem forgetRelativeToFiniteCover_base_full :
    (forgetRelativeToFiniteCover (B := B) (S := S) (hS := hS) (d := d)
      (𝒳 := baseStack B S hS) (𝒴 := baseStack B S hS)
      (F := 𝟙 (baseCategory B S hS))).toFunctor.Full where
  map_surjective {P Q} χ := by
    refine ⟨{ f := χ.f
              g := χ.g
              square := χ.square
              b := eqToHom P.y_over ≫ χ.f ≫ eqToHom Q.y_over.symm
              b_over := Functor.isHomLift_idFunctor_eqToHom P.y_over Q.y_over χ.f
              a := eqToHom P.x_over ≫ χ.g ≫ eqToHom Q.x_over.symm
              a_over := Functor.isHomLift_idFunctor_eqToHom P.x_over Q.x_over χ.g
              compatible := ?_ }, rfl⟩
    change (eqToHom P.x_over ≫ χ.g ≫ eqToHom Q.x_over.symm) ≫ Q.α = P.α ≫ _
    rw [Functor.eq_of_isHomLift_id_over P.x_over P.y_over P.α_over,
      Functor.eq_of_isHomLift_id_over Q.x_over Q.y_over Q.α_over]
    exact eqToHom_comp_square P.x_over Q.x_over P.y_over Q.y_over χ.square.w

/-- **Reading off the cover is essentially surjective on `ℋ_d(S/S)`.** -/
theorem forgetRelativeToFiniteCover_base_essSurj :
    (forgetRelativeToFiniteCover (B := B) (S := S) (hS := hS) (d := d)
      (𝒳 := baseStack B S hS) (𝒴 := baseStack B S hS)
      (F := 𝟙 (baseCategory B S hS))).toFunctor.EssSurj where
  mem_essImage C :=
    ⟨{ U := C.U
       Z := C.Z
       q := C.q
       finiteLocallyFree := C.finiteLocallyFree
       y := C.U
       y_over := rfl
       x := C.Z
       x_over := rfl
       α := eqToHom (rfl : (𝟭 (BigFppfOver B S hS)).obj C.Z = C.Z) ≫ C.q ≫
         eqToHom (rfl : (𝟭 (BigFppfOver B S hS)).obj C.U = C.U).symm
       α_over := Functor.isHomLift_idFunctor_eqToHom rfl rfl C.q }, ⟨Iso.refl _⟩⟩

/-- **The forgetful 1-morphism `ℋ_d(S/S) ⟶ ℋ_d` is an equivalence.** -/
theorem forgetRelativeToFiniteCover_base_isEquivalence :
    (forgetRelativeToFiniteCover (B := B) (S := S) (hS := hS) (d := d)
      (𝒳 := baseStack B S hS) (𝒴 := baseStack B S hS)
      (F := 𝟙 (baseCategory B S hS))).toFunctor.IsEquivalence where
  faithful := forgetRelativeToFiniteCover_base_faithful d
  full := forgetRelativeToFiniteCover_base_full d
  essSurj := forgetRelativeToFiniteCover_base_essSurj d

/-! ### Representability of the forgetful 1-morphism to the category of covers -/

/-- **The forgetful 1-morphism `ℋ_d(𝒳) ⟶ ℋ_d` is representable by algebraic spaces** as soon as
the structure 1-morphism of `𝒳` is. -/
theorem isRepresentableByAlgebraicSpaces_forgetAbsoluteStructure
    (h𝒳 : IsRepresentableByAlgebraicSpaces B S hS (toBaseStack 𝒳)) :
    IsRepresentableByAlgebraicSpaces B S hS
      (forgetAbsoluteStructure (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳)) := by
  have := forgetRelativeStructure_base_isEquivalence 𝒳 d
  have := forgetRelativeToFiniteCover_base_isEquivalence (B := B) (S := S) (hS := hS) d
  have hrel := isRepresentableByAlgebraicSpaces_mapRelative_of_representable
    (B := B) (S := S) (hS := hS) (d := d) (𝒳 := baseStack B S hS) (𝒴 := baseStack B S hS)
    (F := 𝟙 (baseCategory B S hS)) (𝒳' := 𝒳) (F' := toBaseStack 𝒳) (G := toBaseStack 𝒳)
    (Iso.refl _) h𝒳
  refine (isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS
    (𝒳' := CatFiberedInGroupoids.mk
      (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := baseStack B S hS)
        (F := toBaseStack 𝒳) (d := d))
      isFiberedInGroupoids_finiteHilbertProjection)
    (𝒳 := CatFiberedInGroupoids.mk
      (absoluteHilbertCategory (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳))
      isFiberedInGroupoids_absoluteHilbertProjection)
    (𝒴' := CatFiberedInGroupoids.mk
      (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := baseStack B S hS)
        (𝒴 := baseStack B S hS) (F := 𝟙 (baseCategory B S hS)) (d := d))
      isFiberedInGroupoids_finiteHilbertProjection)
    (𝒴 := CatFiberedInGroupoids.mk
      (finiteCoverCategory (B := B) (S := S) (hS := hS) (d := d))
      isFiberedInGroupoids_finiteCoverProjection)
    (mapRelative B S hS d 𝒳 (baseStack B S hS) (baseStack B S hS) (baseStack B S hS)
      (toBaseStack 𝒳) (𝟙 (baseCategory B S hS)) (toBaseStack 𝒳)
      (𝟙 (baseCategory B S hS)) (Iso.refl _))
    (forgetAbsoluteStructure (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳))
    (forgetRelativeStructure (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳)
      (𝒴 := baseStack B S hS) (F := toBaseStack 𝒳))
    (forgetRelativeToFiniteCover (B := B) (S := S) (hS := hS) (d := d)
      (𝒳 := baseStack B S hS) (𝒴 := baseStack B S hS) (F := 𝟙 (baseCategory B S hS)))
    (eqToIso ((forgetRelativeToFiniteCover_eq_comp (B := B) (S := S) (hS := hS) (d := d)
        (𝒳 := 𝒳) (𝒴 := baseStack B S hS) (F := toBaseStack 𝒳)).symm.trans
      (mapRelative_comp_forgetRelativeToFiniteCover B S hS d 𝒳 (baseStack B S hS)
        (baseStack B S hS) (baseStack B S hS) (toBaseStack 𝒳) (𝟙 (baseCategory B S hS))
        (toBaseStack 𝒳) (𝟙 (baseCategory B S hS)) (Iso.refl _)).symm))).2 hrel

/-- **The structure 1-morphism of a stack in groupoids representable by an algebraic space is
representable by algebraic spaces.** -/
theorem isRepresentableByAlgebraicSpaces_toBaseStack
    (h𝒳 : IsRepresentableByAlgebraicSpace B S hS
      (CatFiberedInGroupoids.mk 𝒳.toBasedCategory
        𝒳.isStackInGroupoids.isFiberedInGroupoids)) :
    IsRepresentableByAlgebraicSpaces B S hS (toBaseStack 𝒳) :=
  isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS
    (𝒴 := CatFiberedInGroupoids.mk (baseCategory B S hS) Functor.isFiberedInGroupoids_id)
    (isAlgebraicStack_terminal.{u, u} B S hS) h𝒳
    (Bicategory.InducedBicategory.mkHom (toBaseStack 𝒳))

/-- **The forgetful 1-morphism `ℋ_d(𝒳) ⟶ ℋ_d` is representable by algebraic spaces** when `𝒳` is
representable by an algebraic space over `S`. -/
theorem isRepresentableByAlgebraicSpaces_forgetAbsoluteStructure_of_space
    (h𝒳 : IsRepresentableByAlgebraicSpace B S hS
      (CatFiberedInGroupoids.mk 𝒳.toBasedCategory
        𝒳.isStackInGroupoids.isFiberedInGroupoids)) :
    IsRepresentableByAlgebraicSpaces B S hS
      (forgetAbsoluteStructure (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳)) :=
  isRepresentableByAlgebraicSpaces_forgetAbsoluteStructure 𝒳 d
    (isRepresentableByAlgebraicSpaces_toBaseStack 𝒳 h𝒳)

/-! ### The 1-morphism as a 1-morphism of categories fibred in groupoids -/

/-- The absolute finite Hilbert category `ℋ_d(𝒳)` as an object of the 2-category of categories
fibred in groupoids over the big fppf site of `S`. -/
abbrev absoluteHilbertFibered : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.mk
    (absoluteHilbertCategory (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳))
    isFiberedInGroupoids_absoluteHilbertProjection

variable (B S hS) in
/-- The category `ℋ_d` of degree-`d` finite locally free covers as an object of the 2-category of
categories fibred in groupoids over the big fppf site of `S`. -/
abbrev finiteCoverFibered : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.mk (finiteCoverCategory (B := B) (S := S) (hS := hS) (d := d))
    isFiberedInGroupoids_finiteCoverProjection

/-- The forgetful 1-morphism `ℋ_d(𝒳) ⟶ ℋ_d` of Stacks 05WD, read as a 1-morphism of categories
fibred in groupoids. Its underlying 1-morphism over the site is
`AlgebraicGeometry.Stack.forgetAbsoluteStructure`. -/
abbrev forgetAbsoluteStructureFibered :
    absoluteHilbertFibered 𝒳 d ⟶ finiteCoverFibered B S hS d :=
  Bicategory.InducedBicategory.mkHom
    (forgetAbsoluteStructure (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳))

end AlgebraicGeometry.Stack

end
