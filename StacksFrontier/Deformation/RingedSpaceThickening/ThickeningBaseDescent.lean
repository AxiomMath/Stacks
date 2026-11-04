module

public import StacksFrontier.CategoryTheory.Sites.RingSheafDescent
public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionPresentation
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentTriangleObstruction
public import StacksFrontier.Topology.Sheaves.RingedSpace.ThickeningTrivialization

/-!
# Descending an algebra structure along a thickening of the base

Let `t : (S, 𝒪_S) ⟶ (S', 𝒪_{S'})` be a thickening of ringed spaces and `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)`
a morphism. A sheaf of rings `ℛ` on `X` which is an `(f ≫ t)⁻¹𝒪_{S'}`-algebra is an
`f⁻¹𝒪_S`-algebra as soon as the ideal `𝒥 = Ker(t^♯)` of the thickening acts on it by zero: this
is what makes the difference of two solutions of the deformation problem of **Stacks 08U7** an
extension of `f⁻¹𝒪_S`-algebras, which is the first step of the proof of **Stacks 08UC**.

The descent is read through the adjunctions `g⁻¹ ⊣ g_*`. An algebra structure
`β : (f ≫ t)⁻¹𝒪_{S'} ⟶ ℛ` is the same thing as its adjoint `𝒪_{S'} ⟶ (f ≫ t)_* ℛ = t_* f_* ℛ`.
If this adjoint kills every section of `𝒪_{S'}` killed by `t^♯`, it descends along the locally
surjective `t^♯ : 𝒪_{S'} ⟶ t_* 𝒪_S`, and since `t` is a homeomorphism on underlying spaces the
descended map `t_* 𝒪_S ⟶ t_* f_* ℛ` is the direct image of a unique `𝒪_S ⟶ f_* ℛ`, whose
adjoint is the descended algebra structure `f⁻¹𝒪_S ⟶ ℛ`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.thickeningSharp`: `t^♯ : 𝒪_{S'} ⟶ t_* 𝒪_S`, as a
  morphism of sheaves of rings.
* `AlgebraicGeometry.RingedSpaceThickening.descendAlongThickening`: the descent of a morphism
  `𝒪_{S'} ⟶ t_* 𝒯` killing `Ker(t^♯)` to a morphism `𝒪_S ⟶ 𝒯`.
* `AlgebraicGeometry.RingedSpaceThickening.adjointBaseHom` and
  `AlgebraicGeometry.RingedSpaceThickening.descendBase`: the adjoint `𝒪_{S'} ⟶ (f ≫ t)_* ℛ` of an
  algebra structure, and the descended `f⁻¹𝒪_S`-algebra structure.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.thickeningSharp_comp_descendAlongThickening` and
  `AlgebraicGeometry.RingedSpaceThickening.eq_descendAlongThickening`: the descent exists and is
  unique.
* `AlgebraicGeometry.RingedSpaceThickening.descendBase_comp`: the descended algebra structure is
  natural in `ℛ`.
* `AlgebraicGeometry.RingedSpaceThickening.descendBase_comp_eq_structureRingMap`: a morphism to
  `𝒪_X` under `(f ≫ t)⁻¹𝒪_{S'}` is a morphism under `f⁻¹𝒪_S` for the descended structure.

## References

* [Stacks Project, Tag 08UC](https://stacks.math.columbia.edu/tag/08UC)
* [Stacks Project, Tag 08U7](https://stacks.math.columbia.edu/tag/08U7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

variable {S S' : RingedSpace.{u, u}} (t : S ⟶ S') (ht : IsThickening t)

/-! ### The comorphism of a thickening, and the full faithfulness of its direct image -/

/-- The comorphism `t^♯ : 𝒪_{S'} ⟶ t_* 𝒪_S` of a morphism of ringed spaces, as a morphism of
sheaves of commutative rings. -/
def thickeningSharp :
    S'.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} t.hom.base).obj S.sheaf :=
  ⟨t.hom.c⟩

include ht in
/-- The comorphism of a thickening is locally surjective. -/
theorem isLocallySurjective_thickeningSharp :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology S'.carrier)
      (thickeningSharp t).hom :=
  isLocallySurjective_comorphism_of_isThickening t ht

variable {t}

/-- The direct image along a thickening is full: a morphism between direct images is the direct
image of a morphism, because the underlying map of a thickening is a homeomorphism. -/
def unpushforward {T T' : Sheaf (Opens.grothendieckTopology S.carrier) CommRingCat.{u}}
    (δ : (TopCat.Sheaf.pushforward CommRingCat.{u} t.hom.base).obj T ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} t.hom.base).obj T') : T ⟶ T' :=
  haveI : IsIso t.hom.base := ht.1
  ⟨(TopCat.Presheaf.presheafEquivOfIso CommRingCat.{u}
    (asIso t.hom.base)).fullyFaithfulFunctor.preimage δ.hom⟩

/-- The direct image of `unpushforward ht δ` is `δ`. -/
theorem pushforward_map_unpushforward
    {T T' : Sheaf (Opens.grothendieckTopology S.carrier) CommRingCat.{u}}
    (δ : (TopCat.Sheaf.pushforward CommRingCat.{u} t.hom.base).obj T ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} t.hom.base).obj T') :
    (TopCat.Sheaf.pushforward CommRingCat.{u} t.hom.base).map (unpushforward ht δ) = δ := by
  have : IsIso t.hom.base := ht.1
  exact Sheaf.hom_ext ((TopCat.Presheaf.presheafEquivOfIso CommRingCat.{u}
    (asIso t.hom.base)).fullyFaithfulFunctor.map_preimage δ.hom)

include ht in
/-- The direct image along a thickening is faithful. -/
theorem pushforward_map_injective
    {T T' : Sheaf (Opens.grothendieckTopology S.carrier) CommRingCat.{u}} {γ₁ γ₂ : T ⟶ T'}
    (h : (TopCat.Sheaf.pushforward CommRingCat.{u} t.hom.base).map γ₁ =
      (TopCat.Sheaf.pushforward CommRingCat.{u} t.hom.base).map γ₂) : γ₁ = γ₂ := by
  have : IsIso t.hom.base := ht.1
  exact Sheaf.hom_ext ((TopCat.Presheaf.presheafEquivOfIso CommRingCat.{u}
    (asIso t.hom.base)).fullyFaithfulFunctor.map_injective
      (congrArg (fun k => k.hom) h))

/-! ### The descent along a thickening -/

section Descend

variable (T : Sheaf (Opens.grothendieckTopology S.carrier) CommRingCat.{u})
  (ψ : S'.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} t.hom.base).obj T)
  (hψ : ∀ (V : (Opens S'.carrier)ᵒᵖ) (s : S'.presheaf.obj V),
    (t.hom.c.app V).hom s = 0 → (ψ.hom.app V).hom s = 0)

/-- **The descent along a thickening.** A morphism `ψ : 𝒪_{S'} ⟶ t_* 𝒯` of sheaves of rings
killing every section killed by `t^♯` is `t^♯` followed by the direct image of a unique
morphism `𝒪_S ⟶ 𝒯`. -/
def descendAlongThickening : S.sheaf ⟶ T :=
  haveI := isLocallySurjective_thickeningSharp t ht
  unpushforward ht (Stacks.Sites.RingDescent.desc (thickeningSharp t) ψ hψ)

/-- `t^♯` followed by the direct image of the descent of `ψ` is `ψ`. -/
theorem thickeningSharp_comp_descendAlongThickening :
    thickeningSharp t ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} t.hom.base).map
      (descendAlongThickening ht T ψ hψ) = ψ := by
  have := isLocallySurjective_thickeningSharp t ht
  exact (congrArg (fun k => thickeningSharp t ≫ k) (pushforward_map_unpushforward ht
    (Stacks.Sites.RingDescent.desc (thickeningSharp t) ψ hψ))).trans
    (Stacks.Sites.RingDescent.comp_desc _ _ _)

/-- A morphism `γ : 𝒪_S ⟶ 𝒯` such that `t^♯` followed by the direct image of `γ` is `ψ` is the
descent of `ψ`. -/
theorem eq_descendAlongThickening (γ : S.sheaf ⟶ T)
    (h : thickeningSharp t ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} t.hom.base).map γ = ψ) :
    γ = descendAlongThickening ht T ψ hψ := by
  have := isLocallySurjective_thickeningSharp t ht
  refine pushforward_map_injective ht ?_
  exact Stacks.Sites.RingDescent.hom_ext_of_isLocallySurjective (thickeningSharp t)
    (h.trans (thickeningSharp_comp_descendAlongThickening ht T ψ hψ).symm)

end Descend

/-! ### Descending an algebra structure -/

section Base

variable {X : RingedSpace.{u, u}} (f : X ⟶ S)

/-- The adjoint `𝒪_{S'} ⟶ (f ≫ t)_* ℛ` of an `(f ≫ t)⁻¹𝒪_{S'}`-algebra structure on a sheaf of
rings `ℛ` on `X`. -/
abbrev adjointBaseHom (R : Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u})
    (β : inverseImageBaseRing (f ≫ t) ⟶ R) :
    S'.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} (f ≫ t).hom.base).obj R :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (f ≫ t).hom.base).homEquiv _ _ β

variable (R : Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u})
  (β : inverseImageBaseRing (f ≫ t) ⟶ R)
  (hβ : ∀ (V : (Opens S'.carrier)ᵒᵖ) (s : S'.presheaf.obj V),
    (t.hom.c.app V).hom s = 0 → ((adjointBaseHom f R β).hom.app V).hom s = 0)

/-- **The descended algebra structure.** An `(f ≫ t)⁻¹𝒪_{S'}`-algebra structure on `ℛ` whose
adjoint kills `Ker(t^♯)` descends to an `f⁻¹𝒪_S`-algebra structure. -/
def descendBase : inverseImageBaseRing f ⟶ R :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).homEquiv _ _).symm
    (descendAlongThickening ht ((TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj R)
      (adjointBaseHom f R β) hβ)

/-- **The descended algebra structure is natural.** -/
theorem descendBase_comp {R' : Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}}
    (γ : R ⟶ R') (β' : inverseImageBaseRing (f ≫ t) ⟶ R')
    (hβ' : ∀ (V : (Opens S'.carrier)ᵒᵖ) (s : S'.presheaf.obj V),
      (t.hom.c.app V).hom s = 0 → ((adjointBaseHom f R' β').hom.app V).hom s = 0)
    (h : β ≫ γ = β') :
    descendBase ht f R β hβ ≫ γ = descendBase ht f R' β' hβ' := by
  have hadj : adjointBaseHom f R' β' = adjointBaseHom f R β ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} (f ≫ t).hom.base).map γ := by
    rw [← h]
    exact Adjunction.homEquiv_naturality_right _ _ _
  have hdesc : descendAlongThickening ht ((TopCat.Sheaf.pushforward CommRingCat.{u}
        f.hom.base).obj R) (adjointBaseHom f R β) hβ ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map γ =
      descendAlongThickening ht ((TopCat.Sheaf.pushforward CommRingCat.{u}
        f.hom.base).obj R') (adjointBaseHom f R' β') hβ' := by
    refine eq_descendAlongThickening ht _ _ hβ' _ ?_
    exact (congrArg (fun k => thickeningSharp t ≫ k) (Functor.map_comp _ _ _)).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (fun k => k ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} (f ≫ t).hom.base).map γ)
        (thickeningSharp_comp_descendAlongThickening ht _ _ hβ)).trans hadj.symm))
  exact (Adjunction.homEquiv_naturality_right_symm _ _ _).symm.trans
    (congrArg (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
      f.hom.base).homEquiv _ _).symm) hdesc)

/-- The adjoint of the structure map of `f ≫ t` is the comorphism of `f ≫ t`. -/
private theorem adjointBaseHom_structureRingMap :
    adjointBaseHom f X.sheaf (structureRingMap (f ≫ t)) =
      (⟨(f ≫ t).hom.c⟩ : S'.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat.{u} (f ≫ t).hom.base).obj X.sheaf) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (f ≫ t).hom.base).homEquiv
    _ _).apply_symm_apply _

/-- The structure map of `f ≫ t` descends to the structure map of `f`. -/
theorem descendBase_structureRingMap
    (hβ : ∀ (V : (Opens S'.carrier)ᵒᵖ) (s : S'.presheaf.obj V),
      (t.hom.c.app V).hom s = 0 →
        ((adjointBaseHom f X.sheaf (structureRingMap (f ≫ t))).hom.app V).hom s = 0) :
    descendBase ht f X.sheaf (structureRingMap (f ≫ t)) hβ = structureRingMap f := by
  have hadj := adjointBaseHom_structureRingMap f (t := t)
  have hdesc : (⟨f.hom.c⟩ : S.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u}
      f.hom.base).obj X.sheaf) =
      descendAlongThickening ht ((TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj X.sheaf)
        (adjointBaseHom f X.sheaf (structureRingMap (f ≫ t))) hβ :=
    eq_descendAlongThickening ht _ _ hβ _ hadj.symm
  exact (congrArg (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    f.hom.base).homEquiv _ _).symm) hdesc).symm

/-- The adjoint of the structure map of `f ≫ t` kills `Ker(t^♯)`: it is the comorphism of
`f ≫ t`, which factors through `t^♯`. -/
theorem adjointBaseHom_structureRingMap_eq_zero (V : (Opens S'.carrier)ᵒᵖ)
    (s : S'.presheaf.obj V) (hs : (t.hom.c.app V).hom s = 0) :
    ((adjointBaseHom f X.sheaf (structureRingMap (f ≫ t))).hom.app V).hom s = 0 := by
  have hadj := adjointBaseHom_structureRingMap f (t := t)
  refine (congrArg (fun k : S'.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u}
    (f ≫ t).hom.base).obj X.sheaf => (k.hom.app V).hom s) hadj).trans ?_
  exact (congrArg (f.hom.c.app (op ((Opens.map t.hom.base).obj V.unop))).hom hs).trans
    (map_zero _)

/-- **A morphism to `𝒪_X` under `(f ≫ t)⁻¹𝒪_{S'}` is a morphism under `f⁻¹𝒪_S` for the
descended structure.** -/
theorem descendBase_comp_eq_structureRingMap (ρ : R ⟶ X.sheaf)
    (h : β ≫ ρ = structureRingMap (f ≫ t)) :
    descendBase ht f R β hβ ≫ ρ = structureRingMap f :=
  (descendBase_comp ht f R β hβ ρ (structureRingMap (f ≫ t))
    (adjointBaseHom_structureRingMap_eq_zero f) h).trans
    (descendBase_structureRingMap ht f _)

end Base

/-! ### Restricting an algebra structure along the thickening of the base -/

section Restrict

variable (t) {X : RingedSpace.{u, u}} (f : X ⟶ S)

/-- The adjoint `𝒪_S ⟶ f_* ℛ` of an `f⁻¹𝒪_S`-algebra structure on a sheaf of rings `ℛ` on `X`. -/
abbrev adjointHom (R : Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u})
    (β : inverseImageBaseRing f ⟶ R) :
    S.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj R :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).homEquiv _ _ β

/-- **The adjoint of a restricted algebra structure** `(f ≫ t)⁻¹𝒪_{S'} ⟶ f⁻¹𝒪_S ⟶ ℛ` is `t^♯`
followed by the direct image of the adjoint of `f⁻¹𝒪_S ⟶ ℛ`. -/
theorem adjointBaseHom_baseInverseImageRingMap_comp
    (R : Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u})
    (β : inverseImageBaseRing f ⟶ R) :
    adjointBaseHom f R (baseInverseImageRingMap f t ≫ β) =
      thickeningSharp t ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} t.hom.base).map
        (adjointHom f R β) := by
  have h₁ : adjointBaseHom f R (baseInverseImageRingMap f t ≫ β) =
      adjointBaseHom f (inverseImageBaseRing f) (baseInverseImageRingMap f t) ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} (f ≫ t).hom.base).map β :=
    Adjunction.homEquiv_naturality_right _ _ _
  have h₂ : adjointBaseHom f (inverseImageBaseRing f) (baseInverseImageRingMap f t) =
      thickeningSharp t ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} t.hom.base).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app
          S.sheaf) :=
    Equiv.apply_symm_apply _ _
  have h₃ : adjointHom f R β =
      (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app S.sheaf ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map β :=
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).homEquiv_unit
      S.sheaf R β
  refine h₁.trans ((congrArg (· ≫ (TopCat.Sheaf.pushforward CommRingCat.{u}
    (f ≫ t).hom.base).map β) h₂).trans ?_)
  refine (Category.assoc _ _ _).trans (congrArg (thickeningSharp t ≫ ·) ?_)
  refine Eq.trans ?_ (congrArg (TopCat.Sheaf.pushforward CommRingCat.{u} t.hom.base).map h₃).symm
  exact ((TopCat.Sheaf.pushforward CommRingCat.{u} t.hom.base).map_comp
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app S.sheaf)
    ((TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map β)).symm

/-- **A restricted algebra structure kills `Ker(t^♯)`.** -/
theorem adjointBaseHom_baseInverseImageRingMap_comp_eq_zero
    (R : Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u})
    (β : inverseImageBaseRing f ⟶ R)
    (V : (Opens S'.carrier)ᵒᵖ) (s : S'.presheaf.obj V) (hs : (t.hom.c.app V).hom s = 0) :
    ((adjointBaseHom f R (baseInverseImageRingMap f t ≫ β)).hom.app V).hom s = 0 := by
  refine (congrArg (fun k : S'.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u}
    (f ≫ t).hom.base).obj R => (k.hom.app V).hom s)
    (adjointBaseHom_baseInverseImageRingMap_comp t f R β)).trans ?_
  show (((TopCat.Sheaf.pushforward CommRingCat.{u} t.hom.base).map
      (adjointHom f R β)).hom.app V).hom ((t.hom.c.app V).hom s) = 0
  exact (congrArg _ hs).trans (map_zero _)

include ht in
/-- **Restriction of the algebra structure is injective.** -/
theorem baseInverseImageRingMap_comp_injective
    {R : Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}}
    {β₁ β₂ : inverseImageBaseRing f ⟶ R}
    (h : baseInverseImageRingMap f t ≫ β₁ = baseInverseImageRingMap f t ≫ β₂) : β₁ = β₂ := by
  have := isLocallySurjective_thickeningSharp t ht
  have h' : thickeningSharp t ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} t.hom.base).map
        (adjointHom f R β₁) =
      thickeningSharp t ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} t.hom.base).map
        (adjointHom f R β₂) :=
    (adjointBaseHom_baseInverseImageRingMap_comp t f R β₁).symm.trans
      ((congrArg (adjointBaseHom f R) h).trans
        (adjointBaseHom_baseInverseImageRingMap_comp t f R β₂))
  exact ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).homEquiv
    _ _).injective (pushforward_map_injective ht
      (Stacks.Sites.RingDescent.hom_ext_of_isLocallySurjective (thickeningSharp t) h'))

/-- **Descending a restricted algebra structure gives it back.** -/
theorem descendBase_baseInverseImageRingMap_comp
    (R : Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u})
    (β : inverseImageBaseRing f ⟶ R) :
    descendBase ht f R (baseInverseImageRingMap f t ≫ β)
      (adjointBaseHom_baseInverseImageRingMap_comp_eq_zero t f R β) = β := by
  have h : adjointHom f R β = descendAlongThickening ht
      ((TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj R)
      (adjointBaseHom f R (baseInverseImageRingMap f t ≫ β))
      (adjointBaseHom_baseInverseImageRingMap_comp_eq_zero t f R β) :=
    eq_descendAlongThickening ht _ _ _ _ (adjointBaseHom_baseInverseImageRingMap_comp t f R β).symm
  exact (congrArg ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    f.hom.base).homEquiv _ _).symm h).symm.trans (Equiv.symm_apply_apply _ _)

/-- **Restricting a descended algebra structure gives it back.** -/
theorem baseInverseImageRingMap_comp_descendBase
    (R : Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u})
    (β : inverseImageBaseRing (f ≫ t) ⟶ R)
    (hβ : ∀ (V : (Opens S'.carrier)ᵒᵖ) (s : S'.presheaf.obj V),
      (t.hom.c.app V).hom s = 0 → ((adjointBaseHom f R β).hom.app V).hom s = 0) :
    baseInverseImageRingMap f t ≫ descendBase ht f R β hβ = β := by
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    (f ≫ t).hom.base).homEquiv _ _).injective
  refine (adjointBaseHom_baseInverseImageRingMap_comp t f R _).trans ?_
  have h : adjointHom f R (descendBase ht f R β hβ) = descendAlongThickening ht
      ((TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj R) (adjointBaseHom f R β) hβ :=
    Equiv.apply_symm_apply _ _
  refine (congrArg (fun k => thickeningSharp t ≫
    (TopCat.Sheaf.pushforward CommRingCat.{u} t.hom.base).map k) h).trans ?_
  exact thickeningSharp_comp_descendAlongThickening ht _ _ hβ

end Restrict

namespace AlgebraSquareZeroExtension

variable {X : RingedSpace.{u, u}} {f : X ⟶ S}
  {G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)}

variable (t) in
/-- **A square-zero extension of `f⁻¹𝒪_S`-algebras, read as one of `(f ≫ t)⁻¹𝒪_{S'}`-algebras**:
the same sheaf of rings, reduction and ideal, with the algebra structure restricted along
`(f ≫ t)⁻¹𝒪_{S'} ⟶ f⁻¹𝒪_S`. -/
def restrictBase (P : AlgebraSquareZeroExtension f G) : AlgebraSquareZeroExtension (f ≫ t) G where
  sheaf := P.sheaf
  base := baseInverseImageRingMap f t ≫ P.base
  reduction := P.reduction
  base_comp_reduction := (Category.assoc _ _ _).trans
    ((congrArg (baseInverseImageRingMap f t ≫ ·) P.base_comp_reduction).trans
      (baseInverseImageRingMap_comp f t))
  reduction_surjective := P.reduction_surjective
  ideal := P.ideal

/-- **A square-zero extension of `(f ≫ t)⁻¹𝒪_{S'}`-algebras whose algebra structure kills
`Ker(t^♯)`, read as one of `f⁻¹𝒪_S`-algebras.** -/
def descendBase (P : AlgebraSquareZeroExtension (f ≫ t) G)
    (hP : ∀ (V : (Opens S'.carrier)ᵒᵖ) (s : S'.presheaf.obj V),
      (t.hom.c.app V).hom s = 0 → ((adjointBaseHom f P.sheaf P.base).hom.app V).hom s = 0) :
    AlgebraSquareZeroExtension f G where
  sheaf := P.sheaf
  base := RingedSpaceThickening.descendBase ht f P.sheaf P.base hP
  reduction := P.reduction
  base_comp_reduction :=
    descendBase_comp_eq_structureRingMap ht f P.sheaf P.base hP P.reduction P.base_comp_reduction
  reduction_surjective := P.reduction_surjective
  ideal := P.ideal

end AlgebraSquareZeroExtension

end AlgebraicGeometry.RingedSpaceThickening


end
